// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory conflict inference for Alethe proof generation.
//!
//! This module maps theory solver conflicts to structured Alethe proof rules
//! (EUF congruence, transitivity, LRA Farkas, array axioms, ground/symbolic
//! string-regex facts, pure-NRA interval/univariate refutations). When a
//! structured rule can be inferred the proof is more precise than the generic
//! `trust` fallback.
//!
//! Extracted from `proof_tracker.rs` for file-size hygiene (#4534).
//! Split into submodules for code health (#5970):
//! - `euf`: EUF congruence/transitivity lemma inference
//! - `decompose`: Combined real-theory lemma decomposition
//! - `funnel`: strict-checkable classification of materialized lemmas

mod arith_farkas_classification;
mod decompose;
mod euf;
mod funnel;
#[cfg(test)]
mod funnel_tests;

use std::borrow::Cow;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    FarkasAnnotation, ProofId, Sort, Symbol, TermData, TermId, TermStore, TheoryConflict,
    TheoryLemmaKind, TheoryLit,
};

use crate::proof_tracker::ProofTracker;

use arith_farkas_classification::{linear_equality_arith_farkas_valid, opaque_arith_farkas_valid};

// Re-export pub(crate) items from submodules.
pub(crate) use decompose::{decompose_generic_combined_real_lemma, CombinedDecompositionBudget};
pub(crate) use funnel::{
    dt_funnel_registry_data, infer_theory_lemma_kind_from_clause_terms_and_farkas,
    record_funnel_classified_lemma, DatatypeRegistries,
};

/// Record a theory conflict and infer the most specific Alethe rule.
pub(crate) fn record_theory_conflict_unsat(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<ProofId> {
    record_theory_conflict_unsat_with_annotation(tracker, terms, negations, conflict).0
}

/// Record a theory conflict and return the exact direct trace annotation, when
/// the recorded derivation can be represented by [`ay_core::TheoryLemmaProof`].
///
/// This is the single authority decision used by lazy split pipelines. A
/// mixed-theory core recorded as `TheoryLemma + Weakening` deliberately returns
/// no indexed annotation: that compact annotation type cannot encode the
/// weakening premise, so the full tracker derivation remains authoritative.
pub(crate) fn record_theory_conflict_unsat_with_annotation(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> (Option<ProofId>, Option<ay_core::TheoryLemmaProof>) {
    if !tracker.is_enabled() {
        return (None, None);
    }

    let Some(clause) = build_blocking_clause_terms(negations, conflict) else {
        let raw_clause = conflict.iter().map(|lit| lit.term).collect::<Vec<_>>();
        let id = tracker.add_explicit_trust_lemma(raw_clause);
        return (id, None);
    };

    // When no single classifier recognises the whole conflict, try
    // combined-theory decomposition before falling back to Generic/trust.
    let (kind, ordered_clause) = if let Some(terms) = terms {
        match classify_whole_conflict(terms, negations, conflict, &clause) {
            Some(result) => result,
            None => {
                // #combined-theory-decompose: a conflict no classifier accepts
                // is usually MIXED — a single-theory core plus literals from
                // other theories that the combination happened to carry along.
                // The core's blocking clause IS a checkable single-theory
                // lemma, and the full blocking clause follows from it by
                // `weakening`, so emit the core with its real kind and weaken
                // up to the clause the caller expects.
                if let Some((core_kind, core_clause, full_clause)) =
                    classifiable_core_decomposition(terms, negations, conflict, &clause)
                {
                    let id = tracker.add_theory_lemma_weakened(core_clause, core_kind, full_clause);
                    return (id, None);
                }
                (TheoryLemmaKind::Generic, clause)
            }
        }
    } else {
        (TheoryLemmaKind::Generic, clause)
    };

    let farkas = matches!(
        kind,
        TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas
    )
    .then(|| FarkasAnnotation::from_ints(&vec![1i64; ordered_clause.len()]));
    let id = match (kind, farkas.as_ref()) {
        (TheoryLemmaKind::Generic, _) => tracker.add_explicit_trust_lemma(ordered_clause.clone()),
        (TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas, Some(unit_farkas)) => tracker
            .add_theory_lemma_with_farkas_and_kind(
                ordered_clause.clone(),
                unit_farkas.clone(),
                kind,
            ),
        _ => tracker.add_theory_lemma_with_kind(ordered_clause.clone(), kind),
    };
    let annotation = id.map(|_| ay_core::TheoryLemmaProof {
        clause: ordered_clause,
        kind,
        farkas,
        lia: None,
    });
    (id, annotation)
}

/// Classify a clause as one of the strict-checkable array kinds
/// (`ArraySelectStore { index_eq }`, `ArrayStorePermutation`, `ArrayRowChain`)
/// when it matches an exact schema, else `None`. Recognition is delegated to
/// the checker's own matcher (`ay_proof::recognize_array_theory_lemma`) so the
/// classifier and validator cannot drift. Extensionality is intentionally
/// excluded (not yet strict-validatable, #8073), so it stays `Generic` rather
/// than be mislabelled a kind strict mode would reject.
fn infer_array_lemma(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    ay_proof::recognize_array_theory_lemma(terms, clause).map(|kind| (kind, clause.to_vec()))
}

/// Classify a clause as the strict-checkable ground string/regex kind
/// `StringGroundEval` when the checker's own independent evaluator proves one
/// of its literals TRUE, else `None`. Delegating to
/// `ay_proof::recognize_string_ground_eval` keeps the classifier and the strict
/// validator from drifting.
fn infer_string_ground_eval_lemma(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    ay_proof::recognize_string_ground_eval(terms, clause)
        .then(|| (TheoryLemmaKind::StringGroundEval, clause.to_vec()))
}

/// Classify a clause as the strict-checkable SYMBOLIC regex kind
/// `RegexIntersectEmpty` when the checker's own independent derivative-product
/// emptiness decision proves that some `str.in_re` literal group over a common
/// subject denies an EMPTY intersection, else `None`. Delegating to
/// `ay_proof::recognize_regex_intersect_empty` keeps the classifier and the
/// strict validator from drifting.
fn infer_regex_intersect_empty_lemma(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    ay_proof::recognize_regex_intersect_empty(terms, clause)
        .then(|| (TheoryLemmaKind::RegexIntersectEmpty, clause.to_vec()))
}

/// Classify a clause as the strict-checkable exact-IEEE-754 kind
/// `FpGroundEval` when the checker's own correctly-rounded kernel proves the
/// clause valid — after substituting the ground bindings the clause itself
/// carries, and over every assignment of whatever variables remain. Delegating
/// to `ay_proof::recognize_fp_ground_eval` keeps the classifier and the strict
/// validator from drifting.
fn infer_fp_ground_eval_lemma(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    fp_ground_eval_applies(terms, clause).then(|| (TheoryLemmaKind::FpGroundEval, clause.to_vec()))
}

/// Whether the exact IEEE-754 evaluator should CLAIM this clause.
///
/// `FpClassification` keeps priority on the sign/class/comparison identities it
/// already validates. Those two kinds overlap — an `(= (fp.abs (fp.abs x))
/// (fp.abs x))` identity over a narrow format is decidable by both — and the
/// older kind is the one downstream artifacts key on (the Lean firewall emitter
/// matches `K::FpClassification`, so silently re-labelling those clauses would
/// drop a proof artifact without any test asserting the verdict changed).
/// `FpGroundEval` therefore covers exactly what `FpClassification` REFUSES: the
/// arithmetic and conversion fragment it has no evaluator for.
///
/// The cheap-first order matters: the exact evaluator's own hygiene gate
/// rejects a non-FP clause immediately, so the classification recognizer only
/// runs on the handful of clauses that already passed.
fn fp_ground_eval_applies(terms: &TermStore, clause: &[TermId]) -> bool {
    ay_proof::recognize_fp_ground_eval(terms, clause)
        && !ay_proof::recognize_fp_classification(terms, clause)
}

/// Record an already-materialized theory LEMMA clause through the central
/// classifier funnel (#trust->0 C1.iii).
///
/// `clause_lits` are the lemma's CLAUSE literals (`value == true` means the
/// literal is `term` itself; `false` means its negation), i.e. the polarity
/// convention of `TheoryLemma::clause` / `term_to_literal` — the OPPOSITE of
/// the conflict convention `build_blocking_clause_terms` consumes.
///
/// Polarity is resolved through the negation cache BEFORE classification: a
/// clause with any unresolvable negation keeps the legacy raw-term fallback
/// literal and is recorded as bare `Generic` WITHOUT running the funnel.
/// Classifying a wrong-polarity clause could stamp a typed kind on a
/// malformed artifact, turning today's deferred-trust discharge into a hard
/// strict failure (the review-required polarity fix); the unclassified
/// residual is the same negation-cache miss class as
/// `build_blocking_clause_terms` (Wave-3, never loosened here).
pub(crate) fn record_materialized_lemma_clause(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    clause_lits: &[TheoryLit],
) -> Option<ProofId> {
    if !tracker.is_enabled() {
        return None;
    }
    let mut clause = Vec::with_capacity(clause_lits.len());
    let mut polarity_complete = true;
    for lit in clause_lits {
        if lit.value {
            clause.push(lit.term);
        } else if let Some(&neg) = negations.get(&lit.term) {
            clause.push(neg);
        } else {
            // Legacy fallback literal (wrong polarity): recorded for parity
            // with the historical sites, but NEVER classified.
            polarity_complete = false;
            clause.push(lit.term);
        }
    }
    let funnel_terms = if polarity_complete { terms } else { None };
    let Some(terms) = funnel_terms else {
        return tracker.add_explicit_trust_lemma(clause);
    };
    // DT registries are executor-context state the C1.iii extension lanes do
    // not hold, so DT shapes stay `Generic` here (fail-closed residual, same
    // class as the negation-cache misses above). EUF recognition needs only
    // the clause and runs in full; adopt its validator-ordered clause.
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(terms, &clause, None, None);
    let clause = match ordered {
        Cow::Owned(reordered) => reordered,
        Cow::Borrowed(_) => clause,
    };
    match kind {
        TheoryLemmaKind::Generic => tracker.add_explicit_trust_lemma(clause),
        // The funnel classifies these only after the integer gate
        // (`LiaGeneric`) or a FULL semantic verification of the UNIT
        // certificate (opaque-atom `LraFarkas`); attach the same unit
        // coefficients, exactly as `record_theory_conflict_unsat` does. The
        // strict checker re-decides either way (fail-closed).
        TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas => {
            let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; clause.len()]);
            tracker.add_theory_lemma_with_farkas_and_kind(clause, unit_farkas, kind)
        }
        _ => tracker.add_theory_lemma_with_kind(clause, kind),
    }
}

/// Record a theory conflict with Farkas coefficients (arithmetic theories).
pub(crate) fn record_theory_conflict_unsat_with_farkas(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &TheoryConflict,
) -> Option<ProofId> {
    record_theory_conflict_unsat_with_farkas_and_annotation(tracker, terms, negations, conflict).0
}

/// Farkas-bearing counterpart of
/// [`record_theory_conflict_unsat_with_annotation`]. The returned annotation
/// is constructed from the exact kind, clause, and evidence recorded in the
/// tracker; a Generic fallback deliberately carries no rejected certificate.
pub(crate) fn record_theory_conflict_unsat_with_farkas_and_annotation(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &TheoryConflict,
) -> (Option<ProofId>, Option<ay_core::TheoryLemmaProof>) {
    if !tracker.is_enabled() {
        return (None, None);
    }

    let Some(farkas) = conflict.farkas.clone() else {
        // #trust->0 C1.i: no Farkas certificate on the conflict — delegate to
        // `record_theory_conflict_unsat` so the WHOLE-conflict classifier
        // (EUF/arith/array/string/FP + combined-theory core decomposition)
        // runs instead of recording a bare `Generic`/trust lemma.
        //
        // Fail-closed nuance preserved: this site historically recorded
        // NOTHING (`?` early return) when the negation cache cannot express
        // the blocking clause, while the delegate's fallback records the
        // UNNEGATED literal terms — a wrong-polarity clause no validator can
        // accept (the mod.rs `build_blocking_clause_terms` miss class,
        // Wave-3). Keep the stricter no-record behavior on that residual by
        // probing the builder first.
        if build_blocking_clause_terms(negations, &conflict.literals).is_none() {
            return (None, None);
        }
        return record_theory_conflict_unsat_with_annotation(
            tracker,
            terms,
            negations,
            &conflict.literals,
        );
    };

    let Some(clause) = build_blocking_clause_terms(negations, &conflict.literals) else {
        return (None, None);
    };

    let kind = match terms {
        Some(terms) => classify_arith_conflict_kind(terms, &conflict.literals, Some(&farkas)),
        // No TermStore -- cannot classify Farkas conflict.
        None => TheoryLemmaKind::Generic,
    };

    let (id, recorded_farkas) = match kind {
        TheoryLemmaKind::Generic => (tracker.add_explicit_trust_lemma(clause.clone()), None),
        TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas => (
            tracker.add_theory_lemma_with_farkas_and_kind(clause.clone(), farkas.clone(), kind),
            Some(farkas),
        ),
        _ => (
            tracker.add_theory_lemma_with_kind(clause.clone(), kind),
            None,
        ),
    };
    let annotation = id.map(|_| ay_core::TheoryLemmaProof {
        clause,
        kind,
        farkas: recorded_farkas,
        lia: None,
    });
    (id, annotation)
}

pub(crate) fn build_blocking_clause_terms(
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<Vec<TermId>> {
    let mut out = Vec::with_capacity(conflict.len());
    for &lit in conflict {
        if lit.value {
            out.push(*negations.get(&lit.term)?);
        } else {
            out.push(lit.term);
        }
    }
    Some(out)
}

fn blocking_clause_to_conflict_lits(terms: &TermStore, clause: &[TermId]) -> Vec<TheoryLit> {
    clause
        .iter()
        .map(|&lit| match terms.get(lit) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(lit, false),
        })
        .collect()
}

fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Infer an arithmetic proof kind when all conflict literals are comparisons.
///
/// The certificate boundary is semantic, not sort-based: any conflict whose
/// coefficients pass the shared Farkas verifier exports as `LraFarkas`, even if
/// the atoms mention `Int` terms. Integer arithmetic only falls back to
/// `LiaGeneric` when the coefficients are not Farkas-valid. Returns `None` if
/// any literal is non-arithmetic (#6365).
fn infer_arith_farkas(
    terms: &TermStore,
    conflict: &[TheoryLit],
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    if conflict.is_empty() {
        return None;
    }
    if !conflict_all_arith_literals(terms, conflict) {
        // Opaque-atom rescue (class 4): comparisons (and asserted-true
        // equalities) over uninterpreted Int/Real atoms with a fully
        // verified unit certificate export as `la_generic` instead of trust.
        let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; clause.len()]);
        if opaque_arith_farkas_valid(terms, conflict, &unit_farkas) {
            return Some((TheoryLemmaKind::LraFarkas, clause.to_vec()));
        }
        return None;
    }
    let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; clause.len()]);
    let kind = classify_arith_conflict_kind(terms, conflict, Some(&unit_farkas));
    Some((kind, clause.to_vec()))
}

fn classify_arith_conflict_kind(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: Option<&FarkasAnnotation>,
) -> TheoryLemmaKind {
    if let Some(farkas) = farkas {
        // A positional vector with the right length and sign is not yet proof
        // authority: SAT/theory reordering or a producer defect can attach valid-
        // looking coefficients to the wrong inequalities. `la_generic` is an
        // externally checked proof rule, so classify it only after the exact
        // LINEAR verifier accepts the certificate against this conflict. The
        // linear variant deliberately excludes congruence reasoning unavailable
        // to Alethe checkers.
        //
        // First accept the pure-inequality subset. Equality rows need signed
        // orientation and therefore pass through the narrower exact gate below.
        if conflict_all_arith_literals(terms, conflict)
            && ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                terms, conflict, farkas,
            )
            .is_ok()
        {
            return TheoryLemmaKind::LraFarkas;
        }
        if linear_equality_arith_farkas_valid(terms, conflict, farkas) {
            return TheoryLemmaKind::LraFarkas;
        }
    }

    if arith_conflict_is_integer(terms, conflict) {
        return TheoryLemmaKind::LiaGeneric;
    }

    // Opaque-atom rescue (class 4): the conflict would otherwise fall back to
    // `Generic`/trust. If the provided certificate passes the LINEAR semantic
    // Farkas verifier with uninterpreted Int/Real atoms treated as opaque
    // variables, it is a genuine `la_generic` step. Fail-closed.
    if let Some(farkas) = farkas {
        if opaque_arith_farkas_valid(terms, conflict, farkas) {
            return TheoryLemmaKind::LraFarkas;
        }
    }

    // Arith conflict that is neither LRA Farkas-valid nor integer. Could be a
    // real-valued conflict with bad Farkas annotation shape, or a mixed-theory
    // conflict. Needs LRA fallback.
    TheoryLemmaKind::Generic
}

fn strip_not(terms: &TermStore, term: TermId) -> TermId {
    match terms.get(term) {
        TermData::Not(inner) => *inner,
        _ => term,
    }
}

fn is_pure_lia_term(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(_)) => true,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" | "-" | "*" | "div" | "mod" | "abs" => {
                args.iter().all(|&arg| is_pure_lia_term(terms, arg))
            }
            _ => false,
        },
        _ => false,
    }
}

fn arith_conflict_is_integer(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    !conflict.is_empty()
        && conflict.iter().all(|lit| {
            let atom = strip_not(terms, lit.term);
            match terms.get(atom) {
                TermData::App(Symbol::Named(name), args)
                    if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=")
                        && args.len() == 2 =>
                {
                    matches!(terms.sort(args[0]), Sort::Int)
                        && matches!(terms.sort(args[1]), Sort::Int)
                        && is_pure_lia_term(terms, args[0])
                        && is_pure_lia_term(terms, args[1])
                }
                _ => false,
            }
        })
}

fn conflict_all_arith_literals(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    conflict
        .iter()
        .all(|lit| is_la_generic_eligible_literal(terms, strip_not(terms, lit.term)))
}

/// Check if a literal is eligible for the Alethe `la_generic` rule.
///
/// This pure-inequality gate accepts strict/non-strict comparisons whose
/// arguments are linear arithmetic. Asserted equalities use the separately
/// signed and verified equality gate; asserted disequalities remain excluded.
/// Mixed-theory terms such as `(>= (f x) 0)` use the opaque-atom gate.
fn is_la_generic_eligible_literal(terms: &TermStore, atom: TermId) -> bool {
    match terms.get(atom) {
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "<=" | "<" | ">=" | ">") && args.len() == 2 =>
        {
            // Both arguments must be pure arithmetic (no UF applications).
            is_pure_la_term(terms, args[0]) && is_pure_la_term(terms, args[1])
        }
        _ => false,
    }
}

/// Check if a term is pure linear arithmetic (suitable for `la_generic`).
///
/// Returns true for: integer/rational constants, Int/Real variables,
/// and arithmetic operations (+, -, *, /, div, mod, abs, to_real, to_int)
/// applied recursively to pure LA terms.
///
/// Returns false for: uninterpreted function applications like `f(x)`,
/// select/store, or any non-arithmetic operation — and for NONLINEAR
/// products/quotients, see below.
///
/// LINEARITY IS LOAD-BEARING, NOT COSMETIC (#nra-la-generic). `la_generic` is
/// the LINEAR Farkas rule: a checker sums `Σ λᵢ·¬φᵢ` and demands the variable
/// terms CANCEL. Accepting `(* skoX (* skoX c))` here classified a NONLINEAR
/// QF_NRA conflict as `LraFarkas`, and — because the promotion in
/// `classify_arith_conflict_kind` is a shape-only check on the coefficients,
/// never a semantic one — AY emitted
///
///   (step t1 (cl (<= (* skoC -235/42) skoS)
///                (<= (* skoX (+ -201381/11500 (* skoX -1258807/23000000))) 41844/23)
///                (<= (* skoX (+ 57/500 (* skoX 361/1000000))) -12)
///                (<= skoX 0)) :rule la_generic :args (1 1 1 1))
///
/// on `QF_NRA/meti-tarski/Chua/1/IL/L/Chua-1-IL-L-chunk-0034`. carcara rejects
/// the whole document: nothing cancels, so the claimed contradiction is not
/// one. The clause is a true tautology of NONLINEAR real arithmetic (it needs
/// `skoX² ≥ 0`), but `la_generic` cannot express that, and `skoC`/`skoS` occur
/// in no other literal so no Farkas combination could ever eliminate them.
///
/// Rejecting nonlinearity here demotes such conflicts to `Generic`, which the
/// printer wires to `hole` — an honest unproved step — instead of an `invalid`
/// certificate. Per `scripts/check_proofs.sh`: "A WRONG PROOF IS WORSE THAN NO
/// PROOF." The test is purely syntactic (no `BigRational`), so linear logics
/// are bit-identical: a QF_LRA/QF_LIA term has no variable×variable product.
fn is_pure_la_term(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(_) | ay_core::Constant::Rational(_)) => true,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int | Sort::Real),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "*" => {
                // Linear only when at most ONE factor carries a variable.
                args.iter().all(|&arg| is_pure_la_term(terms, arg))
                    && args
                        .iter()
                        .filter(|&&arg| !is_ground_arith_term(terms, arg))
                        .count()
                        <= 1
            }
            "/" | "div" | "mod" => {
                // Linear only when every DIVISOR is variable-free; `(/ x y)`
                // and `(div x y)` over two variables are not linear terms.
                // The UNARY form `(/ x)` is the reciprocal `1/x` — nonlinear
                // unless `x` itself is ground — so it has no divisor to skip
                // and every argument must be ground.
                let divisors = if args.len() >= 2 {
                    &args[1..]
                } else {
                    &args[..]
                };
                args.iter().all(|&arg| is_pure_la_term(terms, arg))
                    && divisors.iter().all(|&arg| is_ground_arith_term(terms, arg))
            }
            "+" | "-" | "to_real" | "to_int" | "abs" => {
                args.iter().all(|&arg| is_pure_la_term(terms, arg))
            }
            _ => false,
        },
        _ => false,
    }
}

/// Whether an arithmetic term is GROUND (variable-free), i.e. it denotes a
/// constant. Used by [`is_pure_la_term`] to tell a linear `(* 2 x)` from a
/// nonlinear `(* x x)`; `(* (+ 1 2) x)` is still linear.
///
/// Deliberately conservative: anything not recognised as a ground arithmetic
/// operator answers `false`, so an unknown shape can only make a term look
/// LESS linear, never more.
fn is_ground_arith_term(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(_) | ay_core::Constant::Rational(_)) => true,
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" | "-" | "*" | "/" | "to_real" | "to_int" | "div" | "mod" | "abs" => {
                args.iter().all(|&arg| is_ground_arith_term(terms, arg))
            }
            _ => false,
        },
        _ => false,
    }
}

// =========================================================================
// Theory conflict clause minimization (#8424)
// =========================================================================

/// Minimum clause size for minimization to be worthwhile.
/// Clauses with 4 or fewer literals are already small; the overhead of
/// sorting/dedup or scanning Farkas coefficients is not justified.
const MIN_CLAUSE_SIZE_FOR_MINIMIZE: usize = 5;

/// Minimize an EUF conflict clause by finding the shortest equality chain.
///
/// An EUF transitivity conflict has the form:
///   {(= a b)=true, (= b c)=true, ..., (= a z)=false}
/// where the asserted equalities form a chain proving (= a z), contradicting
/// the negated conclusion. If the conflict contains more equalities than the
/// shortest BFS path requires, the extras are redundant.
///
/// Non-equality literals (e.g., predicate congruence arguments) are always
/// retained since they may be essential for the conflict.
///
/// Returns the number of literals removed. The `conflict` vector is modified
/// in place if a shorter chain is found.
pub(crate) fn minimize_euf_conflict(conflict: &mut Vec<TheoryLit>, terms: &TermStore) -> usize {
    use std::collections::VecDeque;

    if conflict.len() < MIN_CLAUSE_SIZE_FOR_MINIMIZE {
        return 0;
    }

    // Identify the single negated equality (conclusion) and asserted equalities (premises).
    let mut conclusion_idx = None;
    let mut premise_eq_indices = Vec::new();
    let mut non_eq_indices = Vec::new();

    for (i, lit) in conflict.iter().enumerate() {
        if decode_eq(terms, lit.term).is_some() {
            if lit.value {
                premise_eq_indices.push(i);
            } else {
                // Multiple negated equalities: not a simple transitivity pattern.
                if conclusion_idx.is_some() {
                    return 0;
                }
                conclusion_idx = Some(i);
            }
        } else {
            non_eq_indices.push(i);
        }
    }

    // Need exactly one conclusion and at least 2 premises for minimization to help.
    let Some(conc_idx) = conclusion_idx else {
        return 0;
    };
    if premise_eq_indices.len() < 2 {
        return 0;
    }

    let conc_lit = conflict[conc_idx];
    let Some((lhs, rhs)) = decode_eq(terms, conc_lit.term) else {
        return 0;
    };

    // Build adjacency graph from asserted equalities.
    let mut adj: HashMap<TermId, Vec<(TermId, usize)>> = HashMap::default();
    for &idx in &premise_eq_indices {
        let Some((a, b)) = decode_eq(terms, conflict[idx].term) else {
            continue;
        };
        adj.entry(a).or_default().push((b, idx));
        adj.entry(b).or_default().push((a, idx));
    }

    // BFS from lhs to rhs to find shortest path.
    let mut queue = VecDeque::new();
    let mut parent: HashMap<TermId, (TermId, usize)> = HashMap::default();
    queue.push_back(lhs);
    parent.insert(lhs, (lhs, usize::MAX));

    while let Some(curr) = queue.pop_front() {
        if curr == rhs {
            break;
        }
        if let Some(neighbors) = adj.get(&curr) {
            for &(next, eq_idx) in neighbors {
                if !parent.contains_key(&next) {
                    parent.insert(next, (curr, eq_idx));
                    queue.push_back(next);
                }
            }
        }
    }

    // If BFS didn't find a path, cannot minimize.
    if !parent.contains_key(&rhs) {
        return 0;
    }

    // Reconstruct the chain.
    let mut chain_indices = Vec::new();
    let mut curr = rhs;
    while curr != lhs {
        let Some(&(prev, eq_idx)) = parent.get(&curr) else {
            return 0;
        };
        chain_indices.push(eq_idx);
        curr = prev;
    }

    // If the chain uses all premise equalities, no reduction possible.
    if chain_indices.len() >= premise_eq_indices.len() {
        return 0;
    }

    // Build the minimized conflict: chain equalities + conclusion + non-equalities.
    let original_len = conflict.len();
    let mut minimized = Vec::with_capacity(chain_indices.len() + 1 + non_eq_indices.len());
    for &idx in &chain_indices {
        minimized.push(conflict[idx]);
    }
    for &idx in &non_eq_indices {
        minimized.push(conflict[idx]);
    }
    minimized.push(conc_lit);

    *conflict = minimized;
    original_len - conflict.len()
}

/// Minimize a Farkas conflict clause by removing literals with zero Farkas
/// coefficients. The `clause` and `coefficients` vectors are modified in
/// place and remain synchronized (same indices).
///
/// Returns the number of literals removed.
pub(crate) fn minimize_farkas_conflict(
    clause: &mut Vec<ay_sat::Literal>,
    coefficients: &mut Vec<num_rational::Rational64>,
) -> usize {
    use num_traits::Zero;

    if clause.len() <= MIN_CLAUSE_SIZE_FOR_MINIMIZE {
        return 0;
    }
    // Coefficient count mismatch — skip minimization to avoid corruption.
    if clause.len() != coefficients.len() {
        return 0;
    }

    let original_len = clause.len();

    // Count non-zero coefficients first to check for the degenerate case.
    let non_zero_count = coefficients.iter().filter(|c| !c.is_zero()).count();
    // All zeros → degenerate Farkas certificate. Skip minimization to avoid
    // producing an empty (or nearly empty) clause.
    if non_zero_count == 0 {
        return 0;
    }
    // Nothing to remove.
    if non_zero_count == original_len {
        return 0;
    }

    let mut write = 0;
    for read in 0..original_len {
        if !coefficients[read].is_zero() {
            clause[write] = clause[read];
            coefficients[write] = coefficients[read];
            write += 1;
        }
    }
    clause.truncate(write);
    coefficients.truncate(write);

    original_len - clause.len()
}

/// Minimize a plain (non-Farkas) conflict clause by removing duplicate
/// literals via sort + dedup.
///
/// Returns the number of duplicate literals removed.
///
/// Superseded by `minimize_conflict_with_levels` which also removes
/// level-0 literals. Retained for tests and as a fallback when level
/// information is not available.
#[allow(dead_code)]
pub(crate) fn minimize_plain_conflict(clause: &mut Vec<ay_sat::Literal>) -> usize {
    if clause.len() <= MIN_CLAUSE_SIZE_FOR_MINIMIZE {
        return 0;
    }

    let original_len = clause.len();
    clause.sort_unstable();
    clause.dedup();
    original_len - clause.len()
}

/// Minimize a theory conflict clause using SAT assignment levels.
///
/// This implements Z3/CaDiCaL-style self-subsumption for theory conflicts:
/// 1. Remove duplicate literals (sort + dedup)
/// 2. Remove literals assigned at decision level 0 (root-level assignments
///    are permanent and don't need to appear in blocking clauses)
/// 3. Remove tautological pairs (x and !x)
///
/// The `var_level` closure returns `Some(level)` for assigned variables and
/// `None` for unassigned ones. This allows the function to work with both
/// the SAT solver (via `Solver::var_level`) and the extension context (via
/// `SolverContext::var_level`).
///
/// Returns the number of literals removed.
pub(crate) fn minimize_conflict_with_levels(
    clause: &mut Vec<ay_sat::Literal>,
    var_level: impl Fn(ay_sat::Variable) -> Option<u32>,
) -> usize {
    if clause.len() <= MIN_CLAUSE_SIZE_FOR_MINIMIZE {
        return 0;
    }

    let original_len = clause.len();

    // Phase 1: Sort for dedup and tautology detection.
    clause.sort_unstable();

    // Phase 2: Single-pass compaction that removes:
    //   (a) duplicate literals (adjacent after sort)
    //   (b) tautological pairs — same variable, opposite polarity
    //   (c) literals assigned at decision level 0
    //
    // Level-0 literals are permanently assigned and can never be
    // backtracked. Including them in the blocking clause wastes space
    // without adding any conflict-driving information. Z3 performs this
    // in smt_conflict_resolution.cpp:process_antecedent() by skipping
    // level-0 literals during conflict clause construction.
    let mut write = 0;
    let mut i = 0;
    while i < clause.len() {
        let lit = clause[i];

        // Skip duplicate of previous literal.
        if write > 0 && clause[write - 1] == lit {
            i += 1;
            continue;
        }

        // Check for tautological pair: same variable, opposite polarity.
        // After sort, literals of the same variable are adjacent.
        if i + 1 < clause.len()
            && lit.variable() == clause[i + 1].variable()
            && lit != clause[i + 1]
        {
            // Skip both literals (tautology makes the clause trivially true).
            // However, a trivially-true conflict clause is unsound — if we
            // detect a tautology, skip the pair but do NOT short-circuit.
            // The caller (SAT solver) will handle the simplified clause.
            i += 2;
            continue;
        }

        // Remove level-0 literals.
        if var_level(lit.variable()) == Some(0) {
            i += 1;
            continue;
        }

        clause[write] = lit;
        write += 1;
        i += 1;
    }
    clause.truncate(write);

    original_len - clause.len()
}

/// Run the single-theory classifier chain over a whole conflict.
///
/// Extracted so the same chain can be applied to a SUB-conflict during
/// combined-theory decomposition (#combined-theory-decompose).
fn classify_whole_conflict(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    euf::infer_euf_lemma(terms, negations, conflict)
        .or_else(|| infer_arith_farkas(terms, conflict, clause))
        .or_else(|| infer_array_lemma(terms, clause))
        .or_else(|| infer_string_ground_eval_lemma(terms, clause))
        .or_else(|| infer_regex_intersect_empty_lemma(terms, clause))
        .or_else(|| infer_fp_ground_eval_lemma(terms, clause))
        .filter(|(kind, _)| *kind != TheoryLemmaKind::Generic)
}

/// How many literals the core search may drop from a mixed conflict.
///
/// The mixed conflicts observed in practice carry a small number of foreign
/// literals (sampled shapes: a datatype-tester core plus one or two equalities,
/// a set/array core plus a select). Three covers those while keeping the search
/// small; the attempt cap below is the real bound.
const DECOMPOSE_MAX_DROPPED: usize = 3;

/// Hard cap on classifier invocations per conflict, so a wide conflict cannot
/// turn proof production into a combinatorial search.
const DECOMPOSE_MAX_ATTEMPTS: usize = 512;

/// Find a single-theory core inside a mixed conflict (#combined-theory-decompose).
///
/// Returns `(kind, core_clause, full_clause)` where `core_clause` is the
/// classifier's own ordering of the core literals and `full_clause` is the
/// complete blocking clause with `core_clause` as a PREFIX — the exact shape
/// `weakening` requires (`ay-proof` `validate_weakening`: the premise clause
/// must be a prefix of the result).
///
/// Soundness: the emitted core lemma is checked by its own kind's validator, and
/// weakening a valid clause by appending literals preserves validity. The full
/// clause is literal-for-literal the same SET the caller would have emitted as
/// `Generic`, so nothing downstream sees a different fact — only a checkable
/// justification for it.
fn classifiable_core_decomposition(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>)> {
    // `clause[i]` is the blocking literal for `conflict[i]`
    // (`build_blocking_clause_terms` maps them positionally).
    if conflict.len() != clause.len() || conflict.len() < 2 {
        return None;
    }

    let mut attempts = 0usize;
    let max_dropped = DECOMPOSE_MAX_DROPPED.min(conflict.len().saturating_sub(1));

    // Prefer the LARGEST core: dropping fewer literals keeps more of the
    // conflict inside the checked lemma.
    for dropped in 1..=max_dropped {
        let mut drop_idx = (0..dropped).collect::<Vec<usize>>();
        loop {
            if attempts >= DECOMPOSE_MAX_ATTEMPTS {
                return None;
            }
            attempts += 1;

            let keep: Vec<usize> = (0..conflict.len())
                .filter(|i| !drop_idx.contains(i))
                .collect();
            let sub_conflict: Vec<TheoryLit> = keep.iter().map(|&i| conflict[i]).collect();
            let sub_clause: Vec<TermId> = keep.iter().map(|&i| clause[i]).collect();

            if let Some((kind, core_clause)) =
                classify_whole_conflict(terms, negations, &sub_conflict, &sub_clause)
            {
                // The classifier may reorder its literals; the core must stay a
                // prefix, so rebuild the full clause as core ++ dropped.
                let core_set: HashSet<TermId> = core_clause.iter().copied().collect();
                if core_set.len() == core_clause.len() {
                    let mut full_clause = core_clause.clone();
                    for &lit in clause {
                        if !core_set.contains(&lit) {
                            full_clause.push(lit);
                        }
                    }
                    // Only accept when the weakened clause still covers the
                    // original blocking clause exactly. A malformed candidate
                    // must not abort the bounded search: a later subset can
                    // still expose an unambiguous core.
                    let full_set: HashSet<TermId> = full_clause.iter().copied().collect();
                    let orig_set: HashSet<TermId> = clause.iter().copied().collect();
                    if full_set == orig_set {
                        return Some((kind, core_clause, full_clause));
                    }
                }
            }

            // Next combination of dropped indices (lexicographic). Exhausting
            // this cardinality continues the outer loop so cores that require
            // dropping two or three foreign literals are still considered.
            if !advance_combination(&mut drop_idx, conflict.len()) {
                break;
            }
        }
    }
    None
}

fn advance_combination(indices: &mut [usize], universe_len: usize) -> bool {
    let selected = indices.len();
    for position in (0..selected).rev() {
        let Some(max_index) = universe_len.checked_sub(selected - position) else {
            return false;
        };
        if indices[position] < max_index {
            indices[position] += 1;
            for later in position + 1..selected {
                indices[later] = indices[later - 1] + 1;
            }
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn conflict_outcome_keeps_euf_reorder_tracker_and_annotation_identical() {
        let mut terms = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let a = terms.mk_var("a", u.clone());
        let b = terms.mk_var("b", u.clone());
        let c = terms.mk_var("c", u);
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_ac = terms.mk_eq(a, c);
        let not_ab = terms.mk_not(eq_ab);
        let not_bc = terms.mk_not(eq_bc);
        let mut negations = HashMap::default();
        negations.insert(eq_ab, not_ab);
        negations.insert(eq_bc, not_bc);

        // Conclusion first makes the materialized caller order invalid for
        // the strict EUF validator. The atomic outcome must expose the exact
        // validator order recorded in the tracker.
        let conflict = vec![
            TheoryLit::new(eq_ac, false),
            TheoryLit::new(eq_bc, true),
            TheoryLit::new(eq_ab, true),
        ];
        let mut tracker = ProofTracker::new();
        tracker.enable();
        let (id, annotation) = record_theory_conflict_unsat_with_annotation(
            &mut tracker,
            Some(&terms),
            &negations,
            &conflict,
        );
        let id = id.expect("EUF conflict recorded");
        let annotation = annotation.expect("direct EUF annotation");
        let proof = tracker.take_proof();
        let Some(ay_core::ProofStep::TheoryLemma {
            clause,
            kind,
            farkas,
            lia,
            ..
        }) = proof.get_step(id)
        else {
            panic!("expected direct theory lemma");
        };
        assert_eq!(annotation.clause, *clause);
        assert_eq!(annotation.kind, *kind);
        assert_eq!(annotation.farkas, *farkas);
        assert_eq!(annotation.lia, *lia);
        assert_eq!(*kind, TheoryLemmaKind::EufTransitive);
        assert!(ay_proof::recognize_euf_transitive(&terms, clause));
    }

    #[test]
    fn conflict_outcome_keeps_array_tracker_and_annotation_identical() {
        let mut terms = TermStore::new();
        let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
        let array = terms.mk_var("a", array_sort.clone());
        let index = terms.mk_var("i", Sort::Int);
        let value = terms.mk_var("v", Sort::Int);
        let store = terms.mk_app(Symbol::named("store"), [array, index, value], array_sort);
        let select = terms.mk_app(Symbol::named("select"), [store, index], Sort::Int);
        let row = terms.mk_eq(select, value);
        let conflict = [TheoryLit::new(row, false)];
        let mut tracker = ProofTracker::new();
        tracker.enable();
        let (id, annotation) = record_theory_conflict_unsat_with_annotation(
            &mut tracker,
            Some(&terms),
            &HashMap::default(),
            &conflict,
        );
        let id = id.expect("array conflict recorded");
        let annotation = annotation.expect("direct array annotation");
        let proof = tracker.take_proof();
        let Some(ay_core::ProofStep::TheoryLemma {
            clause,
            kind,
            farkas,
            lia,
            ..
        }) = proof.get_step(id)
        else {
            panic!("expected direct theory lemma");
        };
        assert_eq!(annotation.clause, *clause);
        assert_eq!(annotation.kind, *kind);
        assert_eq!(annotation.farkas, *farkas);
        assert_eq!(annotation.lia, *lia);
        assert_eq!(*kind, TheoryLemmaKind::ArraySelectStore { index_eq: true });
    }

    #[test]
    fn conflict_outcome_with_weakening_has_no_lossy_direct_annotation() {
        let mut terms = TermStore::new();
        let foreign = terms.mk_var("foreign", Sort::Bool);
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
        let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
        let le_zero = terms.mk_le(x, zero);
        let ge_one = terms.mk_ge(x, one);
        let conflict = vec![
            TheoryLit::new(foreign, true),
            TheoryLit::new(le_zero, true),
            TheoryLit::new(ge_one, true),
        ];
        let mut negations = HashMap::default();
        for literal in &conflict {
            negations.insert(literal.term, terms.mk_not(literal.term));
        }
        let mut tracker = ProofTracker::new();
        tracker.enable();
        let (id, annotation) = record_theory_conflict_unsat_with_annotation(
            &mut tracker,
            Some(&terms),
            &negations,
            &conflict,
        );
        let id = id.expect("decomposed conflict recorded");
        assert!(
            annotation.is_none(),
            "TheoryLemmaProof cannot encode the weakening premise"
        );
        let proof = tracker.take_proof();
        assert!(matches!(
            proof.get_step(id),
            Some(ay_core::ProofStep::Step {
                rule: ay_core::AletheRule::Weakening,
                ..
            })
        ));
    }

    #[test]
    fn rejected_farkas_outcome_is_generic_without_payload_everywhere() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
        let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
        let ge_one = terms.mk_ge(x, one);
        let le_zero = terms.mk_le(x, zero);
        let mut negations = HashMap::default();
        negations.insert(ge_one, terms.mk_not(ge_one));
        negations.insert(le_zero, terms.mk_not(le_zero));
        let conflict = TheoryConflict::with_farkas(
            vec![TheoryLit::new(ge_one, true), TheoryLit::new(le_zero, true)],
            FarkasAnnotation::from_ints(&[1, 0]),
        );
        let mut tracker = ProofTracker::new();
        tracker.enable();
        let (id, annotation) = record_theory_conflict_unsat_with_farkas_and_annotation(
            &mut tracker,
            Some(&terms),
            &negations,
            &conflict,
        );
        let id = id.expect("rejected-certificate conflict recorded");
        let annotation = annotation.expect("Generic direct annotation");
        let proof = tracker.take_proof();
        let Some(ay_core::ProofStep::TheoryLemma { kind, farkas, .. }) = proof.get_step(id) else {
            panic!("expected theory lemma");
        };
        assert_eq!(*kind, TheoryLemmaKind::Generic);
        assert!(farkas.is_none());
        assert_eq!(annotation.kind, *kind);
        assert!(annotation.farkas.is_none());
    }

    #[test]
    fn c3_evidence_less_arithmetic_annotation_matches_tracker_demotion() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let x_eq_y = terms.mk_eq(x, y);
        let clause = vec![terms.mk_not_raw(x_eq_y)];
        let (raw_kind, _) =
            infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
        assert_eq!(raw_kind, TheoryLemmaKind::LiaGeneric);

        let mut tracker = ProofTracker::new();
        tracker.enable();
        let (effective_kind, recorded) =
            record_funnel_classified_lemma(&mut tracker, &terms, clause, None);
        assert_eq!(effective_kind, TheoryLemmaKind::Generic);
        let proof = tracker.take_proof();
        let Some(ay_core::ProofStep::TheoryLemma { kind, clause, .. }) = proof.steps.first() else {
            panic!("expected theory lemma");
        };
        assert_eq!(*kind, effective_kind);
        assert_eq!(clause, &recorded);
    }

    #[test]
    fn combined_theory_core_search_advances_to_two_dropped_literals() {
        use num_rational::BigRational;

        let mut terms = TermStore::new();
        let foreign_a = terms.mk_var("foreign_a", Sort::Bool);
        let foreign_b = terms.mk_var("foreign_b", Sort::Bool);
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
        let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
        let le_zero = terms.mk_le(x, zero);
        let ge_one = terms.mk_ge(x, one);
        let conflict = vec![
            TheoryLit::new(foreign_a, true),
            TheoryLit::new(foreign_b, true),
            TheoryLit::new(le_zero, true),
            TheoryLit::new(ge_one, true),
        ];
        let mut negations = HashMap::default();
        for literal in &conflict {
            negations.insert(literal.term, terms.mk_not(literal.term));
        }
        let clause = build_blocking_clause_terms(&negations, &conflict)
            .expect("every conflict literal has a negation");

        let (kind, core, weakened) =
            classifiable_core_decomposition(&terms, &negations, &conflict, &clause)
                .expect("dropping both foreign literals exposes the arithmetic core");

        assert_eq!(kind, TheoryLemmaKind::LraFarkas);
        assert_eq!(core.len(), 2);
        assert_eq!(weakened.len(), clause.len());
    }

    #[test]
    fn ambiguous_duplicate_core_does_not_abort_later_candidates() {
        use num_rational::BigRational;

        let mut terms = TermStore::new();
        let foreign = terms.mk_var("foreign", Sort::Bool);
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
        let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
        let le_zero = terms.mk_le(x, zero);
        let ge_one = terms.mk_ge(x, one);
        // Dropping `foreign` first exposes a classifiable but duplicate core.
        // The search must reject that candidate and continue until it also
        // drops one copy of `le_zero`.
        let conflict = vec![
            TheoryLit::new(foreign, true),
            TheoryLit::new(le_zero, true),
            TheoryLit::new(ge_one, true),
            TheoryLit::new(le_zero, true),
        ];
        let mut negations = HashMap::default();
        for literal in &conflict {
            negations
                .entry(literal.term)
                .or_insert_with(|| terms.mk_not(literal.term));
        }
        let clause = build_blocking_clause_terms(&negations, &conflict)
            .expect("every conflict literal has a negation");

        let (kind, core, _) =
            classifiable_core_decomposition(&terms, &negations, &conflict, &clause)
                .expect("a later unambiguous arithmetic core remains available");

        assert_eq!(kind, TheoryLemmaKind::LraFarkas);
        assert_eq!(core.len(), 2);
    }

    #[test]
    fn test_infer_theory_lemma_kind_from_clause_terms_and_farkas_strict_int_bounds() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let ten = terms.mk_int(BigInt::from(10));
        let five = terms.mk_int(BigInt::from(5));
        let gt = terms.mk_gt(x, ten);
        let lt = terms.mk_lt(x, five);
        let clause = vec![terms.mk_not(gt), terms.mk_not(lt)];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);

        let (kind, ordered) = infer_theory_lemma_kind_from_clause_terms_and_farkas(
            &terms,
            &clause,
            Some(&farkas),
            None,
        );
        assert_eq!(kind, TheoryLemmaKind::LraFarkas);
        assert_eq!(ordered.as_ref(), clause.as_slice());
    }

    #[test]
    fn la_generic_eligibility_rejects_variable_products_and_divisors() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let two = terms.mk_rational(num_rational::BigRational::from(BigInt::from(2)));

        let scaled = terms.mk_mul(vec![x, two]);
        let product = terms.mk_mul(vec![x, y]);
        let divided_by_constant = terms.mk_div(x, two);
        let divided_by_variable = terms.mk_div(x, y);

        assert!(is_pure_la_term(&terms, scaled));
        assert!(!is_pure_la_term(&terms, product));
        assert!(is_pure_la_term(&terms, divided_by_constant));
        assert!(!is_pure_la_term(&terms, divided_by_variable));
    }

    #[test]
    fn la_generic_classification_requires_semantically_valid_coefficients() {
        use num_rational::BigRational;

        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
        let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
        let le_zero = terms.mk_le(x, zero);
        let ge_one = terms.mk_ge(x, one);
        let conflict = [TheoryLit::new(le_zero, true), TheoryLit::new(ge_one, true)];

        let valid = FarkasAnnotation::from_ints(&[1, 1]);
        assert_eq!(
            classify_arith_conflict_kind(&terms, &conflict, Some(&valid)),
            TheoryLemmaKind::LraFarkas
        );

        let misbound = FarkasAnnotation::from_ints(&[2, 1]);
        assert_eq!(
            classify_arith_conflict_kind(&terms, &conflict, Some(&misbound)),
            TheoryLemmaKind::Generic
        );
    }

    // =====================================================================
    // Theory conflict clause minimization tests (#8424)
    // =====================================================================

    /// Helper: make a positive Literal from a raw variable id.
    fn lit(v: u32) -> ay_sat::Literal {
        ay_sat::Literal::positive(ay_sat::Variable::new(v))
    }

    #[test]
    fn test_minimize_farkas_conflict_removes_zero_coefficients() {
        use num_rational::Rational64;

        // 6 literals, coefficients [1, 0, 3, 0, 2, 0] → keep indices 0, 2, 4
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)];
        let mut coeffs = vec![
            Rational64::from_integer(1),
            Rational64::from_integer(0),
            Rational64::from_integer(3),
            Rational64::from_integer(0),
            Rational64::from_integer(2),
            Rational64::from_integer(0),
        ];
        let removed = minimize_farkas_conflict(&mut clause, &mut coeffs);
        assert_eq!(removed, 3);
        assert_eq!(clause.len(), 3);
        assert_eq!(coeffs.len(), 3);
        assert_eq!(clause, vec![lit(1), lit(3), lit(5)]);
        assert_eq!(coeffs[0], Rational64::from_integer(1));
        assert_eq!(coeffs[1], Rational64::from_integer(3));
        assert_eq!(coeffs[2], Rational64::from_integer(2));
    }

    #[test]
    fn test_minimize_farkas_conflict_skips_small_clauses() {
        use num_rational::Rational64;

        // 4 literals — below threshold, should not be modified
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4)];
        let mut coeffs = vec![
            Rational64::from_integer(1),
            Rational64::from_integer(0),
            Rational64::from_integer(0),
            Rational64::from_integer(2),
        ];
        let removed = minimize_farkas_conflict(&mut clause, &mut coeffs);
        assert_eq!(removed, 0);
        assert_eq!(clause.len(), 4);
    }

    #[test]
    fn test_minimize_farkas_conflict_no_zeros_passthrough() {
        use num_rational::Rational64;

        // 6 literals, all non-zero — nothing to remove
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)];
        let mut coeffs = vec![
            Rational64::from_integer(1),
            Rational64::from_integer(2),
            Rational64::from_integer(3),
            Rational64::from_integer(4),
            Rational64::from_integer(5),
            Rational64::from_integer(6),
        ];
        let removed = minimize_farkas_conflict(&mut clause, &mut coeffs);
        assert_eq!(removed, 0);
        assert_eq!(clause.len(), 6);
    }

    #[test]
    fn test_minimize_farkas_conflict_all_zeros_degenerate() {
        use num_rational::Rational64;

        // 6 literals, all zero coefficients — degenerate Farkas certificate.
        // Minimization is skipped to avoid producing an empty clause.
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)];
        let mut coeffs = vec![Rational64::from_integer(0); 6];
        let removed = minimize_farkas_conflict(&mut clause, &mut coeffs);
        assert_eq!(removed, 0);
        assert_eq!(
            clause.len(),
            6,
            "all-zero degenerate case should preserve clause"
        );
    }

    #[test]
    fn test_minimize_plain_conflict_removes_duplicates() {
        // 6 literals with duplicates
        let mut clause = vec![lit(3), lit(1), lit(3), lit(2), lit(1), lit(4)];
        let removed = minimize_plain_conflict(&mut clause);
        assert_eq!(removed, 2);
        assert_eq!(clause.len(), 4);
        // After sort+dedup, should be [lit(1), lit(2), lit(3), lit(4)]
        assert_eq!(clause, vec![lit(1), lit(2), lit(3), lit(4)]);
    }

    #[test]
    fn test_minimize_plain_conflict_skips_small_clauses() {
        // 3 literals — below threshold
        let mut clause = vec![lit(1), lit(1), lit(2)];
        let removed = minimize_plain_conflict(&mut clause);
        assert_eq!(removed, 0);
        assert_eq!(clause.len(), 3);
    }

    #[test]
    fn test_minimize_plain_conflict_no_duplicates_passthrough() {
        // 6 unique literals — nothing to remove
        let mut clause = vec![lit(6), lit(5), lit(4), lit(3), lit(2), lit(1)];
        let removed = minimize_plain_conflict(&mut clause);
        assert_eq!(removed, 0);
        assert_eq!(clause.len(), 6);
        // But they should now be sorted
        assert_eq!(clause, vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)]);
    }

    // =====================================================================
    // EUF conflict clause minimization tests (#8424)
    // =====================================================================

    #[test]
    fn test_minimize_euf_conflict_removes_redundant_equalities() {
        // Conflict: (= a b)=true, (= b c)=true, (= a c)=true, (= c d)=true,
        //           (= a d)=false
        // BFS finds shortest path a->c->d (via eq_ac, eq_cd), which is
        // length 2. This makes eq_ab and eq_bc redundant (removed = 2).
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let d = terms.mk_var("d", Sort::Int);
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_ac = terms.mk_eq(a, c);
        let eq_cd = terms.mk_eq(c, d);
        let eq_ad = terms.mk_eq(a, d);

        let mut conflict = vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
            TheoryLit::new(eq_ac, true),
            TheoryLit::new(eq_cd, true),
            TheoryLit::new(eq_ad, false), // conclusion
        ];

        let removed = minimize_euf_conflict(&mut conflict, &terms);
        assert!(
            removed >= 1,
            "should remove at least one redundant equality, got {removed}"
        );
        // The conclusion should still be present.
        assert!(conflict.iter().any(|l| l.term == eq_ad && !l.value));
    }

    #[test]
    fn test_minimize_euf_conflict_skips_small_clauses() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_ac = terms.mk_eq(a, c);

        // 3 literals — below threshold
        let mut conflict = vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
            TheoryLit::new(eq_ac, false),
        ];
        let removed = minimize_euf_conflict(&mut conflict, &terms);
        assert_eq!(removed, 0, "should skip small clauses");
        assert_eq!(conflict.len(), 3);
    }

    #[test]
    fn test_minimize_euf_conflict_no_reduction_possible() {
        // All equalities are part of the shortest chain.
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let d = terms.mk_var("d", Sort::Int);
        let e = terms.mk_var("e", Sort::Int);
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_cd = terms.mk_eq(c, d);
        let eq_de = terms.mk_eq(d, e);
        let eq_ae = terms.mk_eq(a, e);

        let mut conflict = vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
            TheoryLit::new(eq_cd, true),
            TheoryLit::new(eq_de, true),
            TheoryLit::new(eq_ae, false),
        ];
        let removed = minimize_euf_conflict(&mut conflict, &terms);
        assert_eq!(removed, 0, "all equalities are essential");
        assert_eq!(conflict.len(), 5);
    }

    #[test]
    fn test_minimize_euf_conflict_non_equality_pattern_passthrough() {
        // No negated equality → not an EUF transitivity pattern.
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let d = terms.mk_var("d", Sort::Int);
        let e = terms.mk_var("e", Sort::Int);
        let eq_ab = terms.mk_eq(a, b);
        let eq_bc = terms.mk_eq(b, c);
        let eq_cd = terms.mk_eq(c, d);
        let eq_de = terms.mk_eq(d, e);
        let eq_ae = terms.mk_eq(a, e);

        // All true (no conclusion) — not minimizable as EUF transitivity.
        let mut conflict = vec![
            TheoryLit::new(eq_ab, true),
            TheoryLit::new(eq_bc, true),
            TheoryLit::new(eq_cd, true),
            TheoryLit::new(eq_de, true),
            TheoryLit::new(eq_ae, true),
        ];
        let removed = minimize_euf_conflict(&mut conflict, &terms);
        assert_eq!(
            removed, 0,
            "no negated equality → not a transitivity pattern"
        );
    }

    // =====================================================================
    // Level-aware conflict clause minimization tests (#8424)
    // =====================================================================

    /// Helper: make a negative Literal from a raw variable id.
    fn neg_lit(v: u32) -> ay_sat::Literal {
        ay_sat::Literal::negative(ay_sat::Variable::new(v))
    }

    #[test]
    fn test_minimize_conflict_with_levels_removes_level0_literals() {
        // 6 literals: vars 1,2,3 at level 0, vars 4,5,6 at level 3
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)];
        let removed = minimize_conflict_with_levels(&mut clause, |var| {
            if var.index() <= 3 {
                Some(0) // level 0
            } else {
                Some(3) // level 3
            }
        });
        assert_eq!(removed, 3, "should remove 3 level-0 literals");
        assert_eq!(clause.len(), 3);
        // Remaining literals should be vars 4, 5, 6 (sorted)
        assert_eq!(clause, vec![lit(4), lit(5), lit(6)]);
    }

    #[test]
    fn test_minimize_conflict_with_levels_removes_duplicates() {
        // 6 literals with duplicates, all at non-zero levels
        let mut clause = vec![lit(3), lit(1), lit(3), lit(2), lit(1), lit(4)];
        let removed = minimize_conflict_with_levels(&mut clause, |_| Some(5));
        assert_eq!(removed, 2, "should remove 2 duplicates");
        assert_eq!(clause.len(), 4);
        assert_eq!(clause, vec![lit(1), lit(2), lit(3), lit(4)]);
    }

    #[test]
    fn test_minimize_conflict_with_levels_removes_level0_and_duplicates() {
        // Mix of duplicates and level-0 assignments
        let mut clause = vec![lit(1), lit(2), lit(1), lit(3), lit(4), lit(5)];
        let removed = minimize_conflict_with_levels(&mut clause, |var| {
            if var.index() == 2 || var.index() == 4 {
                Some(0)
            } else {
                Some(2)
            }
        });
        // Removes: 1 duplicate of lit(1), lit(2) at level 0, lit(4) at level 0
        assert_eq!(removed, 3);
        assert_eq!(clause.len(), 3);
        assert_eq!(clause, vec![lit(1), lit(3), lit(5)]);
    }

    #[test]
    fn test_minimize_conflict_with_levels_skips_small_clauses() {
        let mut clause = vec![lit(1), lit(2), lit(3)];
        let removed = minimize_conflict_with_levels(&mut clause, |_| Some(0));
        assert_eq!(removed, 0, "should skip clauses below threshold");
        assert_eq!(clause.len(), 3);
    }

    #[test]
    fn test_minimize_conflict_with_levels_unassigned_vars_kept() {
        // Unassigned variables (None level) should be kept
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)];
        let removed = minimize_conflict_with_levels(&mut clause, |var| {
            if var.index() <= 3 {
                None // unassigned
            } else {
                Some(0) // level 0
            }
        });
        assert_eq!(removed, 3, "should remove 3 level-0 literals");
        assert_eq!(clause.len(), 3);
        assert_eq!(clause, vec![lit(1), lit(2), lit(3)]);
    }

    #[test]
    fn test_minimize_conflict_with_levels_tautology_removal() {
        // Clause with both x and !x for some variable
        let mut clause = vec![lit(1), neg_lit(1), lit(2), lit(3), lit(4), lit(5)];
        let removed = minimize_conflict_with_levels(&mut clause, |_| Some(2));
        // lit(1) and neg_lit(1) form a tautological pair — both removed
        assert_eq!(removed, 2, "should remove tautological pair");
        assert_eq!(clause.len(), 4);
    }

    #[test]
    fn test_minimize_conflict_with_levels_all_level0_returns_empty() {
        // All literals at level 0 — clause becomes empty
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)];
        let removed = minimize_conflict_with_levels(&mut clause, |_| Some(0));
        assert_eq!(removed, 6);
        assert!(clause.is_empty());
    }

    #[test]
    fn test_minimize_conflict_with_levels_no_removals() {
        // All at non-zero levels, no duplicates
        let mut clause = vec![lit(1), lit(2), lit(3), lit(4), lit(5), lit(6)];
        let removed = minimize_conflict_with_levels(&mut clause, |_| Some(3));
        assert_eq!(removed, 0);
        assert_eq!(clause.len(), 6);
    }
}
