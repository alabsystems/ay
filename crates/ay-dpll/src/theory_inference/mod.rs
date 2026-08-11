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

mod decompose;
mod euf;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    FarkasAnnotation, ProofId, Sort, Symbol, TermData, TermId, TermStore, TheoryConflict,
    TheoryLemmaKind, TheoryLit,
};

use crate::proof_tracker::ProofTracker;

// Re-export pub(crate) items from submodules.
pub(crate) use decompose::decompose_generic_combined_real_lemma;

/// Record a theory conflict and infer the most specific Alethe rule.
pub(crate) fn record_theory_conflict_unsat(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<ProofId> {
    if !tracker.is_enabled() {
        return None;
    }

    let Some(clause) = build_blocking_clause_terms(negations, conflict) else {
        return tracker.add_theory_lemma(conflict.iter().map(|lit| lit.term).collect::<Vec<_>>());
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
                    return tracker.add_theory_lemma_weakened(core_clause, core_kind, full_clause);
                }
                (TheoryLemmaKind::Generic, clause)
            }
        }
    } else {
        (TheoryLemmaKind::Generic, clause)
    };

    match kind {
        TheoryLemmaKind::Generic => tracker.add_theory_lemma(ordered_clause),
        TheoryLemmaKind::LiaGeneric => {
            let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; ordered_clause.len()]);
            tracker.add_theory_lemma_with_farkas_and_kind(ordered_clause, unit_farkas, kind)
        }
        TheoryLemmaKind::LraFarkas => {
            let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; ordered_clause.len()]);
            tracker.add_theory_lemma_with_farkas_and_kind(ordered_clause, unit_farkas, kind)
        }
        _ => tracker.add_theory_lemma_with_kind(ordered_clause, kind),
    }
}

/// Infer the most specific proof kind available for an already-materialized
/// theory lemma clause.
#[must_use]
pub(crate) fn infer_theory_lemma_kind_from_clause_terms(
    terms: &TermStore,
    clause: &[TermId],
) -> TheoryLemmaKind {
    infer_theory_lemma_kind_from_clause_terms_and_farkas(terms, clause, None)
}

/// Infer the most specific proof kind available for an already-materialized
/// theory lemma clause, using semantic Farkas validation when coefficients are
/// already available.
#[must_use]
pub(crate) fn infer_theory_lemma_kind_from_clause_terms_and_farkas(
    terms: &TermStore,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> TheoryLemmaKind {
    let conflict = blocking_clause_to_conflict_lits(terms, clause);

    if let Some(farkas) = farkas {
        let kind = classify_arith_conflict_kind(terms, &conflict, Some(farkas));
        if kind != TheoryLemmaKind::Generic {
            return kind;
        }
    }

    if !conflict.is_empty() && conflict_all_arith_literals(terms, &conflict) {
        let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; conflict.len()]);
        let kind = classify_arith_conflict_kind(terms, &conflict, Some(&unit_farkas));
        if kind == TheoryLemmaKind::LraFarkas {
            return kind;
        }
    }

    // Array axiom instances (read-over-write, n-ary store permutation, chain
    // read-over-write): classify into the strict-checkable kinds the checker
    // validates (`ay-proof` `validate_array_*`), so they no longer fall back to
    // the `Generic`/trust kind. Recognition reuses the checker's own schema
    // matcher (no drift). Drives `ProofQuality::trust_count` down for QF_AX.
    if let Some(kind) = ay_proof::recognize_array_theory_lemma(terms, clause) {
        return kind;
    }

    // Ground string/regex refutations: the QF_S "sink" family reduces to
    // "this CONSTANT is not in the language of this ground regex", a closed
    // form the checker decides outright. Classify into the strict-checkable
    // `StringGroundEval` kind so it stops exporting as `trust`. Recognition is
    // the checker's own evaluator (`ay_proof::recognize_string_ground_eval`),
    // so classifier and validator cannot drift.
    if ay_proof::recognize_string_ground_eval(terms, clause) {
        return TheoryLemmaKind::StringGroundEval;
    }

    // Symbolic regex intersection-emptiness (#regex-cert): the automatark
    // family refutes `x ∈ R₁ ∧ … ∧ x ∈ Rₖ` on a SYMBOLIC `x`, which the ground
    // evaluator above cannot touch. Classify into the strict-checkable
    // `RegexIntersectEmpty` kind so it stops exporting as `trust`. Recognition
    // is the checker's own independent derivative-product emptiness decision
    // (`ay_proof::recognize_regex_intersect_empty`), so classifier and
    // validator cannot drift.
    if ay_proof::recognize_regex_intersect_empty(terms, clause) {
        return TheoryLemmaKind::RegexIntersectEmpty;
    }

    // Pure-NRA refutations (#nra-cert): a genuinely NONLINEAR real-arithmetic
    // conflict (mbo/hong-class) whose negation the strict checker itself
    // re-refutes. Recognition is the checker's own exact decision
    // (`ay_proof::recognize_nra_univariate_unsat` — Sturm-based univariate
    // cell decomposition — and `ay_proof::recognize_nra_interval_unsat` —
    // bounded exact-rational interval propagation), so classifier and
    // validator cannot drift. Univariate runs first: its one-variable gate is
    // cheap and it is the more precise decision on univariate systems.
    //
    // These arms run BEFORE `arith_conflict_is_integer` so a nonlinear,
    // real-refutable NIA conflict certifies instead of being tagged
    // `LiaGeneric` and rejected; the checkers' nonlinearity gate guarantees
    // no LINEAR conflict is touched (no label-stealing from
    // LraFarkas/LiaGeneric).
    if ay_proof::recognize_nra_univariate_unsat(terms, clause) {
        return TheoryLemmaKind::NraUnivariateUnsat;
    }
    if ay_proof::recognize_nra_interval_unsat(terms, clause) {
        return TheoryLemmaKind::NraIntervalUnsat;
    }

    if arith_conflict_is_integer(terms, &conflict) {
        return TheoryLemmaKind::LiaGeneric;
    }

    // Opaque-atom Farkas conflicts (#trust-count→0, class 4): inequalities (and
    // asserted-true equalities) over uninterpreted Int/Real atoms — `(f x)`,
    // `(select a i)` — are valid `la_generic` steps (Alethe checkers treat
    // non-arithmetic subterms as opaque variables), but the pure-LA eligibility
    // above rejects them. This branch fires ONLY where the classifier would
    // otherwise fall back to `Generic`/trust, and ONLY when the certificate
    // passes the FULL semantic Farkas verifier (fail-closed; never a
    // shape-only promotion).
    match farkas {
        Some(farkas) => {
            if opaque_arith_farkas_valid(terms, &conflict, farkas) {
                return TheoryLemmaKind::LraFarkas;
            }
        }
        // No annotation on the step yet: classify with the unit certificate.
        // The caller (`promote_generic_theory_lemma_kinds_after_rewrite`)
        // attaches the SAME unit certificate it re-verifies, so the exported
        // `:args` are exactly the coefficients that passed the full check.
        None if !conflict.is_empty() => {
            let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; conflict.len()]);
            if opaque_arith_farkas_valid(terms, &conflict, &unit_farkas) {
                return TheoryLemmaKind::LraFarkas;
            }
        }
        None => {}
    }

    // Non-integer, non-LRA, non-array clause with no Farkas classification.
    // Could be EUF, string, datatype, or combined theory. Needs classifier.
    TheoryLemmaKind::Generic
}

/// Whether every conflict literal is an "opaque-atom" linear-arithmetic
/// literal — a binary `<`/`<=`/`>`/`>=` comparison over Int/Real-sorted terms
/// (uninterpreted subterms are treated as opaque variables, exactly as the
/// semantic Farkas verifier and Alethe `la_generic` checkers do), or an
/// equality over Int/Real-sorted terms that is asserted TRUE (its blocking
/// literal is the negation, which `la_generic` consumes as an equality; an
/// equality asserted false would need a disequality case split downstream
/// checkers do not perform, so it is rejected) — AND the given certificate
/// passes the full semantic Farkas check in LINEAR-ONLY mode (no #4666
/// congruence merging, which external `la_generic` checkers cannot replay).
fn opaque_arith_farkas_valid(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> bool {
    if conflict.is_empty() {
        return false;
    }
    let eligible = conflict.iter().all(|lit| {
        let atom = strip_not(terms, lit.term);
        // `strip_not` flips into conflict polarity: a `Not` wrapper on the
        // conflict literal inverts the asserted value.
        let value = if matches!(terms.get(lit.term), TermData::Not(_)) {
            !lit.value
        } else {
            lit.value
        };
        match terms.get(atom) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let arith_sorts = matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                    && matches!(terms.sort(args[1]), Sort::Int | Sort::Real);
                match name.as_str() {
                    "<" | "<=" | ">" | ">=" => arith_sorts,
                    "=" => arith_sorts && value,
                    _ => false,
                }
            }
            _ => false,
        }
    });
    if !eligible {
        return false;
    }
    // LINEAR-only verification: no congruence-closure merging of opaque
    // terms, matching exactly what external `la_generic` checkers can check.
    ay_core::proof_validation::verify_farkas_conflict_lits_linear(terms, conflict, farkas).is_ok()
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

/// Infer the proof kind for a theory conflict that will be materialized as an
/// original SAT clause in the clause trace.
#[must_use]
pub(crate) fn infer_theory_conflict_kind(
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
    farkas: Option<&FarkasAnnotation>,
) -> TheoryLemmaKind {
    match terms {
        Some(terms) => {
            if let Some(farkas) = farkas {
                let kind = classify_arith_conflict_kind(terms, conflict, Some(farkas));
                if kind != TheoryLemmaKind::Generic {
                    return kind;
                }
            }

            if !conflict.is_empty() && conflict_all_arith_literals(terms, conflict) {
                let unit_farkas = FarkasAnnotation::from_ints(&vec![1i64; conflict.len()]);
                let kind = classify_arith_conflict_kind(terms, conflict, Some(&unit_farkas));
                if kind == TheoryLemmaKind::LraFarkas {
                    return kind;
                }
            }

            euf::infer_euf_lemma(terms, negations, conflict).map_or_else(
                || {
                    if arith_conflict_is_integer(terms, conflict) {
                        TheoryLemmaKind::LiaGeneric
                    } else if farkas.is_some_and(|f| opaque_arith_farkas_valid(terms, conflict, f))
                    {
                        // Opaque-atom rescue (class 4): fully verified Farkas
                        // certificate over uninterpreted Int/Real atoms.
                        TheoryLemmaKind::LraFarkas
                    } else {
                        // Non-EUF, non-arith conflict. Needs classifier
                        // for string, array, or combined theory conflicts.
                        TheoryLemmaKind::Generic
                    }
                },
                |(kind, _)| kind,
            )
        }
        // No TermStore available -- cannot classify. This path is
        // hit when proof generation is disabled or terms are not accessible.
        None => TheoryLemmaKind::Generic,
    }
}

/// Record a theory conflict with Farkas coefficients (arithmetic theories).
pub(crate) fn record_theory_conflict_unsat_with_farkas(
    tracker: &mut ProofTracker,
    terms: Option<&TermStore>,
    negations: &HashMap<TermId, TermId>,
    conflict: &TheoryConflict,
) -> Option<ProofId> {
    if !tracker.is_enabled() {
        return None;
    }

    let Some(farkas) = conflict.farkas.clone() else {
        let clause = build_blocking_clause_terms(negations, &conflict.literals)?;
        return tracker.add_theory_lemma(clause);
    };

    let clause = build_blocking_clause_terms(negations, &conflict.literals)?;

    let kind = match terms {
        Some(terms) => classify_arith_conflict_kind(terms, &conflict.literals, Some(&farkas)),
        // No TermStore -- cannot classify Farkas conflict.
        None => TheoryLemmaKind::Generic,
    };

    match kind {
        TheoryLemmaKind::Generic => tracker.add_theory_lemma(clause),
        TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas => {
            tracker.add_theory_lemma_with_farkas_and_kind(clause, farkas, kind)
        }
        _ => tracker.add_theory_lemma_with_kind(clause, kind),
    }
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
        // Additionally, ALL conflict literals must be la_generic-eligible:
        // pure linear arithmetic inequalities without equalities or UF terms.
        // Without this check, conflicts containing `(= (f x) 10)` or `(= a b)`
        // are misclassified as LraFarkas, causing Carcara rejection.
        if conflict_all_arith_literals(terms, conflict)
            && ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                terms, conflict, farkas,
            )
            .is_ok()
        {
            return TheoryLemmaKind::LraFarkas;
        }
    }

    if arith_conflict_is_integer(terms, conflict) {
        return TheoryLemmaKind::LiaGeneric;
    }

    // Opaque-atom rescue (class 4): the conflict would otherwise fall back to
    // `Generic`/trust. If the provided certificate passes the FULL semantic
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
/// `la_generic` only accepts strict/non-strict inequality comparisons
/// (`<=`, `<`, `>=`, `>`) whose arguments are pure linear arithmetic
/// (no uninterpreted functions). Equalities (`=`) are NOT valid for
/// `la_generic` because Carcara checks that the Farkas combination
/// produces a contradictory *disequality*, and `(not (= a b))` cannot
/// participate in a linear combination. Mixed-theory terms like
/// `(>= (f x) 0)` are also invalid because `f` is uninterpreted.
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
#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

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

        assert_eq!(
            infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, Some(&farkas)),
            TheoryLemmaKind::LraFarkas
        );
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
                if core_set.len() != core_clause.len() {
                    // Duplicate literals would make the prefix check ambiguous.
                    return None;
                }
                let mut full_clause = core_clause.clone();
                for &lit in clause {
                    if !core_set.contains(&lit) {
                        full_clause.push(lit);
                    }
                }
                // Only accept when the weakened clause still covers the original
                // blocking clause exactly; otherwise the caller's fact changed.
                let full_set: HashSet<TermId> = full_clause.iter().copied().collect();
                let orig_set: HashSet<TermId> = clause.iter().copied().collect();
                if full_set != orig_set {
                    return None;
                }
                return Some((kind, core_clause, full_clause));
            }

            // Next combination of dropped indices (lexicographic).
            let mut pos = dropped;
            loop {
                if pos == 0 {
                    break;
                }
                pos -= 1;
                if drop_idx[pos] < conflict.len() - (dropped - pos) {
                    drop_idx[pos] += 1;
                    for later in pos + 1..dropped {
                        drop_idx[later] = drop_idx[later - 1] + 1;
                    }
                    break;
                }
                if pos == 0 {
                    return None;
                }
            }
            if drop_idx[0] > conflict.len() - dropped {
                break;
            }
        }
    }
    None
}
