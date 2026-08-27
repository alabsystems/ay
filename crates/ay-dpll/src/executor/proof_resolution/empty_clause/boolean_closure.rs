// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive the empty clause through the BOOLEAN structure of a wide
//! disjunction leaf, instead of asserting the trust closer's head.
//!
//! # Why this exists (#4751)
//!
//! [`super::derive_empty_via_trust_lemma`] is the last resort: it asserts one
//! head clause — the negation of every leaf the proof carries — and resolves
//! the leaves away against it. The head is an unproved claim, so the strict
//! checker rejects it (`TheoryLemmaKind::Generic`).
//!
//! On the #4751 route those heads are NOT arithmetic tautologies, and the
//! campaign measured that directly: their arithmetic rows are all LOWER
//! bounds, satisfied at `B = C = D = 0`, so no cutting-plane or lattice rule
//! of any rank can close them. Their validity rests on ONE Boolean literal —
//! a wide `(or D1 .. Dn)` leaf. That is a derivation the closer can build:
//! decompose the disjunction with the Alethe `or` rule and refute every
//! disjunct against the OTHER leaves, then resolve.
//!
//! # What makes this sound
//!
//! Nothing here is asserted. Every emitted step is re-validated from scratch
//! by the untouched strict checker:
//!
//! * the `or` decomposition is Alethe `or` over an existing leaf, checked by
//!   `validate_or_clausification`;
//! * a `false` disjunct is discharged by Alethe `false` — `(cl (not false))` —
//!   checked by the bounded-semantics evaluator;
//! * a negated-equality disjunct is discharged by an `ArithEqTriangle` theory
//!   lemma, whose clause is offered to the CHECKER'S OWN
//!   [`ay_proof::recognize_arith_eq_triangle`] before it is committed, so the
//!   producer and the validator cannot drift;
//! * an arithmetic disjunct is discharged by a Farkas conflict returned by a
//!   fresh [`ay_lra::LraSolver`], carrying the certificate the strict checker
//!   re-verifies;
//! * every remaining step is an exact binary resolution against a leaf that is
//!   ALREADY in the proof — no `assume` is injected.
//!
//! A refutation that cannot be built this way leaves the proof untouched and
//! the trust closer runs exactly as before (fail-closed). This never converts
//! a rescuable `Generic` rejection into a hard `InvalidTheoryLemma` one,
//! because it emits no kind whose validator it has not already run.
//!
//! # `GUARD_MUTATION_LEDGER`
//!
//! Each guard was DELETED, the named test observed failing, and the guard
//! restored. Two entries are classified honestly as defensive rather than
//! soundness-critical, with the reason, because deleting them alone failed
//! nothing:
//!
//! | guard | mutation | observed |
//! |---|---|---|
//! | the `Admission::Complement` arm | deleted | 5 of 10 tests FAIL |
//! | disjunct de-duplication (`distinct`) | `distinct = disjuncts` | `a_wide_disjunction_closes_by_derivation_and_the_strict_checker_accepts_it` FAILS — the strict checker rejects the no-op resolution, exactly `#trust-lemma-dup-assume` |
//! | [`MAX_DISJUNCTS`] | deleted | `a_disjunction_wider_than_the_cap_declines_rather_than_truncating` FAILS |
//! | the leaf-citation PAIR — [`find_le_leaf`] AND `discharge_to_unit`'s `units.get(&atom)?` | both replaced by fabricating the term / premise | `a_half_bounded_equality_declines_and_leaves_the_proof_untouched` FAILS. Each ALONE fails nothing: they are redundant, and the pair is what enforces "every resolved literal cites an existing leaf". Recorded as a pair rather than claimed as two guards. |
//! | the complement-polarity check in `close_with` | deleted | NO test fails. DEFENSIVE, and unreachable by construction: the LRA is asked for a conflict with the disjunct asserted at its OWN polarity, so negating the reported literal always yields the complement. A violation would still fail closed twice over — at `discharge_to_unit`'s `[complement]` match, and at the strict checker. |

mod recognition;

use recognition::*;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{
    AletheRule, Constant, FarkasAnnotation, Proof, ProofId, ProofStep, TermId, TermStore,
    TheoryLemmaKind, TheoryResult, TheorySolver,
};

/// Widest disjunction this closer will attempt.
///
/// A cap rather than a truncation: a wider `or` is DECLINED outright, so
/// acceptance never depends on disjunct order. #4751's heads carry 31-51
/// disjuncts; the bound leaves room without licensing an unbounded number of
/// fresh LRA solves inside a latency-sensitive closer.
const MAX_DISJUNCTS: usize = 128;

/// How one disjunct is discharged.
enum Justification {
    /// The disjunct's exact complement is ALREADY a leaf of this proof, so the
    /// disjunct resolves away against it with no lemma at all. This is the
    /// purely Boolean arm and it needs no theory reasoning whatsoever.
    Leaf(ProofId),
    /// Alethe `false`: `(cl (not false))`.
    FalseRule,
    /// `ArithEqTriangle`: `(cl (not (<= a b)) (not (<= b a)) (= a b))`.
    EqTriangle,
    /// An LRA conflict's Farkas certificate.
    Farkas(Box<FarkasAnnotation>),
}

/// One disjunct together with the clause that eliminates it.
///
/// `clause` always contains the exact complement of `disjunct`; every OTHER
/// literal is the negation of a leaf listed in `unit_proof`, so the chain can
/// resolve it down to the unit `[complement(disjunct)]`.
struct Refutation {
    disjunct: TermId,
    clause: Vec<TermId>,
    justification: Justification,
}

/// Structural admissibility of one disjunct, decided WITHOUT running a solver.
///
/// Ordering matters for cost, not for soundness: an `or` carrying a disjunct
/// no arm can discharge is rejected here, before any LRA solve is spent on its
/// siblings, and the cheapest arm that applies is chosen first.
enum Admission {
    Complement { leaf: TermId, unit: ProofId },
    False,
    Equality,
    Arithmetic,
}

fn admit(
    terms: &TermStore,
    units: &HashMap<TermId, ProofId>,
    disjunct: TermId,
) -> Option<Admission> {
    // A disjunct the proof already refutes literally needs no lemma. It is
    // also the case a fresh LRA solve does NOT cover: measured on #4751, a
    // conflict between a bound atom and its own negation comes back without a
    // Farkas certificate, because there is no linear combination to report.
    if let Some((leaf, unit)) = find_complement_leaf(terms, units, disjunct) {
        return Some(Admission::Complement { leaf, unit });
    }
    if matches!(terms.get(disjunct), TermData::Const(Constant::Bool(false))) {
        return Some(Admission::False);
    }
    if decode_negated_arith_equality(terms, disjunct).is_some() {
        return Some(Admission::Equality);
    }
    if arith_inequality(terms, disjunct) {
        return Some(Admission::Arithmetic);
    }
    None
}

/// Refute one negated-equality disjunct with the checker's own triangle rule.
fn refute_equality(
    terms: &mut TermStore,
    units: &HashMap<TermId, ProofId>,
    disjunct: TermId,
) -> Option<Refutation> {
    let (eq, lhs, rhs) = decode_negated_arith_equality(terms, disjunct)?;
    // Both bounds must ALREADY be leaves: the triangle turns `a <= b` and
    // `b <= a` into `a = b`, and a bound this proof does not carry cannot be
    // resolved away later.
    let forward = find_le_leaf(terms, units, lhs, rhs)?;
    let reverse = find_le_leaf(terms, units, rhs, lhs)?;
    let not_forward = terms.mk_not_raw(forward);
    let not_reverse = terms.mk_not_raw(reverse);
    let clause = vec![not_forward, not_reverse, eq];
    // Gate on the CHECKER'S recognizer, which is its validator run on exactly
    // the clause about to be recorded.
    if !ay_proof::recognize_arith_eq_triangle(terms, &clause) {
        return None;
    }
    Some(Refutation {
        disjunct,
        clause,
        justification: Justification::EqTriangle,
    })
}

/// Refute one arithmetic disjunct against the bound leaves with a fresh LRA
/// solve, keeping the certificate the strict checker re-verifies.
fn refute_arithmetic(
    terms: &mut TermStore,
    units: &HashMap<TermId, ProofId>,
    bounds: &[TermId],
    disjunct: TermId,
) -> Option<Refutation> {
    let (disjunct_atom, disjunct_value) = match terms.get(disjunct) {
        TermData::Not(inner) => (*inner, false),
        _ => (disjunct, true),
    };
    let conflict = {
        let mut lra = ay_lra::LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        TheorySolver::register_atom(&mut lra, disjunct_atom);
        for &bound in bounds {
            TheorySolver::register_atom(&mut lra, atom_of(terms, bound));
        }
        TheorySolver::assert_literal(&mut lra, disjunct_atom, disjunct_value);
        for &bound in bounds {
            let (atom, value) = match terms.get(bound) {
                TermData::Not(inner) => (*inner, false),
                _ => (bound, true),
            };
            TheorySolver::assert_literal(&mut lra, atom, value);
        }
        let TheoryResult::UnsatWithFarkas(conflict) = TheorySolver::check(&mut lra) else {
            return None;
        };
        conflict
    };
    let farkas = conflict.farkas?;
    if conflict.literals.is_empty() || farkas.coefficients.len() != conflict.literals.len() {
        return None;
    }
    // The conflict must name THIS disjunct, or it does not license removing it
    // from the `or` decomposition.
    if !conflict
        .literals
        .iter()
        .any(|lit| lit.term == disjunct_atom)
    {
        return None;
    }
    let mut clause = Vec::with_capacity(conflict.literals.len());
    for lit in &conflict.literals {
        let negated = if lit.value {
            terms.mk_not_raw(lit.term)
        } else {
            lit.term
        };
        clause.push(negated);
    }
    // Every literal other than the disjunct's complement has to be resolvable
    // against an existing leaf.
    for &lit in &clause {
        if atom_of(terms, lit) == disjunct_atom {
            continue;
        }
        if !units.contains_key(&atom_of(terms, lit)) {
            return None;
        }
    }
    Some(Refutation {
        disjunct,
        clause,
        justification: Justification::Farkas(Box::new(farkas)),
    })
}

/// Refute one `false` disjunct with Alethe's own `false` rule.
fn refute_false(terms: &mut TermStore, disjunct: TermId) -> Refutation {
    let not_false = terms.mk_not_raw(disjunct);
    Refutation {
        disjunct,
        clause: vec![not_false],
        justification: Justification::FalseRule,
    }
}

/// Build a refutation for every distinct disjunct, or decline.
fn refute_all(
    terms: &mut TermStore,
    distinct: &[TermId],
    units: &HashMap<TermId, ProofId>,
    or_term: TermId,
) -> Option<Vec<Refutation>> {
    // Structural pass first: an inadmissible disjunct declines the whole
    // candidate before a single solver is constructed.
    let admissions: Vec<Admission> = distinct
        .iter()
        .map(|&disjunct| admit(terms, units, disjunct))
        .collect::<Option<Vec<_>>>()?;

    let bounds: Vec<TermId> = units
        .keys()
        .copied()
        .filter(|&leaf| leaf != or_term && arith_inequality(terms, leaf))
        .collect();
    // Deterministic rows: `units` is a hash map, and the Farkas certificate is
    // positional, so an unsorted bound list would make the emitted clause (and
    // therefore the proof) depend on hash order.
    let mut bounds = bounds;
    bounds.sort_unstable();

    let mut refutations = Vec::with_capacity(distinct.len());
    for (&disjunct, admission) in distinct.iter().zip(admissions.iter()) {
        let refutation = match admission {
            Admission::Complement { leaf, unit } => Refutation {
                disjunct,
                clause: vec![*leaf],
                justification: Justification::Leaf(*unit),
            },
            Admission::False => refute_false(terms, disjunct),
            Admission::Equality => refute_equality(terms, units, disjunct)?,
            Admission::Arithmetic => refute_arithmetic(terms, units, &bounds, disjunct)?,
        };
        refutations.push(refutation);
    }
    Some(refutations)
}

/// Record one refutation's justifying step.
fn emit_justification(proof: &mut Proof, refutation: &Refutation) -> ProofId {
    match &refutation.justification {
        // The leaf IS the justification; `discharge_to_unit` short-circuits
        // before reaching here, and this arm keeps that fact total.
        Justification::Leaf(unit) => *unit,
        Justification::FalseRule => proof.add_rule_step(
            AletheRule::False,
            refutation.clause.clone(),
            Vec::new(),
            Vec::new(),
        ),
        Justification::EqTriangle => proof.add_theory_lemma_with_kind(
            "LIA",
            refutation.clause.clone(),
            TheoryLemmaKind::ArithEqTriangle,
        ),
        Justification::Farkas(farkas) => proof.add_step(ProofStep::TheoryLemma {
            theory: String::from("LRA"),
            clause: refutation.clause.clone(),
            farkas: Some((**farkas).clone()),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        }),
    }
}

/// Resolve one refutation down to the unit `[complement(disjunct)]`.
fn discharge_to_unit(
    terms: &TermStore,
    proof: &mut Proof,
    units: &HashMap<TermId, ProofId>,
    refutation: &Refutation,
) -> Option<(ProofId, TermId)> {
    // The Boolean arm is already a unit: the leaf itself. Emitting anything
    // for it would only restate a step the proof carries.
    if let Justification::Leaf(unit) = refutation.justification {
        return match refutation.clause.as_slice() {
            [complement] => Some((unit, *complement)),
            _ => None,
        };
    }
    let disjunct_atom = atom_of(terms, refutation.disjunct);
    let mut clause = refutation.clause.clone();
    let mut current = emit_justification(proof, refutation);

    let bound_literals: Vec<TermId> = clause
        .iter()
        .copied()
        .filter(|&lit| atom_of(terms, lit) != disjunct_atom)
        .collect();
    for literal in bound_literals {
        let atom = atom_of(terms, literal);
        let unit = *units.get(&atom)?;
        let resolvent: Vec<TermId> = clause.iter().copied().filter(|&l| l != literal).collect();
        current = proof.add_resolution(resolvent.clone(), atom, current, unit);
        clause = resolvent;
    }
    match clause.as_slice() {
        [complement] => Some((current, *complement)),
        _ => None,
    }
}

/// Try to close the proof through the Boolean structure of a disjunction leaf.
///
/// Returns `true` only when the emitted chain reaches the empty clause.
pub(crate) fn try_derive_empty_via_boolean_disjunction(
    terms: &mut TermStore,
    proof: &mut Proof,
) -> bool {
    let leaves = collect_leaves(proof);
    if leaves.is_empty() {
        return false;
    }
    let mut units: HashMap<TermId, ProofId> = HashMap::default();
    for &(id, term) in &leaves {
        units.entry(term).or_insert(id);
    }

    for &(or_id, or_term) in &leaves {
        let Some(disjuncts) = decode_or(terms, or_term) else {
            continue;
        };
        if disjuncts.len() > MAX_DISJUNCTS {
            continue;
        }
        // The `or` term's children repeat on this route; resolution is decided
        // set-wise, so one resolution per DISTINCT disjunct is exact, while a
        // second one on an already-eliminated literal would not be a
        // resolution at all (#trust-lemma-dup-assume).
        let mut distinct: Vec<TermId> = Vec::with_capacity(disjuncts.len());
        for &disjunct in &disjuncts {
            if !distinct.contains(&disjunct) {
                distinct.push(disjunct);
            }
        }
        let Some(refutations) = refute_all(terms, &distinct, &units, or_term) else {
            continue;
        };
        // Emit into the proof only as far as the chain gets, and REWIND on a
        // short chain: a partial derivation is sound but unused, and leaving
        // it behind would hand the trust closer a proof it did not build.
        let committed = proof.steps.len();
        if close_with(
            terms,
            proof,
            or_id,
            &disjuncts,
            &distinct,
            &refutations,
            &units,
        ) {
            return true;
        }
        proof.steps.truncate(committed);
    }
    false
}

/// Emit the `or` decomposition and resolve every disjunct away.
fn close_with(
    terms: &TermStore,
    proof: &mut Proof,
    or_id: ProofId,
    disjuncts: &[TermId],
    distinct: &[TermId],
    refutations: &[Refutation],
    units: &HashMap<TermId, ProofId>,
) -> bool {
    // `validate_or_clausification` matches the conclusion against the `or`
    // children with multiplicity, so the decomposition keeps the duplicates.
    let mut current =
        proof.add_rule_step(AletheRule::Or, disjuncts.to_vec(), vec![or_id], Vec::new());
    let mut clause: Vec<TermId> = distinct.to_vec();

    for refutation in refutations {
        let Some((unit_id, complement)) = discharge_to_unit(terms, proof, units, refutation) else {
            return false;
        };
        // The refutation must have collapsed to the EXACT complement of the
        // disjunct, or the resolution below is not one.
        let expects = atom_of(terms, refutation.disjunct) == atom_of(terms, complement)
            && complement != refutation.disjunct;
        if !expects {
            return false;
        }
        let resolvent: Vec<TermId> = clause
            .iter()
            .copied()
            .filter(|&l| l != refutation.disjunct)
            .collect();
        current = proof.add_resolution(
            resolvent.clone(),
            atom_of(terms, refutation.disjunct),
            current,
            unit_id,
        );
        clause = resolvent;
    }

    clause.is_empty()
}
