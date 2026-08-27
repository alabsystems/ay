// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential and adversarial tests for the model-gated subset search.
//!
//! The load-bearing claim is an EQUIVALENCE, not a speedup: for every pool and
//! target, [`SubsetSearch::ModelGated`] returns exactly what
//! [`SubsetSearch::Exhaustive`] returns — the same `Some`/`None`, and when
//! `Some`, the byte-identical proof. The sweeps below decide that over
//! generated pools rather than asserting it, and each one asserts a minimum
//! ACCEPT and a minimum REJECT count so it cannot pass vacuously.
//!
//! The second family pins the property the gate rests on directly: when
//! [`blocking_clause_negation_has_verified_model`] holds for a pool, the strict
//! Farkas verifier rejects EVERY certificate over EVERY sub-multiset of it.

use super::*;
use ay_core::proof_validation::conflict_lits_satisfied_by;
use ay_core::{FarkasAnnotation, Sort, TheoryLit};
use num_bigint::BigInt;

/// A pool literal plus the assume that introduces it, as the production caller
/// builds them.
fn fact_pool(candidate: &mut Proof, atoms: &[TermId]) -> Vec<ArithmeticFact> {
    atoms
        .iter()
        .map(|&term| ArithmeticFact {
            term,
            unit: candidate.add_assume(term, None),
        })
        .collect()
}

/// `coefficient * variable + constant <= 0`, spelled the way a preprocessed
/// authored assertion is.
fn bound(terms: &mut TermStore, variable: TermId, coefficient: i64, constant: i64) -> TermId {
    let scale = terms.mk_int(BigInt::from(coefficient));
    let scaled = terms.mk_mul(vec![scale, variable]);
    let offset = terms.mk_int(BigInt::from(constant));
    let sum = terms.mk_add(vec![scaled, offset]);
    let zero = terms.mk_int(BigInt::from(0));
    terms.mk_le(sum, zero)
}

/// The atom alphabet the sweeps draw from: single- and two-variable bounds in
/// both directions, an equality, and a strict order, over `Int`.
fn alphabet(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("dsx", Sort::Int);
    let y = terms.mk_var("dsy", Sort::Int);
    let z = terms.mk_var("dsz", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let negative_y = {
        let minus_one = terms.mk_int(BigInt::from(-1));
        terms.mk_mul(vec![minus_one, y])
    };
    let x_minus_y = terms.mk_add(vec![x, negative_y]);
    let q = terms.mk_var("dsq", Sort::Int);
    vec![
        bound(terms, x, 1, -1),  //  x <= 1
        bound(terms, x, -1, -1), //  x >= 1
        bound(terms, y, 1, -4),  //  y <= 4
        bound(terms, y, -1, 0),  //  y >= 0
        bound(terms, z, -1, 2),  //  z >= 2
        terms.mk_le(x_minus_y, zero),
        terms.mk_lt(y, three),
        terms.mk_eq(x, zero),
        // The pair that makes the gate's CARDINALITY FLOOR load-bearing:
        // `1 <= 2q <= 1` is satisfied over the rationals at `q = 1/2`, so a
        // whole-pool model exists, and is refused over the integers only by
        // `recognize_lia_divisibility` — which takes at most two literals, i.e.
        // exactly the cardinality-1 clause the gate must never skip.
        bound(terms, q, -2, 1), //  2q >= 1
        bound(terms, q, 2, -1), //  2q <= 1
    ]
}

/// Run both modes on a fresh proof each and require an identical outcome.
///
/// Returns `true` when the search ACCEPTED, so a sweep can count its accepts.
fn modes_agree(terms: &mut TermStore, atoms: &[TermId], target: TermId) -> bool {
    let mut gated_proof = Proof::new();
    let gated_facts = fact_pool(&mut gated_proof, atoms);
    let gated = derive_numeric_negation(
        terms,
        &mut gated_proof,
        &gated_facts,
        target,
        SubsetSearch::ModelGated,
    );

    let mut exhaustive_proof = Proof::new();
    let exhaustive_facts = fact_pool(&mut exhaustive_proof, atoms);
    let exhaustive = derive_numeric_negation(
        terms,
        &mut exhaustive_proof,
        &exhaustive_facts,
        target,
        SubsetSearch::Exhaustive,
    );

    assert_eq!(
        gated.is_some(),
        exhaustive.is_some(),
        "gated and exhaustive searches disagreed on acceptance for target {target:?} over {atoms:?}"
    );
    assert_eq!(
        format!("{gated:?}"),
        format!("{exhaustive:?}"),
        "gated and exhaustive searches returned different step ids for {target:?}"
    );
    assert_eq!(
        format!("{:?}", gated_proof.steps),
        format!("{:?}", exhaustive_proof.steps),
        "gated and exhaustive searches built different proofs for {target:?}"
    );
    gated.is_some()
}

#[test]
fn the_gated_search_matches_the_exhaustive_one_over_every_pool_of_the_alphabet() {
    let mut terms = TermStore::new();
    let atoms = alphabet(&mut terms);
    // Targets include each atom's NEGATION, which is refuted by that atom alone
    // (cardinality 1, below the gate) and by nothing else, plus one bound that
    // is refuted only by a PAIR of pool rows (cardinality 2, above the gate).
    let mut targets: Vec<TermId> = atoms.clone();
    for &atom in &atoms {
        let negated = terms.mk_not_raw(atom);
        targets.push(negated);
    }
    let y = terms.mk_var("dsy", Sort::Int);
    targets.push(bound(&mut terms, y, -1, 5));
    let j = terms.mk_var("dsj", Sort::Int);
    let m = terms.mk_var("dsm", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let j_plus_one = terms.mk_add(vec![j, one]);
    targets.push(terms.mk_lt(m, j_plus_one));
    let mut accepts = 0_usize;
    let mut rejects = 0_usize;
    for mask in 0_u32..(1 << atoms.len()) {
        let pool: Vec<TermId> = atoms
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, &atom)| atom)
            .collect();
        if pool.len() > 3 {
            continue;
        }
        for &target in &targets {
            if modes_agree(&mut terms, &pool, target) {
                accepts += 1;
            } else {
                rejects += 1;
            }
        }
    }
    assert!(
        accepts >= 100,
        "sweep must exercise the ACCEPT path, saw {accepts}"
    );
    assert!(
        rejects >= 100,
        "sweep must exercise the REJECT path, saw {rejects}"
    );
}

#[test]
fn the_gated_search_matches_the_exhaustive_one_when_only_a_wide_subset_refutes() {
    // `x >= 1`, `y >= 0`, `x - y <= 0`, `y <= 4` is feasible; the target
    // `y >= 5` is refuted only together with `y <= 4`, so acceptance lives at a
    // cardinality the gate is responsible for skipping when it fires.
    let mut terms = TermStore::new();
    let x = terms.mk_var("wsx", Sort::Int);
    let y = terms.mk_var("wsy", Sort::Int);
    let pool = vec![
        bound(&mut terms, x, -1, 1),
        bound(&mut terms, y, -1, 0),
        bound(&mut terms, y, 1, -4),
    ];
    let target = bound(&mut terms, y, -1, 5);
    assert!(
        modes_agree(&mut terms, &pool, target),
        "the two-row refutation must be found by BOTH modes"
    );
}

#[test]
fn a_pool_with_a_verified_model_refutes_every_certificate_over_every_subset() {
    // The gate's whole claim, decided directly: take a pool the model gate
    // accepts, then try EVERY sub-multiset against the strict Farkas verifier
    // with a range of certificates, and require every one to be rejected.
    let mut terms = TermStore::new();
    let atoms = alphabet(&mut terms);
    let mut gated_pools = 0_usize;
    for mask in 1_u32..(1 << atoms.len()) {
        let pool: Vec<TermId> = atoms
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, &atom)| atom)
            .collect();
        if pool.len() > 4 {
            continue;
        }
        let clause: Vec<TermId> = pool.iter().map(|&atom| terms.mk_not_raw(atom)).collect();
        if !blocking_clause_negation_has_verified_model(&terms, &clause) {
            continue;
        }
        gated_pools += 1;
        for subset in 1_u32..(1 << clause.len()) {
            let sub: Vec<TermId> = clause
                .iter()
                .enumerate()
                .filter(|(index, _)| subset & (1 << index) != 0)
                .map(|(_, &literal)| literal)
                .collect();
            let conflict: Vec<TheoryLit> = sub
                .iter()
                .map(|&literal| match terms.get(literal) {
                    TermData::Not(inner) => TheoryLit::new(*inner, true),
                    _ => TheoryLit::new(literal, false),
                })
                .collect();
            for weights in [vec![1_i64; sub.len()], vec![2; sub.len()], {
                let mut mixed = vec![1_i64; sub.len()];
                if let Some(first) = mixed.first_mut() {
                    *first = 3;
                }
                mixed
            }] {
                let farkas = FarkasAnnotation::from_ints(&weights);
                assert!(
                    ay_core::proof_validation::verify_farkas_conflict_lits_full(
                        &terms, &conflict, &farkas
                    )
                    .is_err(),
                    "a pool with a verified model must refute every certificate; \
                     subset {sub:?} weights {weights:?} was accepted"
                );
            }
        }
    }
    assert!(
        gated_pools >= 20,
        "the sweep must find pools the gate accepts, saw {gated_pools}"
    );
}

#[test]
fn the_gate_declines_an_infeasible_pool_rather_than_claiming_a_model() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("infx", Sort::Int);
    let low = bound(&mut terms, x, -1, 5); //  x >= 5
    let high = bound(&mut terms, x, 1, -1); //  x <= 1
    let clause = vec![terms.mk_not_raw(low), terms.mk_not_raw(high)];
    assert!(
        !blocking_clause_negation_has_verified_model(&terms, &clause),
        "an infeasible pool has no model and the gate must not claim one"
    );
}

#[test]
fn a_non_arithmetic_literal_fails_the_model_check_closed() {
    let mut terms = TermStore::new();
    let flag = terms.mk_var("flag", Sort::Bool);
    let conflict = vec![TheoryLit::new(flag, true)];
    assert!(
        !conflict_lits_satisfied_by(&terms, &conflict, &|_| Some(
            num_rational::BigRational::from(BigInt::from(0))
        )),
        "a literal the verifier cannot normalize must fail closed"
    );
}

#[test]
fn an_unvalued_atom_fails_the_model_check_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("unvx", Sort::Int);
    let atom = bound(&mut terms, x, 1, -1);
    let conflict = vec![TheoryLit::new(atom, true)];
    assert!(
        !conflict_lits_satisfied_by(&terms, &conflict, &|_| None),
        "an atom with no assigned value must fail closed"
    );
}

#[test]
fn the_model_check_rejects_an_assignment_that_violates_one_row() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("vrx", Sort::Int);
    let atom = bound(&mut terms, x, 1, -1); //  x <= 1
    let conflict = vec![TheoryLit::new(atom, true)];
    let satisfying = |_: TermId| Some(num_rational::BigRational::from(BigInt::from(0)));
    let violating = |_: TermId| Some(num_rational::BigRational::from(BigInt::from(7)));
    assert!(conflict_lits_satisfied_by(&terms, &conflict, &satisfying));
    assert!(!conflict_lits_satisfied_by(&terms, &conflict, &violating));
}

#[test]
fn the_model_check_honours_the_verifiers_integer_strengthening() {
    // `x < 1` over `Int` is strengthened by the verifier to `x <= 0`, so the
    // rational point `x = 1/2` satisfies the SOURCE literal and must NOT be
    // accepted as a model of the row the verifier will combine.
    let mut terms = TermStore::new();
    let x = terms.mk_var("isx", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let atom = terms.mk_lt(x, one);
    let conflict = vec![TheoryLit::new(atom, true)];
    let half = |_: TermId| {
        Some(num_rational::BigRational::new(
            BigInt::from(1),
            BigInt::from(2),
        ))
    };
    let zero = |_: TermId| Some(num_rational::BigRational::from(BigInt::from(0)));
    assert!(
        !conflict_lits_satisfied_by(&terms, &conflict, &half),
        "a rational point may not stand in for an integer-strengthened row"
    );
    assert!(conflict_lits_satisfied_by(&terms, &conflict, &zero));
}

#[test]
fn the_model_check_reads_a_disequality_as_a_disjunction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("dqx", Sort::Int);
    let zero_term = terms.mk_int(BigInt::from(0));
    let equality = terms.mk_eq(x, zero_term);
    let conflict = vec![TheoryLit::new(equality, false)];
    let at_zero = |_: TermId| Some(num_rational::BigRational::from(BigInt::from(0)));
    let at_one = |_: TermId| Some(num_rational::BigRational::from(BigInt::from(1)));
    assert!(
        !conflict_lits_satisfied_by(&terms, &conflict, &at_zero),
        "x = 0 does not satisfy x != 0"
    );
    assert!(conflict_lits_satisfied_by(&terms, &conflict, &at_one));
}

#[test]
fn the_model_check_keeps_a_real_strict_row_strict() {
    // Over `Real` no integer strengthening applies, so `r < 0` stays a STRICT
    // row and the boundary point `r = 0` is not a model of it. Accepting the
    // boundary would let the gate skip a subset whose Farkas combination
    // genuinely contradicts on the strict inequality.
    let mut terms = TermStore::new();
    let r = terms.mk_var("rsr", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let atom = terms.mk_lt(r, zero);
    let conflict = vec![TheoryLit::new(atom, true)];
    let boundary = |_: TermId| Some(num_rational::BigRational::from(BigInt::from(0)));
    let inside = |_: TermId| Some(num_rational::BigRational::from(BigInt::from(-1)));
    assert!(
        !conflict_lits_satisfied_by(&terms, &conflict, &boundary),
        "the boundary point does not satisfy a strict row"
    );
    assert!(conflict_lits_satisfied_by(&terms, &conflict, &inside));
}

#[test]
fn the_model_check_merges_congruent_opaque_terms_before_evaluating() {
    // `f(a) - f(b) <= -1` with `a = b` is UNSAT only modulo congruence, which
    // the `full` verifier performs. A model that valued the two `f`
    // applications independently would claim a model of a pool the verifier can
    // still refute, so the check must canonicalize by the SAME closure.
    let mut terms = TermStore::new();
    let sort_int = Sort::Int;
    let a = terms.mk_var("cga", sort_int.clone());
    let b = terms.mk_var("cgb", sort_int.clone());
    let f_a = terms.mk_app(Symbol::named("cgf"), [a], sort_int.clone());
    let f_b = terms.mk_app(Symbol::named("cgf"), [b], sort_int.clone());
    let minus_one = terms.mk_int(BigInt::from(-1));
    let negated_f_b = terms.mk_mul(vec![minus_one, f_b]);
    let difference = terms.mk_add(vec![f_a, negated_f_b]);
    let gap = terms.mk_le(difference, minus_one);
    let equality = terms.mk_eq(a, b);
    let conflict = vec![TheoryLit::new(gap, true), TheoryLit::new(equality, true)];
    // An assignment that separates the two congruent applications.
    let separating = |term: TermId| {
        Some(num_rational::BigRational::from(BigInt::from(i64::from(
            term == f_b,
        ))))
    };
    assert!(
        !conflict_lits_satisfied_by(&terms, &conflict, &separating),
        "congruent applications must be merged before the rows are evaluated"
    );
}
