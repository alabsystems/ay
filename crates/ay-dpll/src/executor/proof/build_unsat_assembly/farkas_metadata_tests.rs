// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_rational::Rational64;
use std::cell::Cell;

fn fixture() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("metadata_x", ay_core::Sort::Int);
    let y = terms.mk_var("metadata_y", ay_core::Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let low = terms.mk_le(x, zero);
    let high = terms.mk_ge(x, one);
    let unused = terms.mk_ge(y, zero);
    let clause = vec![
        terms.mk_not_raw(low),
        terms.mk_not_raw(high),
        terms.mk_not_raw(unused),
    ];
    (terms, clause)
}

fn leaf(clause: Vec<TermId>, farkas: Option<FarkasAnnotation>, kind: TheoryLemmaKind) -> Proof {
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "arith".to_owned(),
        clause,
        farkas,
        kind,
        lia: None,
    });
    proof
}

fn annotation(proof: &Proof) -> Option<&FarkasAnnotation> {
    let ProofStep::TheoryLemma { farkas, .. } = &proof.steps[0] else {
        unreachable!()
    };
    farkas.as_ref()
}

#[test]
fn current_whole_clause_keeps_valid_reordered_farkas_without_changing_authority() {
    let (terms, clause) = fixture();
    let source = leaf(
        clause.clone(),
        Some(FarkasAnnotation::from_ints(&[1, 1, 0])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut target = leaf(
        vec![clause[2], clause[1], clause[0]],
        None,
        TheoryLemmaKind::ArithClauseTautology,
    );
    let before = target.clone();
    assert!(ay_proof::recognize_arith_clause_tautology(&terms, &clause));
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        1
    );
    assert_eq!(
        annotation(&target).unwrap().coefficients,
        vec![
            Rational64::from_integer(0),
            Rational64::from_integer(1),
            Rational64::from_integer(1)
        ]
    );
    let ProofStep::TheoryLemma { farkas, .. } = &mut target.steps[0] else {
        unreachable!()
    };
    *farkas = None;
    assert_eq!(target, before, "only optional witness metadata may change");
}

#[test]
fn duplicate_positions_are_summed_rebound_and_independently_replayed() {
    let (terms, clause) = fixture();
    let source_clause = vec![clause[0], clause[0], clause[1], clause[2]];
    let source = leaf(
        source_clause,
        Some(FarkasAnnotation::new(vec![
            Rational64::new(1, 2),
            Rational64::new(1, 2),
            1.into(),
            0.into(),
        ])),
        TheoryLemmaKind::LraFarkas,
    );
    let target_clause = vec![clause[1], clause[0], clause[2], clause[0]];
    let mut target = leaf(
        target_clause.clone(),
        None,
        TheoryLemmaKind::ArithClauseTautology,
    );
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        1
    );
    let witness = annotation(&target).unwrap();
    assert_eq!(
        witness.coefficients,
        vec![
            Rational64::from_integer(1),
            Rational64::from_integer(1),
            Rational64::from_integer(0),
            Rational64::from_integer(0)
        ]
    );
    assert!(valid_full_annotation(
        &terms,
        &target_clause,
        witness,
        &|| false
    ));
}

#[test]
fn zero_weight_causes_and_duplicate_multiplicity_cannot_be_dropped() {
    let (terms, clause) = fixture();
    let source = leaf(
        clause.clone(),
        Some(FarkasAnnotation::from_ints(&[1, 1, 0])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut fewer = leaf(
        clause[..2].to_vec(),
        None,
        TheoryLemmaKind::ArithClauseTautology,
    );
    assert!(ay_proof::recognize_arith_clause_tautology(
        &terms,
        &clause[..2]
    ));
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut fewer, &|| false),
        0
    );
    assert!(
        annotation(&fewer).is_none(),
        "the theorem's zero-weight cause is still required"
    );
    let mut extra_duplicate = leaf(
        vec![clause[0], clause[1], clause[2], clause[2]],
        None,
        TheoryLemmaKind::ArithClauseTautology,
    );
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut extra_duplicate, &|| false),
        0
    );
    assert!(annotation(&extra_duplicate).is_none());
}

#[test]
fn absent_malformed_and_wrongly_permuted_coefficients_grant_no_metadata() {
    let (terms, clause) = fixture();
    for bad in [
        None,
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        Some(FarkasAnnotation::from_ints(&[0, 1, 1])),
        Some(FarkasAnnotation::from_ints(&[0, 0, 0])),
    ] {
        let source = leaf(clause.clone(), bad, TheoryLemmaKind::LraFarkas);
        let mut target = leaf(
            vec![clause[2], clause[1], clause[0]],
            None,
            TheoryLemmaKind::ArithClauseTautology,
        );
        let before = target.clone();
        assert_eq!(
            retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
            0
        );
        assert_eq!(target, before);
    }
}

#[test]
fn duplicate_coefficient_overflow_is_refused_without_changing_target() {
    let (terms, clause) = fixture();
    let source = leaf(
        vec![clause[0], clause[0], clause[1]],
        Some(FarkasAnnotation::from_ints(&[i64::MAX, i64::MAX, i64::MAX])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut target = leaf(
        vec![clause[1], clause[0], clause[0]],
        None,
        TheoryLemmaKind::ArithClauseTautology,
    );
    let before = target.clone();
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        0
    );
    assert_eq!(target, before);
}

#[test]
fn a_satisfiable_arithmetic_clause_cannot_acquire_farkas_authority_from_a_hint() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("satisfiable_metadata_x", ay_core::Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let lower = terms.mk_ge(x, zero);
    let upper = terms.mk_le(x, one);
    let clause = vec![terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
    // The negated clause is satisfied by x=0; its purported Farkas sum
    // leaves the feasible interval [0,1], not a contradiction.
    assert!(!ay_proof::recognize_arith_clause_tautology(&terms, &clause));
    let source = leaf(
        clause.clone(),
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut target = leaf(clause, None, TheoryLemmaKind::ArithClauseTautology);
    let before = target.clone();
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        0
    );
    assert_eq!(
        target, before,
        "hint metadata never creates theorem authority"
    );
}

#[test]
fn a_stopped_shared_assembly_cannot_copy_or_refund_metadata_work() {
    let (terms, clause) = fixture();
    let source = leaf(
        clause.clone(),
        Some(FarkasAnnotation::from_ints(&[1, 1, 0])),
        TheoryLemmaKind::LraFarkas,
    );
    for allowance in [0usize, 1, 4, 10] {
        let mut target = leaf(clause.clone(), None, TheoryLemmaKind::ArithClauseTautology);
        let before = target.clone();
        let spent = Cell::new(0usize);
        let stopped = || {
            let n = spent.get();
            spent.set(n + 1);
            n >= allowance
        };
        assert_eq!(
            retain_verified_farkas_annotations(&terms, &source, &mut target, &stopped),
            0
        );
        let after_first = spent.get();
        assert!(after_first > allowance);
        assert_eq!(
            retain_verified_farkas_annotations(&terms, &source, &mut target, &stopped),
            0
        );
        assert!(
            spent.get() > after_first,
            "the same owner remains spent on retry"
        );
        assert_eq!(target, before);
    }
}

#[test]
fn an_invalid_hint_cannot_shadow_a_later_independently_valid_witness() {
    let (terms, clause) = fixture();
    let mut source = leaf(
        clause.clone(),
        Some(FarkasAnnotation::from_ints(&[0, 1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    source.add_step(ProofStep::TheoryLemma {
        theory: "arith".to_owned(),
        clause: clause.clone(),
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1, 0])),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let mut target = leaf(clause, None, TheoryLemmaKind::ArithClauseTautology);
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        1
    );
    assert_eq!(
        annotation(&target).unwrap().coefficients,
        vec![
            Rational64::from_integer(1),
            Rational64::from_integer(1),
            Rational64::from_integer(0)
        ]
    );
}

#[test]
fn refused_rebind_reservation_cannot_copy_coefficients_or_refill_the_owner() {
    let (_, clause) = fixture();
    let weights = FarkasAnnotation::from_ints(&[1, 1, 0]);
    let calls = Cell::new(0usize);
    let denied = Cell::new(false);
    let stopped = || {
        let next = calls.get() + 1;
        calls.set(next);
        // Denominators are visited first; the next debit belongs to the
        // target coefficient buffer and is denied before try_reserve_exact.
        denied.set(denied.get() || next > weights.coefficients.len());
        denied.get()
    };
    assert!(rebind_fallible(&clause, &clause, &weights, &stopped).is_none());
    assert_eq!(calls.get(), weights.coefficients.len() + 1);
    assert!(rebind_fallible(&clause, &clause, &weights, &stopped).is_none());
    assert_eq!(calls.get(), weights.coefficients.len() + 2);
    assert!(denied.get());
}

#[test]
fn assembly_owned_verifier_denies_shared_dag_visits_without_a_private_grant() {
    let mut terms = TermStore::new();
    let mut expression = terms.mk_var("assembly_shared_dag", ay_core::Sort::Int);
    for _ in 0..32 {
        let previous = expression;
        expression = terms.mk_app(
            ay_core::Symbol::named("+"),
            [previous, previous],
            ay_core::Sort::Int,
        );
    }
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let low = terms.mk_le(expression, zero);
    let high = terms.mk_ge(expression, one);
    let clause = [terms.mk_not_raw(low), terms.mk_not_raw(high)];
    let annotation = FarkasAnnotation::from_ints(&[1, 1]);
    let work = Cell::new(0usize);
    let stopped = || {
        let next = work.get() + 1;
        work.set(next);
        next > 4096
    };
    assert!(!valid_full_annotation(
        &terms,
        &clause,
        &annotation,
        &stopped
    ));
    assert_eq!(
        work.get(),
        4097,
        "scratch and traversal use the enclosing count"
    );
    assert!(!valid_full_annotation(
        &terms,
        &clause,
        &annotation,
        &stopped
    ));
    assert_eq!(work.get(), 4098, "no retry opens another verifier grant");
}

fn congruence_fixture() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("retained_congruence_a", ay_core::Sort::Int);
    let b = terms.mk_var("retained_congruence_b", ay_core::Sort::Int);
    let fa = terms.mk_app(
        ay_core::Symbol::named("retained_f"),
        [a],
        ay_core::Sort::Int,
    );
    let fb = terms.mk_app(
        ay_core::Symbol::named("retained_f"),
        [b],
        ay_core::Sort::Int,
    );
    let equality = terms.mk_app(ay_core::Symbol::named("="), [a, b], ay_core::Sort::Bool);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let low = terms.mk_le(fa, zero);
    let high = terms.mk_ge(fb, one);
    let clause = vec![
        terms.mk_not_raw(equality),
        terms.mk_not_raw(low),
        terms.mk_not_raw(high),
    ];
    (terms, clause)
}

#[test]
fn full_congruence_witness_rebinds_the_exact_whole_clause_without_changing_native_kind() {
    let (terms, clause) = congruence_fixture();
    let weights = FarkasAnnotation::from_ints(&[0, 1, 1]);
    let conflict = clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => unreachable!(),
        })
        .collect::<Vec<_>>();
    assert!(
        ay_core::proof_validation::verify_farkas_conflict_lits_full_holds(
            &terms, &conflict, &weights
        )
    );
    assert!(
        !ay_core::proof_validation::verify_farkas_conflict_lits_linear_holds(
            &terms, &conflict, &weights
        )
    );
    let source = leaf(clause.clone(), Some(weights), TheoryLemmaKind::LraFarkas);
    let mut target = leaf(
        vec![clause[2], clause[0], clause[1]],
        None,
        TheoryLemmaKind::ArithClauseTautology,
    );
    let before = target.clone();
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        1
    );
    let retained = annotation(&target).unwrap();
    assert_eq!(
        retained.coefficients,
        FarkasAnnotation::from_ints(&[1, 0, 1]).coefficients
    );
    assert!(valid_full_annotation(
        &terms,
        &[clause[2], clause[0], clause[1]],
        retained,
        &|| false
    ));
    let ProofStep::TheoryLemma { farkas, .. } = &mut target.steps[0] else {
        unreachable!()
    };
    *farkas = None;
    assert_eq!(
        target, before,
        "no theorem kind, clause, or authority is rewritten"
    );
}

#[test]
fn congruence_retention_refuses_a_false_support_and_shared_owner_exhaustion() {
    let (terms, clause) = congruence_fixture();
    // Flip the asserted equality into a disequality. The bounds now have the
    // model a=0,b=1,f(a)=0,f(b)=1, so the old positive witness cannot be reused.
    let TermData::Not(equality) = terms.get(clause[0]) else {
        unreachable!()
    };
    let false_clause = vec![*equality, clause[1], clause[2]];
    let source = leaf(
        false_clause.clone(),
        Some(FarkasAnnotation::from_ints(&[0, 1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut target = leaf(false_clause, None, TheoryLemmaKind::ArithClauseTautology);
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        0
    );
    assert!(annotation(&target).is_none());
    // Real closure work shares the assembly owner. A spent owner cannot
    // publish even an otherwise valid FULL-only optional annotation.
    let source = leaf(
        clause.clone(),
        Some(FarkasAnnotation::from_ints(&[0, 1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut target = leaf(clause, None, TheoryLemmaKind::ArithClauseTautology);
    let before = target.clone();
    let visits = Cell::new(0usize);
    let stopped = || {
        visits.set(visits.get() + 1);
        visits.get() > 64
    };
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &stopped),
        0
    );
    assert_eq!(target, before);
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &stopped),
        0
    );
    assert_eq!(target, before);
    assert!(visits.get() > 64);
}

fn constructive_long_fixture() -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let mut clause = Vec::new();
    let mut summands = Vec::new();
    for index in 1..=11 {
        let variable = terms.mk_var(format!("retained_derived_{index}"), ay_core::Sort::Int);
        let weight = terms.mk_int(index.into());
        summands.push(terms.mk_app(
            ay_core::Symbol::named("*"),
            [weight, variable],
            ay_core::Sort::Int,
        ));
        let eq = terms.mk_app(
            ay_core::Symbol::named("="),
            [variable, zero],
            ay_core::Sort::Bool,
        );
        clause.push(terms.mk_not_raw(eq));
    }
    let sum = terms.mk_app(ay_core::Symbol::named("+"), summands, ay_core::Sort::Int);
    let disequality = terms.mk_app(
        ay_core::Symbol::named("distinct"),
        [sum, zero],
        ay_core::Sort::Bool,
    );
    clause.push(terms.mk_not_raw(disequality));
    (terms, clause)
}

#[test]
fn retention_derives_real_nonunit_positional_witness_without_relaxing_strict_search() {
    let (terms, clause) = constructive_long_fixture();
    let mut target_clause = clause.clone();
    target_clause.reverse();
    let mut target = leaf(
        target_clause.clone(),
        None,
        TheoryLemmaKind::ArithClauseTautology,
    );
    let before = target.clone();
    // The constructive path remains behind exact current-source hint ingress.
    // Missing/malformed payloads do not become provenance permission.
    for hint in [None, Some(FarkasAnnotation::from_ints(&[1; 11]))] {
        let source = leaf(clause.clone(), hint, TheoryLemmaKind::LraFarkas);
        assert_eq!(
            retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
            0
        );
        assert_eq!(target, before);
    }
    let unit = FarkasAnnotation::from_ints(&[1; 12]);
    assert!(!valid_full_annotation(
        &terms,
        &target_clause,
        &unit,
        &|| false
    ));
    let source = leaf(clause, Some(unit), TheoryLemmaKind::LraFarkas);
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        1
    );
    let derived = annotation(&target).unwrap();
    assert_eq!(
        derived.coefficients,
        FarkasAnnotation::from_ints(&[1, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]).coefficients
    );
    assert!(
        !valid_full_annotation(&terms, &target_clause, derived, &|| false),
        "the old capped verifier has NOT been broadened"
    );
    let ProofStep::TheoryLemma { farkas, .. } = &mut target.steps[0] else {
        unreachable!()
    };
    *farkas = None;
    assert_eq!(
        target, before,
        "only independently replayed metadata may be installed"
    );
}

#[test]
fn constructive_retention_refuses_sat_support_and_a_spent_assembly_owner() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("constructive_sat_x", ay_core::Sort::Int);
    let y = terms.mk_var("constructive_sat_y", ay_core::Sort::Int);
    let zero = terms.mk_int(0.into());
    let equality = terms.mk_app(ay_core::Symbol::named("="), [x, zero], ay_core::Sort::Bool);
    let disequality = terms.mk_app(
        ay_core::Symbol::named("distinct"),
        [y, zero],
        ay_core::Sort::Bool,
    );
    let clause = vec![terms.mk_not_raw(equality), terms.mk_not_raw(disequality)];
    // x=0,y=1 is a concrete model; a matching hint is never authority.
    let source = leaf(
        clause.clone(),
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LraFarkas,
    );
    let mut target = leaf(clause, None, TheoryLemmaKind::ArithClauseTautology);
    let before = target.clone();
    assert_eq!(
        retain_verified_farkas_annotations(&terms, &source, &mut target, &|| false),
        0
    );
    assert_eq!(target, before);
    let (terms, clause) = constructive_long_fixture();
    let visits = Cell::new(0usize);
    let stopped = || {
        visits.set(visits.get() + 1);
        visits.get() > 64
    };
    assert!(derive_current_affine_annotation(&terms, &clause, &stopped).is_none());
    assert_eq!(visits.get(), 65);
    assert!(derive_current_affine_annotation(&terms, &clause, &stopped).is_none());
    assert_eq!(
        visits.get(),
        66,
        "another attempt cannot open a new local allowance"
    );
}
