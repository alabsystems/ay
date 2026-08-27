// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use num_rational::Rational64;

use super::proof_farkas::{reconstruct_missing_farkas_coefficients, try_lra_farkas_reconstruction};
use super::proof_farkas_synthesis::synthesize_mixed_equality_arithmetic_farkas;
use super::proof_farkas_validation::{
    certificate_valid_for_blocking_clause, sanitize_farkas_annotations,
};
use ay_core::{Proof, ProofStep, Sort, TermStore, TheoryLemmaKind, TheoryLit};

#[test]
fn mixed_equality_recovery_handles_scaled_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);
    let equality = terms.mk_eq(two_x, y);
    let positive = terms.mk_gt(x, zero);
    let non_positive = terms.mk_le(y, zero);
    let clause = vec![
        terms.mk_not_raw(equality),
        terms.mk_not_raw(positive),
        terms.mk_not_raw(non_positive),
    ];

    let farkas = synthesize_mixed_equality_arithmetic_farkas(&mut terms, &clause)
        .expect("2*x=y, x>0, y<=0 needs a recovered equality multiplier");
    assert_eq!(
        farkas.coefficients,
        vec![
            Rational64::new(1, 2),
            Rational64::from(1),
            Rational64::new(1, 2),
        ],
        "the equality multiplier must follow its coefficient 2"
    );

    let conflict = vec![
        TheoryLit::new(equality, true),
        TheoryLit::new(positive, true),
        TheoryLit::new(non_positive, true),
    ];
    ay_core::proof_validation::verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("the recovered certificate must replay against the original rows");
}

#[test]
fn replacement_shape_certificate_is_not_authority_for_original_clause() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let equality = terms.mk_eq(x, y);
    let positive = terms.mk_gt(x, zero);
    let non_positive = terms.mk_le(y, zero);
    let candidate_clause = vec![
        terms.mk_not_raw(equality),
        terms.mk_not_raw(positive),
        terms.mk_not_raw(non_positive),
    ];
    let certificate = synthesize_mixed_equality_arithmetic_farkas(&mut terms, &candidate_clause)
        .expect("candidate replacement is a valid arithmetic contradiction");

    let true_term = terms.true_term();
    let original_clause = vec![
        terms.mk_not_raw(true_term),
        candidate_clause[1],
        candidate_clause[2],
    ];
    assert!(!certificate_valid_for_blocking_clause(
        &terms,
        &original_clause,
        &certificate,
    ));

    let mut candidate_farkas = None;
    let mut candidate_kind = TheoryLemmaKind::LiaGeneric;
    assert!(try_lra_farkas_reconstruction(
        &terms,
        &candidate_clause,
        &mut candidate_farkas,
        &mut candidate_kind,
    ));
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: original_clause.clone(),
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    reconstruct_missing_farkas_coefficients(&mut terms, &mut proof, &[equality], &[], &|| false);
    let ProofStep::TheoryLemma { farkas, clause, .. } = &proof.steps[0] else {
        panic!("expected theory lemma");
    };
    assert_eq!(clause, &original_clause);
    assert!(farkas.is_none());
}

#[test]
fn rewrite_rebinds_then_clears_collapsed_farkas_certificate() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(x, zero);
    let lower = terms.mk_ge(x, one);
    let not_upper = terms.mk_not_raw(upper);
    let not_lower = terms.mk_not_raw(lower);
    let certificate = ay_core::FarkasAnnotation::from_ints(&[1, 1]);
    assert!(certificate_valid_for_blocking_clause(
        &terms,
        &[not_upper, not_lower],
        &certificate,
    ));

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_upper, not_lower],
        farkas: Some(certificate),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let mut rewrites = DetHashMap::default();
    rewrites.insert(not_lower, not_upper);
    super::Executor::rewrite_proof_terms(&mut terms, &mut proof, &rewrites);

    let ProofStep::TheoryLemma { clause, farkas, .. } = &proof.steps[0] else {
        panic!("expected theory lemma");
    };
    assert_eq!(clause, &[not_upper]);
    assert!(farkas.is_none());
}

#[test]
fn post_rewrite_sanitation_clears_stale_existing_annotation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(x, zero);
    let lower = terms.mk_ge(x, one);
    let not_upper = terms.mk_not_raw(upper);
    let not_lower = terms.mk_not_raw(lower);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![not_upper],
        farkas: Some(ay_core::FarkasAnnotation::from_ints(&[1, 1])),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });

    sanitize_farkas_annotations(&terms, &mut proof);

    let ProofStep::TheoryLemma { farkas, .. } = &proof.steps[0] else {
        panic!("expected theory lemma");
    };
    assert!(farkas.is_none());
    assert_ne!(not_upper, not_lower);
}
