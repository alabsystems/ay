// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn exports_lra_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(num_rational::BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(num_rational::BigRational::from(BigInt::from(10)));
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x_le_5, None);
    let h1 = proof.add_assume(x_ge_10, None);
    let t2 = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_x_le_5, not_x_ge_10],
        FarkasAnnotation::from_ints(&[1, 1]),
    );
    let t3 = proof.add_resolution(vec![not_x_ge_10], x_le_5, h0, t2);
    proof.add_resolution(vec![], x_ge_10, h1, t3);

    check_proof_strict(&proof, &terms).expect("LRA proof should validate strictly");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[x_le_5, x_ge_10]);
    assert!(
        alethe.contains(":rule la_generic :args (1 1)"),
        "expected Farkas args in Alethe output:\n{alethe}"
    );
    assert_carcara_accepts("lra_bounds_gap", QF_LRA_UNSAT, &alethe);
}

#[test]
fn exports_lia_certificate_that_is_strictly_valid_and_carcara_parseable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x_le_5, None);
    let h1 = proof.add_assume(x_ge_10, None);
    let t2 = proof.add_theory_lemma_with_lia(
        "LIA",
        vec![not_x_le_5, not_x_ge_10],
        Some(FarkasAnnotation::from_ints(&[1, 1])),
        TheoryLemmaKind::LiaGeneric,
        LiaAnnotation::BoundsGap,
    );
    let t3 = proof.add_resolution(vec![not_x_ge_10], x_le_5, h0, t2);
    proof.add_resolution(vec![], x_ge_10, h1, t3);

    check_proof_strict(&proof, &terms).expect("LIA proof should validate strictly");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[x_le_5, x_ge_10]);
    assert!(
        alethe.contains(":rule la_generic :args (1 1)"),
        "expected checked la_generic promotion with Farkas args:\n{alethe}"
    );
    assert!(!alethe.contains(":rule lia_generic"), "{alethe}");
    assert_carcara_accepts("lia_bounds_gap", QF_LIA_UNSAT, &alethe);
}

#[test]
fn exports_unpromotable_lia_certificate_as_honest_carcara_hole() {
    let terms = TermStore::new();
    let mut proof = Proof::new();
    proof.add_step(ay_core::ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: Vec::new(),
        farkas: Some(FarkasAnnotation::from_ints(&[1])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });

    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[]);
    assert!(alethe.contains("(step t0 (cl) :rule hole)"), "{alethe}");
    assert!(!alethe.contains(":rule lia_generic"), "{alethe}");
    assert!(!alethe.contains(":rule la_generic"), "{alethe}");
    assert!(!alethe.contains(":args"), "{alethe}");
    assert_carcara_verdict("lia_bad_farkas_hole", QF_LIA_UNSAT, &alethe, "holey");
}
