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
fn exports_negated_equality_literal_as_a_carcara_equality_row() {
    const PROBLEM: &str = r#"
(set-logic QF_LRA)
(declare-const equality_row_x Real)
(assert (= equality_row_x 0.0))
(assert (not (<= equality_row_x 0.0)))
(check-sat)
"#;

    let mut terms = TermStore::new();
    let x = terms.mk_var("equality_row_x", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let equality = terms.mk_app(ay_core::Symbol::named("="), [x, zero], Sort::Bool);
    let upper = terms.mk_app(ay_core::Symbol::named("<="), [x, zero], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_upper = terms.mk_not_raw(upper);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(equality, None);
    let h1 = proof.add_assume(not_upper, None);
    let farkas = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_equality, upper],
        FarkasAnnotation::from_ints(&[1, 1]),
    );
    let upper_unit = proof.add_resolution(vec![upper], equality, h0, farkas);
    proof.add_resolution(Vec::new(), upper, h1, upper_unit);

    check_proof_strict(&proof, &terms).expect("equality-row Farkas proof validates strictly");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[equality, not_upper]);
    assert!(alethe.contains(":rule la_generic :args (-1 1)"), "{alethe}");
    assert_carcara_accepts("lra_negated_equality_row", PROBLEM, &alethe);
}

#[test]
fn exports_symbolic_linear_identity_as_poly_simp_not_la_generic() {
    const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const linear_identity_x Int)
(assert (not (= (+ linear_identity_x 0) linear_identity_x)))
(check-sat)
"#;

    let mut terms = TermStore::new();
    let x = terms.mk_var("linear_identity_x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let sum = terms.mk_app(ay_core::Symbol::named("+"), [x, zero], Sort::Int);
    let identity = terms.mk_app(ay_core::Symbol::named("="), [sum, x], Sort::Bool);
    let not_identity = terms.mk_not_raw(identity);

    let mut proof = Proof::new();
    let assumed_disequality = proof.add_assume(not_identity, None);
    let identity_lemma = proof.add_theory_lemma_with_lia(
        "LIA",
        vec![identity],
        Some(FarkasAnnotation::from_ints(&[1])),
        TheoryLemmaKind::LiaGeneric,
        LiaAnnotation::LinearIdentity,
    );
    proof.add_resolution(Vec::new(), identity, assumed_disequality, identity_lemma);

    check_proof_strict(&proof, &terms).expect("symbolic linear identity validates strictly");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[not_identity]);
    assert!(alethe.contains(":rule poly_simp"), "{alethe}");
    assert!(!alethe.contains(":rule la_generic"), "{alethe}");
    assert!(!alethe.contains(":rule hole"), "{alethe}");
    assert_carcara_accepts("lia_symbolic_linear_identity_poly_simp", PROBLEM, &alethe);

    let old_la_generic =
        alethe.replacen(":rule poly_simp", ":rule la_generic :args (1)", 1);
    assert_carcara_verdict(
        "lia_symbolic_linear_identity_old_la_generic",
        PROBLEM,
        &old_la_generic,
        "invalid",
    );
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

#[test]
fn computed_farkas_coefficient_is_holey_and_old_wire_claim_is_carcara_invalid() {
    const PROBLEM: &str = r#"
(set-logic QF_NIA)
(declare-const computed_coefficient_x Int)
(assert (<= computed_coefficient_x 0))
(assert (not (<= (* (+ 1 1) computed_coefficient_x) 0)))
(check-sat)
"#;

    let mut terms = TermStore::new();
    let x = terms.mk_var("computed_coefficient_x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let computed_two = terms.mk_app(ay_core::Symbol::named("+"), [one, one], Sort::Int);
    let product = terms.mk_app(ay_core::Symbol::named("*"), [computed_two, x], Sort::Int);
    let fact = terms.mk_app(ay_core::Symbol::named("<="), [x, zero], Sort::Bool);
    let target = terms.mk_app(ay_core::Symbol::named("<="), [product, zero], Sort::Bool);
    let not_fact = terms.mk_not_raw(fact);
    let not_target = terms.mk_not_raw(target);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(fact, None);
    let h1 = proof.add_assume(not_target, None);
    let farkas = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_fact, target],
        FarkasAnnotation::from_ints(&[2, 1]),
    );
    let target_unit = proof.add_resolution(vec![target], fact, h0, farkas);
    proof.add_resolution(Vec::new(), target, h1, target_unit);

    check_proof_strict(&proof, &terms)
        .expect("AY's broader internal linearizer accepts the exact certificate");
    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[fact, not_target]);
    assert!(alethe.contains(":rule hole"), "{alethe}");
    assert!(!alethe.contains(":rule la_generic"), "{alethe}");
    assert_carcara_verdict(
        "computed_farkas_coefficient_hole",
        PROBLEM,
        &alethe,
        "holey",
    );

    let old_wire_claim = alethe.replacen(":rule hole", ":rule la_generic :args (2 1)", 1);
    assert_carcara_verdict(
        "computed_farkas_coefficient_old_wire_claim",
        PROBLEM,
        &old_wire_claim,
        "invalid",
    );
}

#[test]
fn pinned_carcara_accepts_a_shared_opaque_nonlinear_product() {
    const PROBLEM: &str = r#"
(set-logic QF_NIA)
(declare-const sum Int)
(declare-const i Int)
(declare-const sq Int)
(assert (= (+ (* 2 sum) i) sq))
(assert (= sq (* i i)))
(assert (not (<= (+ (* sum 2) (* i 3) 1) (+ (* i 2) (* i i) 1))))
(check-sat)
"#;

    let mut terms = TermStore::new();
    let sum = terms.mk_var("sum", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let sq = terms.mk_var("sq", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    let two_sum = terms.mk_app(ay_core::Symbol::named("*"), [two, sum], Sort::Int);
    let eq1_lhs = terms.mk_app(ay_core::Symbol::named("+"), [two_sum, i], Sort::Int);
    let eq1 = terms.mk_app(ay_core::Symbol::named("="), [eq1_lhs, sq], Sort::Bool);
    let i_squared = terms.mk_app(ay_core::Symbol::named("*"), [i, i], Sort::Int);
    let eq2 = terms.mk_app(ay_core::Symbol::named("="), [sq, i_squared], Sort::Bool);

    let sum_two = terms.mk_app(ay_core::Symbol::named("*"), [sum, two], Sort::Int);
    let i_three = terms.mk_app(ay_core::Symbol::named("*"), [i, three], Sort::Int);
    let bound_lhs =
        terms.mk_app(ay_core::Symbol::named("+"), [sum_two, i_three, one], Sort::Int);
    let i_two = terms.mk_app(ay_core::Symbol::named("*"), [i, two], Sort::Int);
    let bound_rhs =
        terms.mk_app(ay_core::Symbol::named("+"), [i_two, i_squared, one], Sort::Int);
    let bound =
        terms.mk_app(ay_core::Symbol::named("<="), [bound_lhs, bound_rhs], Sort::Bool);
    let not_eq1 = terms.mk_not_raw(eq1);
    let not_eq2 = terms.mk_not_raw(eq2);
    let not_bound = terms.mk_not_raw(bound);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(eq1, None);
    let h1 = proof.add_assume(eq2, None);
    let h2 = proof.add_assume(not_bound, None);
    let farkas = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_eq1, not_eq2, bound],
        FarkasAnnotation::from_ints(&[1, 1, 1]),
    );
    let after_eq1 = proof.add_resolution(vec![not_eq2, bound], eq1, h0, farkas);
    let bound_unit = proof.add_resolution(vec![bound], eq2, h1, after_eq1);
    proof.add_resolution(Vec::new(), bound, h2, bound_unit);

    check_proof_strict(&proof, &terms).expect("opaque-product Farkas proof validates strictly");
    let alethe =
        export_alethe_with_problem_scope(&proof, &terms, &[eq1, eq2, not_bound]);
    assert!(
        alethe.contains(":rule la_generic :args (-1 -1 1)"),
        "{alethe}"
    );
    assert!(!alethe.contains(":rule hole"), "{alethe}");
    assert_carcara_accepts("lra_shared_opaque_nonlinear_product", PROBLEM, &alethe);
}
