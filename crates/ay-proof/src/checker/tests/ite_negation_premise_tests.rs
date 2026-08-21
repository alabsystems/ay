// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// --- not_equiv1 (premise-based) ---

#[test]
fn test_strict_not_equiv1_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq = terms.mk_not_raw(eq_ab);
    // Premise: (not (= a b))
    let prior = vec![Some(vec![not_eq])];
    // not_equiv1: (cl a b)
    validate_strict_with_derived(
        &terms,
        AletheRule::NotEquiv1,
        vec![a, b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_equiv1 should pass");
}

// --- not_equiv2 (premise-based) ---

#[test]
fn test_strict_not_equiv2_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq = terms.mk_not_raw(eq_ab);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // Premise: (not (= a b))
    let prior = vec![Some(vec![not_eq])];
    // not_equiv2: (cl (not a) (not b))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotEquiv2,
        vec![not_a, not_b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_equiv2 should pass");
}

// --- not_ite1 (premise-based) ---

#[test]
fn test_strict_not_ite1_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    let not_e = terms.mk_not_raw(e);
    // Premise: (not (ite c t e))
    let prior = vec![Some(vec![not_ite])];
    // not_ite1: (cl c (not e))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotIte1,
        vec![c, not_e],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_ite1 should pass");
}

// --- not_ite2 (premise-based) ---

#[test]
fn test_strict_not_ite2_valid() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    let not_c = terms.mk_not_raw(c);
    let not_t = terms.mk_not_raw(t);
    // Premise: (not (ite c t e))
    let prior = vec![Some(vec![not_ite])];
    // not_ite2: (cl (not c) (not t))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotIte2,
        vec![not_c, not_t],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_ite2 should pass");
}
