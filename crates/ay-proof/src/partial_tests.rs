// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

#[test]
fn test_check_proof_partial_valid_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![], x, p0, p1);

    let (partial, error) = check_proof_partial(&proof, &terms);
    assert!(error.is_none(), "valid proof should have no error");
    assert_eq!(partial.total_steps, 3);
    assert_eq!(partial.checked_steps, 3);
    assert_eq!(partial.skipped_hole_steps, 0);
}

#[test]
fn test_check_proof_partial_skips_hole_steps() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    // Hole step: accepted for linkage but not semantically checked
    proof.add_rule_step(AletheRule::Hole, vec![not_x], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Drup, vec![], vec![], vec![]);

    let (partial, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "partial check should accept holes: {error:?}"
    );
    assert_eq!(partial.total_steps, 3);
    assert_eq!(partial.checked_steps, 2);
    assert_eq!(partial.skipped_hole_steps, 1);
}

#[test]
fn test_check_proof_partial_error_path_does_not_inflate_checked_steps() {
    // Core #4592 test: on error, checked_steps must reflect only the prefix
    // actually validated, not total_steps - skipped_hole_steps.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);

    // 5-step proof where step 2 is invalid resolution:
    //   0: assume(x)         — validated (checked_steps=1)
    //   1: assume(not_x)     — validated (checked_steps=2)
    //   2: resolution({y})   — FAILS: y is not a valid resolvent of x, not_x
    //   3: assume(y)         — never reached
    //   4: drup({})          — never reached
    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![y], x, p0, p1);
    proof.add_assume(y, None);
    proof.add_rule_step(AletheRule::Drup, vec![], vec![], vec![]);

    let (partial, error) = check_proof_partial(&proof, &terms);
    assert!(error.is_some(), "invalid resolution should produce error");
    assert_eq!(partial.total_steps, 5);
    assert_eq!(
        partial.checked_steps, 2,
        "checked_steps must reflect prefix actually validated, not total - holes"
    );
    assert_eq!(partial.skipped_hole_steps, 0);
}

#[test]
fn test_check_proof_partial_error_with_holes_before_failure() {
    // Holes before a failing step: checked_steps counts only validated
    // non-hole steps.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);

    // 4-step proof:
    //   0: assume(x)         — validated (checked=1)
    //   1: hole({not_x})     — skipped (holes=1)
    //   2: resolution({y})   — FAILS
    //   3: drup({})          — never reached
    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let hole_id = proof.add_rule_step(AletheRule::Hole, vec![not_x], Vec::new(), Vec::new());
    proof.add_resolution(vec![y], x, p0, hole_id);
    proof.add_rule_step(AletheRule::Drup, vec![], vec![], vec![]);

    let (partial, error) = check_proof_partial(&proof, &terms);
    assert!(error.is_some(), "invalid resolution should produce error");
    assert_eq!(partial.total_steps, 4);
    assert_eq!(partial.checked_steps, 1, "only assume was validated");
    assert_eq!(partial.skipped_hole_steps, 1);
}

#[test]
fn test_check_proof_partial_empty_proof() {
    let terms = TermStore::new();
    let proof = Proof::new();

    let (partial, error) = check_proof_partial(&proof, &terms);
    assert!(matches!(error, Some(ProofCheckError::EmptyProof)));
    assert_eq!(partial.total_steps, 0);
    assert_eq!(partial.checked_steps, 0);
}

#[test]
fn test_partial_proof_check_display() {
    let partial = PartialProofCheck {
        checked_steps: 3,
        skipped_hole_steps: 1,
        total_steps: 5,
    };
    let display = format!("{partial}");
    assert!(display.contains("checked=3"));
    assert!(display.contains("skipped_holes=1"));
    assert!(display.contains("total=5"));
}

#[test]
fn test_check_proof_partial_accepts_trust_resolution_chain() {
    let mut terms = TermStore::new();
    let c1 = terms.mk_var("c1", Sort::Int);
    let c2 = terms.mk_var("c2", Sort::Int);
    let c3 = terms.mk_var("c3", Sort::Int);
    let s1 = terms.mk_var("s1", Sort::Int);
    let s2 = terms.mk_var("s2", Sort::Int);

    let three = terms.mk_int(3.into());
    let five_hundred = terms.mk_int(500.into());
    let thousand = terms.mk_int(1000.into());
    let four_k = terms.mk_int(4096.into());

    let eq1_mul = terms.mk_app(Symbol::named("*"), vec![c1, four_k], Sort::Int);
    let eq1_rhs = terms.mk_app(Symbol::named("+"), vec![eq1_mul, s1], Sort::Int);
    let eq1 = terms.mk_app(Symbol::named("="), vec![four_k, eq1_rhs], Sort::Bool);

    let eq2_lhs = terms.mk_app(Symbol::named("*"), vec![s1, three], Sort::Int);
    let eq2_mul = terms.mk_app(Symbol::named("*"), vec![c2, four_k], Sort::Int);
    let eq2_rhs = terms.mk_app(Symbol::named("+"), vec![eq2_mul, s2], Sort::Int);
    let eq2 = terms.mk_app(Symbol::named("="), vec![eq2_lhs, eq2_rhs], Sort::Bool);

    let eq3_lhs = terms.mk_app(Symbol::named("+"), vec![s2, five_hundred], Sort::Int);
    let eq3_mul = terms.mk_app(Symbol::named("*"), vec![c3, four_k], Sort::Int);
    let eq3_rhs = terms.mk_app(Symbol::named("+"), vec![eq3_mul, thousand], Sort::Int);
    let eq3 = terms.mk_app(Symbol::named("="), vec![eq3_lhs, eq3_rhs], Sort::Bool);

    let not_eq1 = terms.mk_not(eq1);
    let not_eq2 = terms.mk_not(eq2);
    let not_eq3 = terms.mk_not(eq3);

    let mut proof = Proof::new();
    let p0 = proof.add_rule_step(AletheRule::Trust, vec![eq1], Vec::new(), Vec::new());
    let p1 = proof.add_assume(eq2, None);
    let p2 = proof.add_rule_step(AletheRule::Trust, vec![eq3], Vec::new(), Vec::new());
    let p3 = proof.add_rule_step(
        AletheRule::Trust,
        vec![not_eq1, not_eq2, not_eq3],
        Vec::new(),
        Vec::new(),
    );
    let p4 = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![not_eq2, not_eq3],
        vec![p3, p0],
        Vec::new(),
    );
    let p5 = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![not_eq3],
        vec![p4, p1],
        Vec::new(),
    );
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![p5, p2], Vec::new());

    let (partial, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "trust-backed th_resolution chain should validate: {error:?}"
    );
    assert_eq!(partial.total_steps, 7);
    assert_eq!(partial.checked_steps, 7);
    assert_eq!(partial.skipped_hole_steps, 0);
}
