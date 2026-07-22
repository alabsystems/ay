// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(int_var(name))
}

// ========================================================================
// drop_mod_div_conjuncts tests
// ========================================================================

#[test]
fn drop_mod_div_no_mod_unchanged() {
    let expr = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::int(1)),
        ChcExpr::eq(var("y"), ChcExpr::int(2)),
    );
    let result = drop_mod_div_conjuncts(&expr);
    assert_eq!(result.collect_conjuncts().len(), 2);
}

#[test]
fn drop_mod_div_removes_mod_conjuncts() {
    let mod_conjunct = ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(2)), ChcExpr::int(0));
    let bound = ChcExpr::le(var("x"), ChcExpr::int(5));
    let expr = ChcExpr::and(bound.clone(), mod_conjunct);
    let result = drop_mod_div_conjuncts(&expr);
    let conjuncts = result.collect_conjuncts();
    assert_eq!(conjuncts.len(), 1);
    assert_eq!(conjuncts[0], bound);
}

#[test]
fn drop_mod_div_all_mod_yields_true() {
    let expr = ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(2)), ChcExpr::int(0));
    let result = drop_mod_div_conjuncts(&expr);
    assert_eq!(result, ChcExpr::Bool(true));
}

#[test]
fn drop_mod_div_preserves_non_mod_conjuncts() {
    let expr = ChcExpr::and_all([
        ChcExpr::eq(var("x"), ChcExpr::int(1)),
        ChcExpr::eq(var("y"), ChcExpr::int(2)),
        ChcExpr::eq(ChcExpr::mod_op(var("z"), ChcExpr::int(3)), ChcExpr::int(0)),
    ]);
    let result = drop_mod_div_conjuncts(&expr);
    let conjuncts = result.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

// ========================================================================
// substitute_mod_equalities_in_body tests (#3211 soundness)
// ========================================================================

#[test]
fn subst_mod_eq_basic() {
    let body = ChcExpr::and(
        ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(3)), var("y")),
        ChcExpr::ge(var("y"), ChcExpr::int(1)),
    );
    let result = substitute_mod_equalities_in_body(&body);
    assert!(result.is_some(), "should find mod equality to substitute");
    let result = result.unwrap();
    assert!(
        !PdrSolver::contains_mod_or_div(&result),
        "substituted body should be mod-free: {result}"
    );
    let conjuncts = result.collect_conjuncts();
    let has_lower = conjuncts
        .iter()
        .any(|c| *c == ChcExpr::ge(var("y"), ChcExpr::int(0)));
    let has_upper = conjuncts
        .iter()
        .any(|c| *c == ChcExpr::lt(var("y"), ChcExpr::int(3)));
    assert!(has_lower, "missing range lower bound: 0 <= y in {result}");
    assert!(has_upper, "missing range upper bound: y < 3 in {result}");
}

#[test]
fn subst_mod_eq_reversed_operands() {
    let body = ChcExpr::and(
        ChcExpr::eq(var("y"), ChcExpr::mod_op(var("x"), ChcExpr::int(2))),
        ChcExpr::eq(var("y"), ChcExpr::int(0)),
    );
    let result = substitute_mod_equalities_in_body(&body);
    assert!(result.is_some(), "should match reversed operands");
}

#[test]
fn subst_mod_eq_no_mod_returns_none() {
    let body = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::int(5)),
        ChcExpr::ge(var("y"), ChcExpr::int(0)),
    );
    assert!(substitute_mod_equalities_in_body(&body).is_none());
}

#[test]
fn subst_mod_eq_mod_without_var_returns_none() {
    let body = ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(3)), ChcExpr::int(0));
    assert!(substitute_mod_equalities_in_body(&body).is_none());
}

#[test]
fn subst_mod_eq_trivially_false_on_contradiction() {
    let body = ChcExpr::and(
        ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(2)), var("y")),
        ChcExpr::eq(var("y"), ChcExpr::int(5)),
    );
    let result = substitute_mod_equalities_in_body(&body);
    assert!(result.is_some());
    let result = result.unwrap();
    assert_eq!(
        result,
        ChcExpr::Bool(false),
        "y=5 contradicts range 0 <= y < 2: {result}"
    );
}

#[test]
fn subst_mod_eq_modulus_one_range() {
    let body = ChcExpr::and(
        ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(1)), var("y")),
        ChcExpr::ge(var("y"), ChcExpr::int(1)),
    );
    let result = substitute_mod_equalities_in_body(&body);
    assert!(result.is_some(), "modulus=1 should be substituted");
    let result = result.unwrap();
    assert!(
        !PdrSolver::contains_mod_or_div(&result),
        "substituted body should be mod-free: {result}"
    );
    let conjuncts = result.collect_conjuncts();
    let has_lower = conjuncts
        .iter()
        .any(|c| *c == ChcExpr::ge(var("y"), ChcExpr::int(0)));
    let has_upper = conjuncts
        .iter()
        .any(|c| *c == ChcExpr::lt(var("y"), ChcExpr::int(1)));
    assert!(has_lower, "missing range lower bound: 0 <= y in {result}");
    assert!(has_upper, "missing range upper bound: y < 1 in {result}");
}

#[test]
fn subst_mod_eq_negative_modulus_skipped() {
    let body = ChcExpr::and(
        ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(-3)), var("y")),
        ChcExpr::ge(var("y"), ChcExpr::int(0)),
    );
    let result = substitute_mod_equalities_in_body(&body);
    assert!(
        result.is_none(),
        "negative modulus should be skipped (return None)"
    );
}

#[test]
fn subst_mod_eq_zero_modulus_skipped() {
    let body = ChcExpr::eq(ChcExpr::mod_op(var("x"), ChcExpr::int(0)), var("y"));
    let result = substitute_mod_equalities_in_body(&body);
    assert!(
        result.is_none(),
        "zero modulus should be skipped (return None)"
    );
}
