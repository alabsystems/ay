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

#[test]
fn fixed_int_subst_eq_single_var() {
    let expr = ChcExpr::eq(var("x"), ChcExpr::int(5));
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(5));
}

#[test]
fn fixed_int_subst_eq_reversed_operands() {
    let expr = ChcExpr::eq(ChcExpr::int(7), var("x"));
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(7));
}

#[test]
fn fixed_int_subst_tight_bounds_yield_eq() {
    let expr = ChcExpr::and(
        ChcExpr::le(var("x"), ChcExpr::int(3)),
        ChcExpr::ge(var("x"), ChcExpr::int(3)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(3));
}

#[test]
fn fixed_int_subst_strict_bounds_yield_eq() {
    let expr = ChcExpr::and(
        ChcExpr::lt(var("x"), ChcExpr::int(5)),
        ChcExpr::gt(var("x"), ChcExpr::int(3)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(4));
}

#[test]
fn fixed_int_subst_wide_bounds_no_subst() {
    let expr = ChcExpr::and(
        ChcExpr::le(var("x"), ChcExpr::int(10)),
        ChcExpr::ge(var("x"), ChcExpr::int(0)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert!(subst.is_empty());
}

#[test]
fn fixed_int_subst_negated_lt() {
    let expr = ChcExpr::and(
        ChcExpr::not(ChcExpr::lt(var("x"), ChcExpr::int(5))),
        ChcExpr::le(var("x"), ChcExpr::int(5)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(5));
}

#[test]
fn fixed_int_subst_negated_le() {
    let expr = ChcExpr::and(
        ChcExpr::not(ChcExpr::le(var("x"), ChcExpr::int(4))),
        ChcExpr::le(var("x"), ChcExpr::int(5)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(5));
}

#[test]
fn fixed_int_subst_negated_gt() {
    let expr = ChcExpr::and(
        ChcExpr::not(ChcExpr::gt(var("x"), ChcExpr::int(5))),
        ChcExpr::ge(var("x"), ChcExpr::int(5)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(5));
}

#[test]
fn fixed_int_subst_negated_ge() {
    let expr = ChcExpr::and(
        ChcExpr::not(ChcExpr::ge(var("x"), ChcExpr::int(6))),
        ChcExpr::ge(var("x"), ChcExpr::int(5)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(5));
}

#[test]
fn fixed_int_subst_multiple_vars() {
    let expr = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::int(1)),
        ChcExpr::eq(var("y"), ChcExpr::int(2)),
    );
    let mut subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    subst.sort_by_key(|(var, _)| var.name.clone());
    assert_eq!(subst.len(), 2);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(1));
    assert_eq!(subst[1].0, int_var("y"));
    assert_eq!(subst[1].1, ChcExpr::int(2));
}

#[test]
fn fixed_int_subst_empty_for_bool_true() {
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&ChcExpr::Bool(true));
    assert!(subst.is_empty());
}

#[test]
fn fixed_int_subst_var_eq_var_no_subst() {
    let expr = ChcExpr::eq(var("x"), var("y"));
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert!(subst.is_empty());
}

#[test]
fn fixed_int_subst_reversed_comparison_k_le_var() {
    let expr = ChcExpr::and(
        ChcExpr::le(ChcExpr::int(3), var("x")),
        ChcExpr::le(var("x"), ChcExpr::int(3)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(3));
}

#[test]
fn fixed_int_subst_reversed_comparison_k_lt_var() {
    let expr = ChcExpr::and(
        ChcExpr::lt(ChcExpr::int(2), var("x")),
        ChcExpr::lt(var("x"), ChcExpr::int(4)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(3));
}

#[test]
fn fixed_int_subst_reversed_comparison_k_ge_var() {
    let expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::int(3), var("x")),
        ChcExpr::ge(var("x"), ChcExpr::int(3)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(3));
}

#[test]
fn fixed_int_subst_reversed_comparison_k_gt_var() {
    let expr = ChcExpr::and(
        ChcExpr::gt(ChcExpr::int(4), var("x")),
        ChcExpr::gt(var("x"), ChcExpr::int(2)),
    );
    let subst = PdrSolver::fixed_int_subst_from_conjuncts(&expr);
    assert_eq!(subst.len(), 1);
    assert_eq!(subst[0].0, int_var("x"));
    assert_eq!(subst[0].1, ChcExpr::int(3));
}
