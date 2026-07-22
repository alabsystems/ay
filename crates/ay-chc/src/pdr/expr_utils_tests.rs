// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, ChcVar};

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

#[test]
fn extract_no_equalities_from_constant() {
    let expr = ChcExpr::int(42);
    let result = extract_equality_constants(&expr, "x");
    assert!(result.is_empty());
}

#[test]
fn extract_single_var_eq_constant() {
    // (= x 5)
    let expr = ChcExpr::eq(var("x"), ChcExpr::int(5));
    let result = extract_equality_constants(&expr, "x");
    assert_eq!(result.len(), 1);
    assert!(result.contains(&5));
}

#[test]
fn extract_reversed_constant_eq_var() {
    // (= 5 x) — reversed operand order
    let expr = ChcExpr::eq(ChcExpr::int(5), var("x"));
    let result = extract_equality_constants(&expr, "x");
    assert_eq!(result.len(), 1);
    assert!(result.contains(&5));
}

#[test]
fn extract_ignores_different_variable() {
    // (= y 5) when searching for "x"
    let expr = ChcExpr::eq(var("y"), ChcExpr::int(5));
    let result = extract_equality_constants(&expr, "x");
    assert!(result.is_empty());
}

#[test]
fn extract_multiple_constants_from_conjunction() {
    // (and (= x 1) (= x 3))
    let expr = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::int(1)),
        ChcExpr::eq(var("x"), ChcExpr::int(3)),
    );
    let result = extract_equality_constants(&expr, "x");
    assert_eq!(result.len(), 2);
    assert!(result.contains(&1));
    assert!(result.contains(&3));
}

#[test]
fn extract_from_nested_ite() {
    // (ite (= J 1) then_expr else_expr)
    let expr = ChcExpr::ite(
        ChcExpr::eq(var("J"), ChcExpr::int(1)),
        ChcExpr::int(10),
        ChcExpr::int(20),
    );
    let result = extract_equality_constants(&expr, "J");
    assert_eq!(result.len(), 1);
    assert!(result.contains(&1));
}

#[test]
fn extract_deduplicates_constants() {
    // (and (= x 5) (= x 5)) — same constant twice
    let expr = ChcExpr::and(
        ChcExpr::eq(var("x"), ChcExpr::int(5)),
        ChcExpr::eq(var("x"), ChcExpr::int(5)),
    );
    let result = extract_equality_constants(&expr, "x");
    assert_eq!(result.len(), 1);
}

#[test]
fn extract_ignores_var_eq_var() {
    // (= x y) — no integer constant
    let expr = ChcExpr::eq(var("x"), var("y"));
    let result = extract_equality_constants(&expr, "x");
    assert!(result.is_empty());
}

#[test]
fn extract_negative_constant() {
    // (= x -3)
    let expr = ChcExpr::eq(var("x"), ChcExpr::int(-3));
    let result = extract_equality_constants(&expr, "x");
    assert_eq!(result.len(), 1);
    assert!(result.contains(&-3));
}

#[test]
fn extract_zero_constant() {
    // (= x 0)
    let expr = ChcExpr::eq(var("x"), ChcExpr::int(0));
    let result = extract_equality_constants(&expr, "x");
    assert_eq!(result.len(), 1);
    assert!(result.contains(&0));
}

#[test]
fn extract_ignores_inequalities() {
    // (>= x 5) — not an equality
    let expr = ChcExpr::ge(var("x"), ChcExpr::int(5));
    let result = extract_equality_constants(&expr, "x");
    assert!(result.is_empty());
}
