// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn assert_ite_split_preserves_target(
    target: ChcVar,
    then_value: ChcExpr,
    else_value: ChcExpr,
    ite_on_left: bool,
) {
    let guard = ChcVar::new("guard", ChcSort::Bool);
    let ite = ChcExpr::ite(
        ChcExpr::var(guard.clone()),
        then_value.clone(),
        else_value.clone(),
    );
    let target_expr = ChcExpr::var(target.clone());
    let constraint = if ite_on_left {
        ChcExpr::eq(ite, target_expr)
    } else {
        ChcExpr::eq(target_expr, ite)
    };

    let cases = PdrSolver::split_ite_in_constraint(&constraint);
    assert_eq!(cases.len(), 2);
    assert_eq!(
        cases[0],
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(target.clone()), then_value),
            ChcExpr::var(guard.clone()),
        )
    );
    assert_eq!(
        cases[1],
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(target), else_value),
            ChcExpr::not(ChcExpr::var(guard)),
        )
    );
}

#[test]
fn ite_case_split_preserves_bool_target_sort() {
    assert_ite_split_preserves_target(
        ChcVar::new("value", ChcSort::Bool),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
        false,
    );
}

#[test]
fn ite_case_split_preserves_real_target_sort_in_reversed_equality() {
    assert_ite_split_preserves_target(
        ChcVar::new("value", ChcSort::Real),
        ChcExpr::Real(1, 2),
        ChcExpr::Real(3, 2),
        true,
    );
}

#[test]
fn ite_case_split_preserves_bitvec_target_sort() {
    assert_ite_split_preserves_target(
        ChcVar::new("value", ChcSort::BitVec(8)),
        ChcExpr::BitVec(1, 8),
        ChcExpr::BitVec(2, 8),
        false,
    );
}
