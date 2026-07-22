// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{extract_negated_parity_constraint, extract_parity_constraint};
use crate::{ChcExpr, ChcSort, ChcVar};

#[test]
fn extract_parity_constraint_mod_left() {
    // (= (mod x 3) 1)
    let var = ChcVar::new("x", ChcSort::Int);
    let mod_expr = ChcExpr::mod_op(ChcExpr::var(var), ChcExpr::int(3));
    let eq_expr = ChcExpr::eq(mod_expr, ChcExpr::int(1));

    let result = extract_parity_constraint(&eq_expr);
    assert_eq!(result, Some(("x".to_string(), 3, 1)));
}

#[test]
fn extract_parity_constraint_mod_right() {
    // (= 2 (mod y 4))
    let var = ChcVar::new("y", ChcSort::Int);
    let mod_expr = ChcExpr::mod_op(ChcExpr::var(var), ChcExpr::int(4));
    let eq_expr = ChcExpr::eq(ChcExpr::int(2), mod_expr);

    let result = extract_parity_constraint(&eq_expr);
    assert_eq!(result, Some(("y".to_string(), 4, 2)));
}

#[test]
fn extract_parity_constraint_non_parity_returns_none() {
    // (= x 5) - not a parity constraint
    let var = ChcVar::new("x", ChcSort::Int);
    let eq_expr = ChcExpr::eq(ChcExpr::var(var), ChcExpr::int(5));

    let result = extract_parity_constraint(&eq_expr);
    assert_eq!(result, None);
}

#[test]
fn extract_negated_parity_constraint_basic() {
    // (not (= (mod z 2) 0))
    let var = ChcVar::new("z", ChcSort::Int);
    let mod_expr = ChcExpr::mod_op(ChcExpr::var(var), ChcExpr::int(2));
    let eq_expr = ChcExpr::eq(mod_expr, ChcExpr::int(0));
    let not_expr = ChcExpr::not(eq_expr);

    let result = extract_negated_parity_constraint(&not_expr);
    assert_eq!(result, Some(("z".to_string(), 2, 0)));
}

#[test]
fn extract_negated_parity_constraint_non_negation_returns_none() {
    // (= (mod x 2) 0) - not negated
    let var = ChcVar::new("x", ChcSort::Int);
    let mod_expr = ChcExpr::mod_op(ChcExpr::var(var), ChcExpr::int(2));
    let eq_expr = ChcExpr::eq(mod_expr, ChcExpr::int(0));

    let result = extract_negated_parity_constraint(&eq_expr);
    assert_eq!(result, None);
}
