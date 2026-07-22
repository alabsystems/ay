// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::constraint::Constraint;
use crate::expr::Expr;
use crate::sort::Sort;

#[test]
fn test_maximize() {
    let x = Expr::var("x", Sort::int());
    let c = Constraint::maximize(x);
    assert_eq!(c.to_string(), "(maximize x)");
}

#[test]
fn test_minimize() {
    let x = Expr::var("x", Sort::real());
    let c = Constraint::minimize(x);
    assert_eq!(c.to_string(), "(minimize x)");
}

#[test]
fn test_maximize_expr() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let sum = x.int_add(y);
    let c = Constraint::maximize(sum);
    assert_eq!(c.to_string(), "(maximize (+ x y))");
}

#[test]
fn test_get_objectives() {
    let c = Constraint::get_objectives();
    assert_eq!(c.to_string(), "(get-objectives)");
}
