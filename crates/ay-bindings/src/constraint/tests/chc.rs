// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::constraint::Constraint;
use crate::expr::Expr;
use crate::sort::Sort;

#[test]
fn test_declare_rel_empty_args() {
    let c = Constraint::declare_rel("Init", vec![]);
    assert_eq!(c.to_string(), "(declare-rel Init ())");
}

#[test]
fn test_declare_rel_with_args() {
    let c = Constraint::declare_rel("Inv", vec![Sort::int(), Sort::int()]);
    assert_eq!(c.to_string(), "(declare-rel Inv (Int Int))");
}

#[test]
fn test_declare_rel_with_bitvec_args() {
    let c = Constraint::declare_rel("State", vec![Sort::bv32(), Sort::bool()]);
    assert_eq!(c.to_string(), "(declare-rel State ((_ BitVec 32) Bool))");
}

#[test]
fn test_declare_rel_with_colons() {
    // Rust identifiers with :: must be quoted
    let c = Constraint::declare_rel("module::Inv", vec![Sort::int()]);
    assert_eq!(c.to_string(), "(declare-rel |module::Inv| (Int))");
}

#[test]
fn test_rule_simple() {
    // Rule: (x > 0) => Inv(x)
    // We represent relation applications as variables for testing
    let inv_x = Expr::var("Inv_x", Sort::bool());
    let x = Expr::var("x", Sort::int());
    let cond = x.int_gt(Expr::int_const(0));
    let c = Constraint::rule(inv_x, cond);
    assert_eq!(c.to_string(), "(rule (=> (> x 0) Inv_x))");
}

#[test]
fn test_rule_with_true_body() {
    // Fact using rule: true => Init(0)
    let init_0 = Expr::var("Init_0", Sort::bool());
    let c = Constraint::rule(init_0, Expr::bool_const(true));
    assert_eq!(c.to_string(), "(rule (=> true Init_0))");
}

#[test]
fn test_fact() {
    // Fact: Init(0) is always true
    let init_0 = Expr::var("Init_0", Sort::bool());
    let c = Constraint::fact(init_0);
    assert_eq!(c.to_string(), "(rule (=> true Init_0))");
}

#[test]
fn test_rule_constraint() {
    // Constraint: Error state must be unreachable
    let error = Expr::var("Error", Sort::bool());
    let c = Constraint::rule_constraint(error);
    assert_eq!(c.to_string(), "(rule Error)");
}

#[test]
fn test_query() {
    // Query: is Error reachable?
    let error = Expr::var("Error", Sort::bool());
    let c = Constraint::query(error);
    assert_eq!(c.to_string(), "(query Error)");
}

#[test]
fn test_query_complex_expr() {
    // Query with complex expression
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::bool());
    let c = Constraint::query(a.and(b));
    assert_eq!(c.to_string(), "(query (and a b))");
}
