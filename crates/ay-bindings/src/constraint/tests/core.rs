// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::constraint::logic;
use crate::constraint::Constraint;
use crate::expr::Expr;
use crate::sort::Sort;

#[test]
fn test_declare_const() {
    let c = Constraint::declare_const("x", Sort::bv32());
    assert_eq!(c.to_string(), "(declare-const x (_ BitVec 32))");
}

#[test]
fn test_declare_fun() {
    let c = Constraint::declare_fun("f", vec![Sort::bv32(), Sort::bv32()], Sort::bool());
    assert_eq!(
        c.to_string(),
        "(declare-fun f ((_ BitVec 32) (_ BitVec 32)) Bool)"
    );
}

#[test]
fn test_define_fun() {
    let x = Expr::var("x", Sort::int());
    let body = x.int_add(Expr::int(1));
    let c = Constraint::define_fun("inc", vec![("x".to_string(), Sort::int())], body);
    assert_eq!(c.to_string(), "(define-fun inc ((x Int)) Int (+ x 1))");
}

#[test]
fn test_assert() {
    let x = Expr::var("x", Sort::bool());
    let c = Constraint::assert(x);
    assert_eq!(c.to_string(), "(assert x)");
}

#[test]
fn test_assert_labeled() {
    let x = Expr::var("x", Sort::bool());
    let c = Constraint::assert_labeled(x, "my_assertion");
    assert_eq!(c.to_string(), "(assert (! x :named my_assertion))");
}

#[test]
fn test_assume() {
    // assume() is a semantic alias for assert() - same SMT-LIB output
    let x = Expr::var("x", Sort::bool());
    let c = Constraint::assume(x);
    assert_eq!(c.to_string(), "(assert x)");
}

#[test]
fn test_assume_labeled() {
    // assume_labeled() is a semantic alias for assert_labeled()
    let x = Expr::var("x", Sort::bool());
    let c = Constraint::assume_labeled(x, "path_constraint");
    assert_eq!(c.to_string(), "(assert (! x :named path_constraint))");
}

#[test]
fn test_push_pop() {
    assert_eq!(Constraint::push().to_string(), "(push)");
    assert_eq!(Constraint::pop(2).to_string(), "(pop 2)");
}

#[test]
fn test_check_sat() {
    assert_eq!(Constraint::check_sat().to_string(), "(check-sat)");
}

#[test]
fn test_check_sat_assuming() {
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::bool());
    let c = Constraint::check_sat_assuming(vec![a, b]);
    assert_eq!(c.to_string(), "(check-sat-assuming (a b))");
}

#[test]
fn test_get_value() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let c = Constraint::get_value(vec![x, y]);
    assert_eq!(c.to_string(), "(get-value (x y))");
}

#[test]
fn test_set_logic() {
    let c = Constraint::set_logic(logic::QF_BV);
    assert_eq!(c.to_string(), "(set-logic QF_BV)");
}

#[test]
fn test_declare_const_with_colons() {
    // Rust identifiers with :: must be quoted
    let c = Constraint::declare_const("test_function::local_1_0", Sort::bool());
    assert_eq!(
        c.to_string(),
        "(declare-const |test_function::local_1_0| Bool)"
    );
}

#[test]
fn test_declare_fun_with_colons() {
    let c = Constraint::declare_fun("module::function", vec![Sort::bv32()], Sort::bool());
    assert_eq!(
        c.to_string(),
        "(declare-fun |module::function| ((_ BitVec 32)) Bool)"
    );
}

#[test]
fn test_define_fun_with_colons() {
    let x = Expr::var("module::x", Sort::int());
    let body = x.int_add(Expr::int(1));
    let c = Constraint::define_fun(
        "module::inc",
        vec![("module::x".to_string(), Sort::int())],
        body,
    );
    assert_eq!(
        c.to_string(),
        "(define-fun |module::inc| ((|module::x| Int)) Int (+ |module::x| 1))"
    );
}

#[test]
fn test_assert_labeled_with_colons() {
    let x = Expr::var("x", Sort::bool());
    let c = Constraint::assert_labeled(x, "test::assertion");
    assert_eq!(c.to_string(), "(assert (! x :named |test::assertion|))");
}
