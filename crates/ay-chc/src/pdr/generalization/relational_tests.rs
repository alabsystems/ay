// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

fn eq_var_int(var: &ChcVar, val: i128) -> ChcExpr {
    ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::Int(val))
}

fn contains_op(expr: &ChcExpr, needle: &ChcOp) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(op, args) => {
            *op == *needle || args.iter().any(|arg| contains_op(arg.as_ref(), needle))
        }
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|arg| contains_op(arg.as_ref(), needle))
        }
        ChcExpr::ConstArray(_ks, value) => contains_op(value.as_ref(), needle),
        _ => false,
    })
}

fn contains_subexpr(expr: &ChcExpr, needle: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| {
        if expr == needle {
            return true;
        }

        match expr {
            ChcExpr::Op(_, args) => args
                .iter()
                .any(|arg| contains_subexpr(arg.as_ref(), needle)),
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => args
                .iter()
                .any(|arg| contains_subexpr(arg.as_ref(), needle)),
            ChcExpr::ConstArray(_ks, value) => contains_subexpr(value.as_ref(), needle),
            _ => false,
        }
    })
}

#[test]
fn returns_none_without_two_equalities() {
    let x = ChcVar::new("x", ChcSort::Int);
    let conjuncts = vec![
        eq_var_int(&x, 1),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::Int(0)),
    ];
    let result = try_relational_equality_generalization_with(&conjuncts, 0, false, |_| {
        panic!("unexpected inductiveness query");
    });
    assert_eq!(result, None);
}

#[test]
fn prefers_equality_invariant_disequality_when_inductive() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let conjuncts = vec![eq_var_int(&x, 1), eq_var_int(&y, 0)];

    let expected = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(y)));
    let result = try_relational_equality_generalization_with(&conjuncts, 3, false, |expr| {
        assert_eq!(expr, &expected);
        true
    });

    assert_eq!(result, Some(expected));
}

#[test]
fn uses_context_when_pure_disequality_is_not_inductive() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let x_eq = eq_var_int(&x, 1);
    let y_eq = eq_var_int(&y, 0);
    let z_eq = eq_var_int(&z, 5);
    let conjuncts = vec![x_eq, y_eq, z_eq.clone()];

    let disequality = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(y)));
    let generalized = build_conjunction(&[z_eq, disequality.clone()]);

    let mut saw_diseq = false;
    let mut saw_generalized = false;
    let result = try_relational_equality_generalization_with(&conjuncts, 2, false, |expr| {
        if expr == &disequality {
            saw_diseq = true;
            return false;
        }
        if expr == &generalized {
            saw_generalized = true;
            return true;
        }
        panic!("unexpected inductiveness query: {expr}");
    });

    assert!(saw_diseq);
    assert!(saw_generalized);
    assert_eq!(result, Some(generalized));
}

#[test]
fn returns_offset_relational_equality_when_inductive() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let conjuncts = vec![eq_var_int(&x, 10), eq_var_int(&y, 3)];

    let expected = ChcExpr::eq(
        ChcExpr::var(x),
        ChcExpr::add(ChcExpr::var(y), ChcExpr::Int(7)),
    );
    let result =
        try_relational_equality_generalization_with(&conjuncts, 1, false, |expr| expr == &expected);

    assert_eq!(result, Some(expected));
}

#[test]
fn skips_offsets_with_large_abs_diff() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let conjuncts = vec![eq_var_int(&x, 0), eq_var_int(&y, 100)];

    let mut calls = 0;
    let mut saw_add = false;
    let result = try_relational_equality_generalization_with(&conjuncts, 0, false, |expr| {
        calls += 1;
        saw_add |= contains_op(expr, &ChcOp::Add);
        false
    });

    assert_eq!(result, None);
    assert_eq!(calls, 1);
    assert!(!saw_add);
}

#[test]
fn step4_tries_pure_equalities_before_offsets() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    let x_eq = eq_var_int(&x, 5);
    let y_eq = eq_var_int(&y, 5);
    let z_eq = eq_var_int(&z, 1);
    let conjuncts = vec![x_eq, y_eq, z_eq.clone()];

    let pure_rel_eq = ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(y));
    let pure_generalized = build_conjunction(&[z_eq, pure_rel_eq]);

    let mut seen = Vec::new();
    let result = try_relational_equality_generalization_with(&conjuncts, 0, false, |expr| {
        if contains_op(expr, &ChcOp::Not) {
            return false;
        }
        if expr == &pure_generalized {
            seen.push("pure");
            return false;
        }
        if contains_op(expr, &ChcOp::Add) {
            seen.push("offset");
            return true;
        }
        false
    });

    assert!(result.is_some());
    assert_eq!(seen.as_slice(), ["pure", "offset"]);
}

#[test]
fn step5_strengthening_can_drop_point_constraints() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let x_eq = eq_var_int(&x, 5);
    let y_eq = eq_var_int(&y, 5);
    let conjuncts = vec![x_eq.clone(), y_eq];

    let rel_eq = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y));
    let expected = build_conjunction(&[x_eq, rel_eq.clone()]);

    let result = try_relational_equality_generalization_with(&conjuncts, 0, false, |expr| {
        contains_subexpr(expr, &rel_eq) && contains_subexpr(expr, &eq_var_int(&x, 5))
    });

    assert_eq!(result, Some(expected));
}
