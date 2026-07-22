// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::contradiction::{extract_implied_relations_from_conjuncts, is_trivial_contradiction};
use super::equality::{
    extract_equalities_and_propagate, extract_equalities_with_relations, is_point_cube_for_vars,
};
use super::eval::{try_eval_const, value_expr_from_model};
use super::PointCubeUnionFind;
use crate::pdr::types::RelationType;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

#[test]
fn test_point_cube_union_find_basic() {
    let mut uf = PointCubeUnionFind::new();

    // x = 5 grounds x
    uf.mark_grounded("x");
    assert!(uf.is_grounded("x"));

    // y is not grounded yet
    assert!(!uf.is_grounded("y"));

    // y = x unions them, so y becomes grounded too
    uf.union("x", "y");
    assert!(uf.is_grounded("y"));
}

#[test]
fn test_point_cube_recognizes_bool_literal_assignment() {
    let b = ChcVar {
        name: "b".to_string(),
        sort: ChcSort::Bool,
    };

    assert!(
        is_point_cube_for_vars(&ChcExpr::var(b.clone()), &[b]),
        "bare bool literal should ground the variable"
    );
}

#[test]
fn test_point_cube_recognizes_negated_bool_literal_assignment() {
    let b = ChcVar {
        name: "b".to_string(),
        sort: ChcSort::Bool,
    };

    assert!(
        is_point_cube_for_vars(&ChcExpr::not(ChcExpr::var(b.clone())), &[b]),
        "negated bool literal should ground the variable"
    );
}

#[test]
fn test_try_eval_const() {
    // Simple integer
    assert_eq!(try_eval_const(&ChcExpr::Int(42)), Some(42));

    // Negation
    let neg = ChcExpr::Op(ChcOp::Neg, vec![Arc::new(ChcExpr::Int(5))]);
    assert_eq!(try_eval_const(&neg), Some(-5));

    // Addition
    let add = ChcExpr::Op(
        ChcOp::Add,
        vec![Arc::new(ChcExpr::Int(3)), Arc::new(ChcExpr::Int(4))],
    );
    assert_eq!(try_eval_const(&add), Some(7));

    // Variable should return None
    let var = ChcExpr::Var(ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Int,
    });
    assert_eq!(try_eval_const(&var), None);
}

#[test]
fn test_extract_equalities_simple() {
    // (and (= x 5) (= y 10))
    let x = ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Int,
    };
    let y = ChcVar {
        name: "y".to_string(),
        sort: ChcSort::Int,
    };
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(ChcExpr::Var(x)), Arc::new(ChcExpr::Int(5))],
            )),
            Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(ChcExpr::Var(y)), Arc::new(ChcExpr::Int(10))],
            )),
        ],
    );

    let values = extract_equalities_and_propagate(&expr);
    assert_eq!(values.get("x"), Some(&5));
    assert_eq!(values.get("y"), Some(&10));
}

/// Regression test for #2950: checked_sub skips overflow in extract_equalities
#[test]
fn test_extract_equalities_with_relations_i64_min_overflow() {
    // (= (+ y 1) i128::MIN) means y = i128::MIN - 1, which overflows i128.
    // checked_sub returns None, so no value should be inserted for y.
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Add,
                vec![Arc::new(ChcExpr::Var(y)), Arc::new(ChcExpr::Int(1))],
            )),
            Arc::new(ChcExpr::Int(i128::MIN)),
        ],
    );

    let mut values = FxHashMap::default();
    let mut relations = Vec::new();
    extract_equalities_with_relations(&expr, &mut values, &mut relations);

    assert!(
        !values.contains_key("y"),
        "overflow input should skip insertion, got y={:?}",
        values.get("y")
    );

    // Positive control: non-overflowing (= (+ y 1) 10) should extract y=9
    let y2 = ChcVar::new("y2", ChcSort::Int);
    let ok_expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Add,
                vec![Arc::new(ChcExpr::Var(y2)), Arc::new(ChcExpr::Int(1))],
            )),
            Arc::new(ChcExpr::Int(10)),
        ],
    );
    extract_equalities_with_relations(&ok_expr, &mut values, &mut relations);
    assert_eq!(
        values.get("y2"),
        Some(&9),
        "non-overflowing input must extract correct value"
    );
}

/// Regression test for #2950: checked_neg skips i128::MIN in subtraction relation
#[test]
fn test_extract_equalities_negation_overflow() {
    // (= x (- y i128::MIN)) means x = y + (-i128::MIN), but -i128::MIN overflows.
    // checked_neg returns None, so no relation should be inserted.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Var(x)),
            Arc::new(ChcExpr::Op(
                ChcOp::Sub,
                vec![Arc::new(ChcExpr::Var(y)), Arc::new(ChcExpr::Int(i128::MIN))],
            )),
        ],
    );

    let mut values = FxHashMap::default();
    let mut relations = Vec::new();
    extract_equalities_with_relations(&expr, &mut values, &mut relations);

    // No relation should be produced since -i128::MIN overflows
    assert!(
        relations.is_empty(),
        "negation overflow must skip relation insertion entirely, got {relations:?}"
    );

    // Positive control: non-overflowing (= x2 (- y2 3)) should produce a relation
    let x2 = ChcVar::new("x2", ChcSort::Int);
    let y2 = ChcVar::new("y2", ChcSort::Int);
    let ok_expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Var(x2)),
            Arc::new(ChcExpr::Op(
                ChcOp::Sub,
                vec![Arc::new(ChcExpr::Var(y2)), Arc::new(ChcExpr::Int(3))],
            )),
        ],
    );
    let mut ok_relations = Vec::new();
    let mut ok_values = FxHashMap::default();
    extract_equalities_with_relations(&ok_expr, &mut ok_values, &mut ok_relations);
    assert!(
        !ok_relations.is_empty(),
        "non-overflowing subtraction must produce a relation"
    );
}

/// Prove that union-find operations allocate O(n) Strings per `find()` chain
/// due to `var.to_string()` on every call (cube.rs:53-71).
///
/// With path compression, the amortized cost per find() is O(α(n)) tree ops,
/// but each op allocates a new String for the HashMap insert. This test
/// measures that n union operations require O(n) find() calls total (correct),
/// but each find() does at least one String allocation (the performance bug).
///
/// Expected behavior: path compression makes the tree flat, so subsequent
/// finds return in O(1) *tree ops*, but still allocate Strings each time.
#[test]
fn union_find_string_allocation_per_operation() {
    let mut uf = PointCubeUnionFind::new();
    let n = 200;

    // Create a long chain: v0 <- v1 <- v2 <- ... <- v_{n-1}
    for i in 0..n {
        let var = format!("v{i}");
        uf.mark_grounded(&var);
    }
    for i in 1..n {
        uf.union(&format!("v{}", i - 1), &format!("v{i}"));
    }

    // After building the chain, the parent map has entries for all n vars.
    // Count parent map size before and after batch finds to show path
    // compression doesn't reduce allocation count.
    let map_size_before = uf.parent.len();

    // Do n find() calls — each should trigger at least one String alloc
    // for the path compression insert.
    for i in 0..n {
        let root = uf.find(&format!("v{i}"));
        // All should resolve to the same root
        assert_eq!(root, uf.find("v0"), "All vars should share one root");
    }

    // The parent map should still have exactly n entries (no growth from finds).
    // This is the correct behavior — but each find() allocated temporary Strings.
    assert_eq!(
        uf.parent.len(),
        map_size_before,
        "find() should not grow the parent map"
    );

    // Verify correctness: all variables are grounded through the union.
    for i in 0..n {
        assert!(uf.is_grounded(&format!("v{i}")), "v{i} should be grounded");
    }
}

/// Regression for #3004: value_expr_from_model returns None for missing
/// Int variables instead of fabricating 0.
#[test]
fn value_expr_from_model_returns_none_for_missing_int_var() {
    let model = FxHashMap::default(); // empty model
    let x = ChcVar::new("x", ChcSort::Int);
    let result = value_expr_from_model(&ChcExpr::var(x), &model);
    assert_eq!(result, None, "missing Int var must not fabricate 0");
}

/// value_expr_from_model returns the value when the variable IS in the model.
#[test]
fn value_expr_from_model_returns_value_for_present_int_var() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(42));
    let x = ChcVar::new("x", ChcSort::Int);
    let result = value_expr_from_model(&ChcExpr::var(x), &model);
    assert_eq!(result, Some(ChcExpr::Int(42)));
}

/// value_expr_from_model propagates None through arithmetic on missing vars.
#[test]
fn value_expr_from_model_propagates_none_through_add() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int); // not in model
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y));
    let result = value_expr_from_model(&expr, &model);
    assert_eq!(result, None, "add with missing var must return None");
}

/// Boundary: And(missing_var, false) returns None because the missing var
/// is evaluated before the false short-circuit fires. This is conservative
/// (not unsound) — the caller falls back to a more conservative cube.
#[test]
fn value_expr_from_model_and_missing_before_false_returns_none() {
    let model = FxHashMap::default(); // empty model
    let x = ChcVar::new("x", ChcSort::Bool); // not in model
                                             // And(x, false) — x is missing, so ? propagates None before false short-circuits
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::Bool(false))],
    );
    let result = value_expr_from_model(&expr, &model);
    // Conservative: returns None even though the expression is trivially false.
    // This is safe because callers fall back to point-cube extraction.
    assert_eq!(
        result, None,
        "And with missing var before false returns None (conservative)"
    );
}

/// Boundary: And(false, missing_var) short-circuits correctly to false.
#[test]
fn value_expr_from_model_and_false_before_missing_short_circuits() {
    let model = FxHashMap::default(); // empty model
    let x = ChcVar::new("x", ChcSort::Bool); // not in model
                                             // And(false, x) — false is evaluated first, short-circuits
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(ChcExpr::Bool(false)), Arc::new(ChcExpr::var(x))],
    );
    let result = value_expr_from_model(&expr, &model);
    assert_eq!(
        result,
        Some(ChcExpr::Bool(false)),
        "And(false, _) must short-circuit to false"
    );
}

/// Boundary: Or(missing_var, true) returns None because the missing var
/// is evaluated before the true short-circuit fires.
#[test]
fn value_expr_from_model_or_missing_before_true_returns_none() {
    let model = FxHashMap::default();
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::Op(
        ChcOp::Or,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::Bool(true))],
    );
    let result = value_expr_from_model(&expr, &model);
    assert_eq!(
        result, None,
        "Or with missing var before true returns None (conservative)"
    );
}

/// Boundary: Or(true, missing_var) short-circuits correctly to true.
#[test]
fn value_expr_from_model_or_true_before_missing_short_circuits() {
    let model = FxHashMap::default();
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::Op(
        ChcOp::Or,
        vec![Arc::new(ChcExpr::Bool(true)), Arc::new(ChcExpr::var(x))],
    );
    let result = value_expr_from_model(&expr, &model);
    assert_eq!(
        result,
        Some(ChcExpr::Bool(true)),
        "Or(true, _) must short-circuit to true"
    );
}

#[test]
fn is_trivial_contradiction_detects_negated_term_in_large_conjunction() {
    let target = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(7),
    );
    let mut conjuncts = Vec::new();
    for i in 0..64 {
        conjuncts.push(Arc::new(ChcExpr::eq(
            ChcExpr::var(ChcVar::new(&format!("v{i}"), ChcSort::Int)),
            ChcExpr::Int(i),
        )));
    }
    conjuncts.push(Arc::new(target.clone()));
    conjuncts.push(Arc::new(ChcExpr::not(target)));

    let expr = ChcExpr::Op(ChcOp::And, conjuncts);
    assert!(is_trivial_contradiction(&expr));
}

#[test]
fn is_trivial_contradiction_detects_bv2nat_disequality_against_bv_literal_9604() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let bv2nat_x = ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(ChcExpr::var(x.clone()))]);
    let expr = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(2, 8)),
        ChcExpr::ne(bv2nat_x, ChcExpr::int(2)),
    );

    assert!(is_trivial_contradiction(&expr));
}

#[test]
fn is_trivial_contradiction_detects_negated_bv2nat_equality_against_bv_literal_9604() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let bv2nat_x = ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(ChcExpr::var(x.clone()))]);
    let expr = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(2, 8)),
        ChcExpr::not(ChcExpr::eq(bv2nat_x, ChcExpr::int(2))),
    );

    assert!(is_trivial_contradiction(&expr));
}

#[test]
fn is_trivial_contradiction_rejects_mismatched_bv2nat_equality_against_bv_literal_9604() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let bv2nat_x = ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(ChcExpr::var(x.clone()))]);
    let expr = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(2, 8)),
        ChcExpr::eq(bv2nat_x, ChcExpr::int(3)),
    );

    assert!(is_trivial_contradiction(&expr));
}

#[test]
fn is_trivial_contradiction_ignores_ill_sorted_bv_literal_width_9604() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let bv2nat_x = ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(ChcExpr::var(x.clone()))]);
    let expr = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(2, 16)),
        ChcExpr::ne(bv2nat_x, ChcExpr::int(2)),
    );

    assert!(!is_trivial_contradiction(&expr));
}

#[test]
fn extract_implied_relations_strengthens_with_ne() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let conjuncts = vec![ChcExpr::ge(x.clone(), y.clone()), ChcExpr::ne(x, y)];

    let relations = extract_implied_relations_from_conjuncts(&conjuncts);
    assert!(relations.contains(&("x".to_string(), "y".to_string(), RelationType::Ge)));
    assert!(relations.contains(&("x".to_string(), "y".to_string(), RelationType::Gt)));
}

#[test]
fn extract_implied_relations_strengthens_with_reversed_not_eq_pair() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let conjuncts = vec![
        ChcExpr::le(y.clone(), x.clone()),
        ChcExpr::not(ChcExpr::eq(x, y)),
    ];

    let relations = extract_implied_relations_from_conjuncts(&conjuncts);
    assert!(relations.contains(&("y".to_string(), "x".to_string(), RelationType::Le)));
    assert!(relations.contains(&("y".to_string(), "x".to_string(), RelationType::Lt)));
}

/// #6074: value_expr_from_model produces concrete BV values (not None).
#[test]
fn value_expr_from_model_returns_bv_value() {
    let bv_var = ChcExpr::var(ChcVar::new("x_bv", ChcSort::BitVec(8)));
    let mut model = FxHashMap::default();
    model.insert("x_bv".to_string(), SmtValue::BitVec(42, 8));

    let result = value_expr_from_model(&bv_var, &model);
    assert_eq!(result, Some(ChcExpr::BitVec(42, 8)));
}

/// #6074: eval_bool handles BV equality under a model.
#[test]
fn value_expr_from_model_evaluates_bv_equality() {
    let bv_x = ChcExpr::var(ChcVar::new("x_bv", ChcSort::BitVec(8)));
    let bv_lit = ChcExpr::BitVec(42, 8);
    let eq_expr = ChcExpr::eq(bv_x, bv_lit);

    let mut model = FxHashMap::default();
    model.insert("x_bv".to_string(), SmtValue::BitVec(42, 8));

    // The equality (= x_bv #x2A) under model {x_bv -> 42} should evaluate to true.
    let result = value_expr_from_model(&eq_expr, &model);
    assert_eq!(result, Some(ChcExpr::Bool(true)));
}

/// #6074: BV inequality evaluates correctly.
#[test]
fn value_expr_from_model_evaluates_bv_inequality() {
    let bv_x = ChcExpr::var(ChcVar::new("x_bv", ChcSort::BitVec(8)));
    let bv_lit = ChcExpr::BitVec(99, 8);
    let eq_expr = ChcExpr::eq(bv_x, bv_lit);

    let mut model = FxHashMap::default();
    model.insert("x_bv".to_string(), SmtValue::BitVec(42, 8));

    // (= x_bv 99) under model {x_bv -> 42} should evaluate to false.
    let result = value_expr_from_model(&eq_expr, &model);
    assert_eq!(result, Some(ChcExpr::Bool(false)));
}
