// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::smt::SmtValue;

fn bv_var(name: &str, width: u32) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(width))))
}

fn assert_malformed_bv_sort_behavior(expr: ChcExpr, expected_release_sort: ChcSort) {
    let sort_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| expr.sort()));

    if cfg!(debug_assertions) {
        assert!(
            sort_result.is_err(),
            "malformed BV sort should trigger debug_assert in debug builds"
        );
        return;
    }

    let sort = sort_result.expect("malformed BV sort should fall back in release builds");
    assert_eq!(sort, expected_release_sort);
    assert_ne!(sort, ChcSort::BitVec(32));
}

#[test]
fn test_bv_concat_sort_adds_widths() {
    let a = bv_var("a", 8);
    let b = bv_var("b", 8);
    let concat = ChcExpr::Op(ChcOp::BvConcat, vec![a, b]);
    assert_eq!(concat.sort(), ChcSort::BitVec(16));
}

#[test]
fn test_bv_concat_sort_asymmetric_widths() {
    let a = bv_var("a", 32);
    let b = bv_var("b", 16);
    let concat = ChcExpr::Op(ChcOp::BvConcat, vec![a, b]);
    assert_eq!(concat.sort(), ChcSort::BitVec(48));
}

#[test]
fn test_bv_extract_sort_correct_width() {
    let a = bv_var("a", 32);
    let extract = ChcExpr::Op(ChcOp::BvExtract(7, 0), vec![a]);
    assert_eq!(extract.sort(), ChcSort::BitVec(8));
}

#[test]
fn test_bv_extract_sort_mid_range() {
    let a = bv_var("a", 32);
    let extract = ChcExpr::Op(ChcOp::BvExtract(15, 8), vec![a]);
    assert_eq!(extract.sort(), ChcSort::BitVec(8));
}

#[test]
fn test_bv_extract_sort_single_bit() {
    let a = bv_var("a", 8);
    let extract = ChcExpr::Op(ChcOp::BvExtract(3, 3), vec![a]);
    assert_eq!(extract.sort(), ChcSort::BitVec(1));
}

#[test]
fn test_bv_extract_sort_malformed_hi_lt_lo() {
    let a = bv_var("a", 8);
    let extract = ChcExpr::Op(ChcOp::BvExtract(2, 5), vec![a]);
    assert_eq!(extract.sort(), ChcSort::BitVec(1));
}

#[test]
fn test_bv_add_sort_empty_args_never_fabricates_32_bits() {
    let expr = ChcExpr::Op(ChcOp::BvAdd, vec![]);
    assert_malformed_bv_sort_behavior(expr, ChcSort::Int);
}

#[test]
fn test_bv_concat_sort_missing_rhs_never_fabricates_32_bits() {
    let expr = ChcExpr::Op(ChcOp::BvConcat, vec![bv_var("a", 8)]);
    assert_malformed_bv_sort_behavior(expr, ChcSort::BitVec(8));
}

#[test]
fn test_bv_rotate_left_sort_empty_args_never_fabricates_32_bits() {
    let expr = ChcExpr::Op(ChcOp::BvRotateLeft(3), vec![]);
    assert_malformed_bv_sort_behavior(expr, ChcSort::Int);
}

#[test]
fn test_bv_zero_extend_sort_non_bv_arg_never_fabricates_32_bits() {
    let expr = ChcExpr::Op(ChcOp::BvZeroExtend(4), vec![Arc::new(ChcExpr::Int(7))]);
    assert_malformed_bv_sort_behavior(expr, ChcSort::Int);
}

#[test]
fn test_bv_repeat_sort_non_bv_arg_never_fabricates_32_bits() {
    let expr = ChcExpr::Op(ChcOp::BvRepeat(3), vec![Arc::new(ChcExpr::Bool(true))]);
    assert_malformed_bv_sort_behavior(expr, ChcSort::Bool);
}

#[test]
fn test_contains_mixed_sort_eq_int_eq_bool() {
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let inner_eq = ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0));
    let mixed = ChcExpr::eq(ChcExpr::var(d), inner_eq);
    assert!(mixed.contains_mixed_sort_eq());
}

#[test]
fn test_contains_mixed_sort_eq_bool_eq_bool() {
    let d = ChcVar::new("D", ChcSort::Bool);
    let e = ChcVar::new("E", ChcSort::Int);
    let inner_eq = ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0));
    let not_mixed = ChcExpr::eq(ChcExpr::var(d), inner_eq);
    assert!(!not_mixed.contains_mixed_sort_eq());
}

#[test]
fn test_contains_mixed_sort_eq_int_eq_int() {
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let same_sort = ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b));
    assert!(!same_sort.contains_mixed_sort_eq());
}

#[test]
fn test_eliminate_mixed_sort_eq_rewrites_int_eq_bool() {
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let inner_eq = ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0));
    let mixed = ChcExpr::eq(ChcExpr::var(d), inner_eq);

    let result = mixed.eliminate_mixed_sort_eq();

    match &result {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Var(v) if v.name == "D"));
            match args[1].as_ref() {
                ChcExpr::Op(ChcOp::Ite, ite_args) if ite_args.len() == 3 => {
                    assert_eq!(*ite_args[1], ChcExpr::Int(1));
                    assert_eq!(*ite_args[2], ChcExpr::Int(0));
                }
                other => panic!("Expected ITE, got: {other}"),
            }
        }
        other => panic!("Expected Eq, got: {other}"),
    }
}

#[test]
fn test_eliminate_mixed_sort_eq_preserves_bool_eq_bool() {
    let d = ChcVar::new("D", ChcSort::Bool);
    let e = ChcVar::new("E", ChcSort::Int);
    let inner_eq = ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0));
    let not_mixed = ChcExpr::eq(ChcExpr::var(d), inner_eq);

    let result = not_mixed.eliminate_mixed_sort_eq();
    assert!(!result.contains_ite());
}

#[test]
fn test_eliminate_mixed_sort_eq_nested() {
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);

    let mixed_eq = ChcExpr::eq(
        ChcExpr::var(a),
        ChcExpr::eq(ChcExpr::var(b), ChcExpr::int(5)),
    );
    let normal_eq = ChcExpr::eq(ChcExpr::var(c), ChcExpr::var(d));
    let conj = ChcExpr::and(mixed_eq, normal_eq);

    let result = conj.eliminate_mixed_sort_eq();
    assert!(
        result.contains_ite(),
        "Should have introduced ITE for the mixed-sort eq"
    );
}

#[test]
fn evaluate_eq_cross_sort_int_eq_bool_true() {
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let expr = ChcExpr::eq(
        ChcExpr::var(d),
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0)),
    );
    let mut model = FxHashMap::default();
    model.insert("D".to_string(), SmtValue::Int(1));
    model.insert("E".to_string(), SmtValue::Int(0));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(result, Some(SmtValue::Bool(true)));
}

#[test]
fn evaluate_eq_cross_sort_int_eq_bool_false() {
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let expr = ChcExpr::eq(
        ChcExpr::var(d),
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0)),
    );
    let mut model = FxHashMap::default();
    model.insert("D".to_string(), SmtValue::Int(0));
    model.insert("E".to_string(), SmtValue::Int(0));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(result, Some(SmtValue::Bool(false)));
}

#[test]
fn evaluate_eq_cross_sort_int_zero_eq_bool_false() {
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let expr = ChcExpr::eq(
        ChcExpr::var(d),
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0)),
    );
    let mut model = FxHashMap::default();
    model.insert("D".to_string(), SmtValue::Int(0));
    model.insert("E".to_string(), SmtValue::Int(5));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(result, Some(SmtValue::Bool(true)));
}

#[test]
fn evaluate_ne_cross_sort() {
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let expr = ChcExpr::Op(
        ChcOp::Ne,
        vec![
            Arc::new(ChcExpr::var(d)),
            Arc::new(ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0))),
        ],
    );
    let mut model = FxHashMap::default();
    model.insert("D".to_string(), SmtValue::Int(1));
    model.insert("E".to_string(), SmtValue::Int(0));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(result, Some(SmtValue::Bool(false)));
}

#[test]
fn evaluate_eq_same_sort_unchanged() {
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let expr = ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b));
    let mut model = FxHashMap::default();
    model.insert("A".to_string(), SmtValue::Int(5));
    model.insert("B".to_string(), SmtValue::Int(5));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(result, Some(SmtValue::Bool(true)));

    model.insert("B".to_string(), SmtValue::Int(3));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(result, Some(SmtValue::Bool(false)));
}

#[test]
fn contains_uf_apps_literal_false() {
    assert!(!ChcExpr::Bool(true).contains_uf_apps());
    assert!(!ChcExpr::Int(42).contains_uf_apps());
    assert!(!ChcExpr::Real(3, 2).contains_uf_apps());
    assert!(!ChcExpr::BitVec(0xFF, 8).contains_uf_apps());
}

#[test]
fn contains_uf_apps_var_false() {
    let x = ChcVar::new("x", ChcSort::Int);
    assert!(!ChcExpr::var(x).contains_uf_apps());
}

#[test]
fn contains_uf_apps_func_app_true() {
    let f_x = ChcExpr::FuncApp(
        "f".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Int(1))],
    );
    assert!(f_x.contains_uf_apps());
}

#[test]
fn contains_uf_apps_nested_in_op_true() {
    let f_x = ChcExpr::FuncApp(
        "__bv2int_and_1_w32".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Int(1)), Arc::new(ChcExpr::Int(2))],
    );
    let expr = ChcExpr::add(f_x, ChcExpr::Int(3));
    assert!(expr.contains_uf_apps());
}

#[test]
fn contains_uf_apps_pure_arithmetic_false() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(
        ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1)),
        ChcExpr::Int(2),
    );
    assert!(!expr.contains_uf_apps());
}

#[test]
fn contains_uf_apps_nested_in_predicate_app_true() {
    let f_x = ChcExpr::FuncApp(
        "g".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Int(0))],
    );
    let pred = ChcExpr::predicate_app("P", PredicateId(0), vec![f_x]);
    assert!(pred.contains_uf_apps());
}

#[test]
fn contains_uf_apps_predicate_app_without_func_false() {
    let pred = ChcExpr::predicate_app("P", PredicateId(0), vec![ChcExpr::Int(5)]);
    assert!(!pred.contains_uf_apps());
}

#[test]
fn contains_uf_apps_const_array_marker_false() {
    assert!(!ChcExpr::ConstArrayMarker(ChcSort::Int).contains_uf_apps());
    assert!(!ChcExpr::IsTesterMarker("tester_0".to_string()).contains_uf_apps());
}

#[test]
fn contains_array_ops_literal_false() {
    assert!(!ChcExpr::Bool(false).contains_array_ops());
    assert!(!ChcExpr::Int(0).contains_array_ops());
}

#[test]
fn scan_features_marks_bv_equalities_6614() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 8));

    let features = expr.scan_features();

    assert!(features.has_bv);
}

#[test]
fn scan_features_leaves_pure_arith_bv_flag_clear_6614() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(1));

    let features = expr.scan_features();

    assert!(!features.has_bv);
}

#[test]
fn contains_array_ops_select_true() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::Op(
        ChcOp::Select,
        vec![Arc::new(ChcExpr::var(a)), Arc::new(ChcExpr::Int(0))],
    );
    assert!(expr.contains_array_ops());
}

#[test]
fn contains_array_ops_array_typed_var_true() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    assert!(ChcExpr::var(a).contains_array_ops());
}

#[test]
fn contains_array_ops_pure_int_op_false() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1));
    assert!(!expr.contains_array_ops());
}

#[test]
fn contains_array_ops_store_true() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::Op(
        ChcOp::Store,
        vec![
            Arc::new(ChcExpr::var(a)),
            Arc::new(ChcExpr::Int(0)),
            Arc::new(ChcExpr::Int(1)),
        ],
    );
    assert!(expr.contains_array_ops());
}

#[test]
fn contains_array_ops_const_array_true() {
    let expr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(0)));
    assert!(expr.contains_array_ops());
}

#[test]
fn contains_uf_apps_inside_const_array_value_true() {
    let f_val = ChcExpr::FuncApp(
        "f".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Int(0))],
    );
    let expr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(f_val));
    assert!(expr.contains_uf_apps());
}

#[test]
fn contains_uf_apps_const_array_no_func_false() {
    let expr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(0)));
    assert!(!expr.contains_uf_apps());
}

#[test]
fn simplify_array_row1_same_index_int() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let stored = ChcExpr::store(ChcExpr::var(a), ChcExpr::Int(0), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored, ChcExpr::Int(0));
    let result = sel.simplify_array_ops();
    assert_eq!(result, ChcExpr::Int(42));
}

#[test]
fn simplify_array_row1_same_index_bv() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8))),
    );
    let stored = ChcExpr::store(
        ChcExpr::var(a),
        ChcExpr::BitVec(0, 32),
        ChcExpr::BitVec(0xFF, 8),
    );
    let sel = ChcExpr::select(stored, ChcExpr::BitVec(0, 32));
    let result = sel.simplify_array_ops();
    assert_eq!(result, ChcExpr::BitVec(0xFF, 8));
}

#[test]
fn simplify_array_row2_different_index() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let stored = ChcExpr::store(ChcExpr::var(a.clone()), ChcExpr::Int(1), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored, ChcExpr::Int(0));
    let result = sel.simplify_array_ops();
    let expected = ChcExpr::select(ChcExpr::var(a), ChcExpr::Int(0));
    assert_eq!(result, expected);
}

#[test]
fn simplify_array_row2_nested_to_row1() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let inner_store = ChcExpr::store(ChcExpr::var(a), ChcExpr::Int(0), ChcExpr::Int(10));
    let outer_store = ChcExpr::store(inner_store, ChcExpr::Int(1), ChcExpr::Int(20));
    let sel = ChcExpr::select(outer_store, ChcExpr::Int(0));
    let result = sel.simplify_array_ops();
    assert_eq!(result, ChcExpr::Int(10));
}

#[test]
fn simplify_array_const_array_select() {
    let const_arr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(42)));
    let sel = ChcExpr::select(const_arr, ChcExpr::Int(5));
    let result = sel.simplify_array_ops();
    assert_eq!(result, ChcExpr::Int(42));
}

#[test]
fn simplify_array_store_then_const_array() {
    let const_arr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(0)));
    let stored = ChcExpr::store(const_arr, ChcExpr::Int(3), ChcExpr::Int(99));
    let sel = ChcExpr::select(stored, ChcExpr::Int(5));
    let result = sel.simplify_array_ops();
    assert_eq!(result, ChcExpr::Int(0));
}

#[test]
fn simplify_array_symbolic_index_no_reduction() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let stored = ChcExpr::store(ChcExpr::var(a), ChcExpr::var(x), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored.clone(), ChcExpr::var(y.clone()));
    let result = sel.simplify_array_ops();
    let expected = ChcExpr::select(stored, ChcExpr::var(y));
    assert_eq!(result, expected);
}

#[test]
fn simplify_array_symbolic_same_var_row1() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let x = ChcVar::new("x", ChcSort::Int);
    let stored = ChcExpr::store(ChcExpr::var(a), ChcExpr::var(x.clone()), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored, ChcExpr::var(x));
    let result = sel.simplify_array_ops();
    assert_eq!(result, ChcExpr::Int(42));
}

/// Memoization regression (model-checker-consumer wishlist item 4c): a deeply shared `Arc`
/// DAG must be simplified once per distinct subtree, not once per path.
/// Pre-memo, the 1M-node budget exhausted after ~2^20 of the 2^40 paths and
/// the rightmost `select(store(a, 0, 1), 0)` survived unsimplified; with the
/// pointer-identity memo (the `simplify_constants` #7060 pattern) every path
/// reaches the folded leaf in O(depth) work.
#[test]
fn simplify_array_ops_memoizes_shared_dag() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let stored = ChcExpr::store(ChcExpr::var(a), ChcExpr::Int(0), ChcExpr::Int(1));
    let leaf = ChcExpr::select(stored, ChcExpr::Int(0));
    let mut node = Arc::new(leaf);
    for _ in 0..40 {
        node = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&node), Arc::clone(&node)],
        ));
    }

    let start = std::time::Instant::now();
    let result = node.simplify_array_ops();
    assert!(
        start.elapsed() < std::time::Duration::from_secs(10),
        "shared-DAG simplify_array_ops should be linear in distinct subtrees"
    );

    // Probe the RIGHTMOST descent: the unmemoized DFS simplified the
    // leftmost paths first and ran out of budget long before the rightmost
    // leaf, so this is the discriminating path.
    let mut cursor: &ChcExpr = &result;
    while let ChcExpr::Op(ChcOp::Add, args) = cursor {
        cursor = args.last().expect("Add node has children").as_ref();
    }
    assert_eq!(
        *cursor,
        ChcExpr::Int(1),
        "every shared path must reach the ROW1-folded stored value"
    );
}

#[test]
fn simplify_array_inside_equality() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let stored = ChcExpr::store(ChcExpr::var(a), ChcExpr::Int(0), ChcExpr::Int(42));
    let sel = ChcExpr::select(stored, ChcExpr::Int(0));
    let eq_expr = ChcExpr::eq(sel, ChcExpr::Int(42));
    let result = eq_expr.simplify_array_ops();
    let expected = ChcExpr::eq(ChcExpr::Int(42), ChcExpr::Int(42));
    assert_eq!(result, expected);
}

#[test]
fn simplify_array_bv_model_checker_consumer_style() {
    let v = ChcVar::new(
        "v",
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
    );
    let stored = ChcExpr::store(ChcExpr::var(v), ChcExpr::BitVec(0, 32), ChcExpr::Bool(true));
    let sel = ChcExpr::select(stored, ChcExpr::BitVec(0, 32));
    let result = sel.simplify_array_ops();
    assert_eq!(result, ChcExpr::Bool(true));
}

#[test]
fn simplify_array_no_array_ops_unchanged() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1));
    let result = expr.simplify_array_ops();
    assert_eq!(result, expr);
}
