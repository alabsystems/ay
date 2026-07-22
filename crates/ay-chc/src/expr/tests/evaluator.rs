// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::smt::SmtValue;

#[test]
fn overflow_add_returns_none() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Add,
        vec![Arc::new(ChcExpr::Int(i128::MAX)), Arc::new(ChcExpr::Int(1))],
    );
    assert_eq!(evaluate_expr(&expr, &model), None);
    // i128-lockstep: the old i64 boundary now evaluates exactly.
    let in_range = ChcExpr::Op(
        ChcOp::Add,
        vec![
            Arc::new(ChcExpr::Int(i128::from(i64::MAX))),
            Arc::new(ChcExpr::Int(1)),
        ],
    );
    assert_eq!(
        evaluate_expr(&in_range, &model),
        Some(SmtValue::Int(i128::from(i64::MAX) + 1))
    );
}

#[test]
fn overflow_sub_returns_none() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Sub,
        vec![Arc::new(ChcExpr::Int(i128::MIN)), Arc::new(ChcExpr::Int(1))],
    );
    assert_eq!(evaluate_expr(&expr, &model), None);
}

#[test]
fn overflow_mul_returns_none() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::Int(i128::MAX)), Arc::new(ChcExpr::Int(2))],
    );
    assert_eq!(evaluate_expr(&expr, &model), None);
}

#[test]
fn neg_min_returns_none() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(ChcOp::Neg, vec![Arc::new(ChcExpr::Int(i128::MIN))]);
    assert_eq!(evaluate_expr(&expr, &model), None);
}

#[test]
fn unary_sub_min_returns_none() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(ChcOp::Sub, vec![Arc::new(ChcExpr::Int(i128::MIN))]);
    assert_eq!(evaluate_expr(&expr, &model), None);
}

#[test]
fn div_euclidean_semantics() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::Int(-3)), Arc::new(ChcExpr::Int(2))],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Int(-2)));
}

#[test]
fn mod_euclidean_semantics() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(-3)), Arc::new(ChcExpr::Int(2))],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Int(1)));
}

#[test]
fn mod_positive_divisor_positive_dividend() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(7)), Arc::new(ChcExpr::Int(3))],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Int(1)));
}

#[test]
fn div_by_zero_returns_zero() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::Int(5)), Arc::new(ChcExpr::Int(0))],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Int(0)));
}

#[test]
fn mod_by_zero_returns_dividend() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::Int(5)), Arc::new(ChcExpr::Int(0))],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Int(5)));
}

#[test]
fn and_short_circuit_false() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::Bool(false)),
            Arc::new(ChcExpr::Var(ChcVar::new("unknown", ChcSort::Bool))),
        ],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(false)));
}

#[test]
fn or_short_circuit_true() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Or,
        vec![
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::Var(ChcVar::new("unknown", ChcSort::Bool))),
        ],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
}

#[test]
fn implies_false_antecedent() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Implies,
        vec![
            Arc::new(ChcExpr::Bool(false)),
            Arc::new(ChcExpr::Var(ChcVar::new("unknown", ChcSort::Bool))),
        ],
    );
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
}

#[test]
fn variable_lookup() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(42));
    let expr = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Int(42)));
}

#[test]
fn missing_variable_returns_none() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    assert_eq!(evaluate_expr(&expr, &model), None);
}

#[test]
fn bv_literal_evaluates() {
    let model = FxHashMap::default();
    let expr = ChcExpr::BitVec(0xFF, 8);
    assert_eq!(
        evaluate_expr(&expr, &model),
        Some(SmtValue::BitVec(0xFF, 8))
    );
}

#[test]
fn bv_literal_masks_to_width() {
    let model = FxHashMap::default();
    let expr = ChcExpr::BitVec(0x1FF, 8);
    assert_eq!(
        evaluate_expr(&expr, &model),
        Some(SmtValue::BitVec(0xFF, 8))
    );
}

#[test]
fn bv_add_basic() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::BitVec(3, 8));
    model.insert("y".to_string(), SmtValue::BitVec(5, 8));
    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))));
    let y = Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8))));
    let expr = ChcExpr::Op(ChcOp::BvAdd, vec![x, y]);
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::BitVec(8, 8)));
}

#[test]
fn bv_add_overflow_wraps() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::BitVec(200, 8));
    model.insert("y".to_string(), SmtValue::BitVec(100, 8));
    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))));
    let y = Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8))));
    let expr = ChcExpr::Op(ChcOp::BvAdd, vec![x, y]);
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::BitVec(44, 8)));
}

#[test]
fn bv_signed_cmp() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::BitVec(0xFF, 8));
    model.insert("y".to_string(), SmtValue::BitVec(1, 8));
    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))));
    let y = Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8))));
    let expr = ChcExpr::Op(ChcOp::BvSLt, vec![x, y]);
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
}

#[test]
fn bv_concat_and_extract() {
    let model = FxHashMap::default();
    let a = Arc::new(ChcExpr::BitVec(0xAB, 8));
    let b = Arc::new(ChcExpr::BitVec(0xCD, 8));
    let concat = ChcExpr::Op(ChcOp::BvConcat, vec![a, b]);
    assert_eq!(
        evaluate_expr(&concat, &model),
        Some(SmtValue::BitVec(0xABCD, 16))
    );
    let val = Arc::new(ChcExpr::BitVec(0xABCD, 16));
    let extract = ChcExpr::Op(ChcOp::BvExtract(15, 8), vec![val]);
    assert_eq!(
        evaluate_expr(&extract, &model),
        Some(SmtValue::BitVec(0xAB, 8))
    );
}

#[test]
fn bv_sign_extend() {
    let model = FxHashMap::default();
    let val = Arc::new(ChcExpr::BitVec(0xFF, 8));
    let expr = ChcExpr::Op(ChcOp::BvSignExtend(8), vec![val]);
    assert_eq!(
        evaluate_expr(&expr, &model),
        Some(SmtValue::BitVec(0xFFFF, 16))
    );
}

#[test]
fn bv_neg() {
    let model = FxHashMap::default();
    let val = Arc::new(ChcExpr::BitVec(1, 8));
    let expr = ChcExpr::Op(ChcOp::BvNeg, vec![val]);
    assert_eq!(
        evaluate_expr(&expr, &model),
        Some(SmtValue::BitVec(0xFF, 8))
    );
}

#[test]
fn bv_variable_lookup() {
    let mut model = FxHashMap::default();
    model.insert("bv_var".to_string(), SmtValue::BitVec(42, 16));
    let expr = ChcExpr::Var(ChcVar::new("bv_var", ChcSort::BitVec(16)));
    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::BitVec(42, 16)));
}

#[test]
fn substitute_empty_map_preserves_arc_sharing() {
    let x = Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::Int)));
    let y = Arc::new(ChcExpr::var(ChcVar::new("y", ChcSort::Int)));
    let z = Arc::new(ChcExpr::var(ChcVar::new("z", ChcSort::Int)));
    let inner = Arc::new(ChcExpr::Op(ChcOp::Add, vec![y, z]));
    let root = ChcExpr::Op(ChcOp::Add, vec![x, inner.clone()]);

    let empty_map: FxHashMap<&ChcVar, &ChcExpr> = Default::default();
    let result = root.substitute_map(&empty_map);

    assert_eq!(root, result);

    match &result {
        ChcExpr::Op(ChcOp::Add, args) => {
            assert!(
                Arc::ptr_eq(&args[1], &inner),
                "substitute_map with empty map should preserve inner node sharing"
            );
        }
        _ => panic!("expected Op(Add, _)"),
    }
}

#[test]
fn simplify_constants_reconstructs_already_simple_expr() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let geq_x = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(x), Arc::new(ChcExpr::Int(0))]);
    let geq_y = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(y), Arc::new(ChcExpr::Int(0))]);
    let conj = ChcExpr::and(geq_x, geq_y);

    let result = conj.simplify_constants();
    assert_eq!(conj, result, "simplify_constants should preserve semantics");
}

#[test]
fn iterative_drop_deep_expr_chain_no_stack_overflow() {
    const DEPTH: usize = 100_000;
    let mut expr = ChcExpr::Int(0);
    for i in 0..DEPTH {
        let var = ChcExpr::var(ChcVar::new(format!("x{i}"), ChcSort::Int));
        expr = ChcExpr::Op(ChcOp::Add, vec![Arc::new(var), Arc::new(expr)]);
    }
    ChcExpr::iterative_drop(expr);
}

#[test]
fn iterative_drop_deep_const_array_chain_no_stack_overflow() {
    const DEPTH: usize = 50_000;
    let mut expr = ChcExpr::Int(42);
    for _ in 0..DEPTH {
        expr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(expr));
    }
    ChcExpr::iterative_drop(expr);
}

#[test]
fn iterative_drop_shared_arcs_does_not_double_free() {
    let shared = Arc::new(ChcExpr::Int(1));
    let expr1 = ChcExpr::Op(ChcOp::Add, vec![shared.clone(), shared.clone()]);
    let expr2 = ChcExpr::Op(ChcOp::Add, vec![shared.clone(), Arc::new(ChcExpr::Int(2))]);
    assert_eq!(Arc::strong_count(&shared), 4);
    ChcExpr::iterative_drop(expr1);
    assert_eq!(Arc::strong_count(&shared), 2);
    ChcExpr::iterative_drop(expr2);
    assert_eq!(Arc::strong_count(&shared), 1);
}

#[test]
fn iterative_drop_deep_expr_succeeds_on_small_stack() {
    const DEPTH: usize = 10_000;
    let mut expr = ChcExpr::Int(0);
    for i in 0..DEPTH {
        let var = ChcExpr::var(ChcVar::new(format!("x{i}"), ChcSort::Int));
        expr = ChcExpr::Op(ChcOp::Add, vec![Arc::new(var), Arc::new(expr)]);
    }

    let result = std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            ChcExpr::iterative_drop(expr);
        })
        .unwrap()
        .join();

    assert!(
        result.is_ok(),
        "iterative_drop on depth-{DEPTH} ChcExpr should succeed on 128KB stack"
    );
}
