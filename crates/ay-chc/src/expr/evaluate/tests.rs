// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector};
// --- eval_array_select ---

#[test]
fn test_eval_array_select_const_array() {
    // ConstArray(42) → select at any index returns 42
    let arr = SmtValue::ConstArray(Box::new(SmtValue::Int(42)));
    let idx = SmtValue::Int(0);
    assert_eq!(eval_array_select(&arr, &idx), Some(SmtValue::Int(42)));
    let idx2 = SmtValue::Int(999);
    assert_eq!(eval_array_select(&arr, &idx2), Some(SmtValue::Int(42)));
}

#[test]
fn test_eval_array_select_basic() {
    // store(const(0), 5, 100) → select at 5 returns 100
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(5), SmtValue::Int(100))],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(5)),
        Some(SmtValue::Int(100))
    );
}

#[test]
fn test_eval_array_select_different_index() {
    // store(const(0), 5, 100) → select at 3 returns default 0
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(5), SmtValue::Int(100))],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(3)),
        Some(SmtValue::Int(0))
    );
}

#[test]
fn test_eval_array_select_nested_store() {
    // store(store(const(0), 1, 10), 2, 20) → select at 1 returns 10, at 2 returns 20
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![
            (SmtValue::Int(1), SmtValue::Int(10)),
            (SmtValue::Int(2), SmtValue::Int(20)),
        ],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(1)),
        Some(SmtValue::Int(10))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(2)),
        Some(SmtValue::Int(20))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(3)),
        Some(SmtValue::Int(0))
    );
}

#[test]
fn test_eval_array_select_last_store_wins() {
    // store(store(const(0), 1, 10), 1, 20) → last store at idx 1 wins
    // After dedup in eval_array_store, there should be only one entry.
    // But if entries are manually constructed with duplicates, reverse order wins.
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![
            (SmtValue::Int(1), SmtValue::Int(10)),
            (SmtValue::Int(1), SmtValue::Int(20)),
        ],
    };
    // Reverse order scan: (1, 20) is found first → returns 20
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(1)),
        Some(SmtValue::Int(20))
    );
}

#[test]
fn test_eval_array_select_bv_index() {
    // Array(BV32, Bool) with BV-indexed entries
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![(SmtValue::BitVec(0, 32), SmtValue::Bool(true))],
    };
    assert_eq!(
        eval_array_select(&arr, &SmtValue::BitVec(0, 32)),
        Some(SmtValue::Bool(true))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::BitVec(1, 32)),
        Some(SmtValue::Bool(false))
    );
}

#[test]
fn test_eval_array_select_non_array_returns_none() {
    // Selecting from a non-array value returns None
    let not_arr = SmtValue::Int(42);
    assert_eq!(eval_array_select(&not_arr, &SmtValue::Int(0)), None);
}

#[test]
fn test_eval_array_select_opaque_key_returns_none_6289() {
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![(
            SmtValue::Opaque("__au_k0".to_string()),
            SmtValue::Bool(true),
        )],
    };
    assert_eq!(eval_array_select(&arr, &SmtValue::BitVec(0, 32)), None);
}

// --- eval_array_store ---

#[test]
fn test_eval_array_store_into_const_array() {
    // store(const(false), bv0, true) → ArrayMap with one entry
    let arr = SmtValue::ConstArray(Box::new(SmtValue::Bool(false)));
    let result = eval_array_store(arr, SmtValue::BitVec(0, 32), SmtValue::Bool(true));
    match &result {
        SmtValue::ArrayMap { default, entries } => {
            assert_eq!(**default, SmtValue::Bool(false));
            assert_eq!(entries.len(), 1);
            assert_eq!(entries[0], (SmtValue::BitVec(0, 32), SmtValue::Bool(true)));
        }
        _ => panic!("Expected ArrayMap, got {result:?}"),
    }
}

#[test]
fn test_eval_array_store_overwrite() {
    // store(store(const(0), 5, 10), 5, 20) → entry at 5 is overwritten to 20
    let arr = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(5), SmtValue::Int(10))],
    };
    let result = eval_array_store(arr, SmtValue::Int(5), SmtValue::Int(20));
    match &result {
        SmtValue::ArrayMap { entries, .. } => {
            assert_eq!(entries.len(), 1, "Overwrite should dedup: {entries:?}");
            assert_eq!(entries[0], (SmtValue::Int(5), SmtValue::Int(20)));
        }
        _ => panic!("Expected ArrayMap, got {result:?}"),
    }
}

#[test]
fn test_eval_array_store_multiple() {
    // store(store(const(0), 1, 10), 2, 20) → two entries
    let arr = SmtValue::ConstArray(Box::new(SmtValue::Int(0)));
    let arr = eval_array_store(arr, SmtValue::Int(1), SmtValue::Int(10));
    let arr = eval_array_store(arr, SmtValue::Int(2), SmtValue::Int(20));
    // Verify both entries via select
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(1)),
        Some(SmtValue::Int(10))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(2)),
        Some(SmtValue::Int(20))
    );
    assert_eq!(
        eval_array_select(&arr, &SmtValue::Int(3)),
        Some(SmtValue::Int(0))
    );
}

#[test]
fn test_eval_array_store_preserves_opaque_default_6289() {
    let arr = SmtValue::Opaque("@arr33".to_string());
    let stored = eval_array_store(arr, SmtValue::BitVec(0, 32), SmtValue::Bool(true));
    assert_eq!(
        eval_array_select(&stored, &SmtValue::BitVec(1, 32)),
        Some(SmtValue::Opaque("@arr33".to_string()))
    );
}

// --- evaluate_expr integration with arrays ---

use crate::expr::ChcVar;
use crate::ChcSort;
use std::sync::Arc;

/// Helper: wrap expr in Arc for Op arguments.
fn a(e: ChcExpr) -> Arc<ChcExpr> {
    Arc::new(e)
}

/// Helper: create a ChcVar with the given name and Int sort.
fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name.to_string(), ChcSort::Int)
}

#[test]
fn test_evaluate_expr_const_array() {
    let model = FxHashMap::default();
    let expr = ChcExpr::ConstArray(ChcSort::Int, a(ChcExpr::Int(42)));
    let result = evaluate_expr(&expr, &model);
    assert_eq!(
        result,
        Some(SmtValue::ConstArray(Box::new(SmtValue::Int(42))))
    );
}

#[test]
fn test_evaluate_expr_store_then_select() {
    let model = FxHashMap::default();
    // select(store(const(0), 5, 100), 5) → 100
    let const_arr = ChcExpr::ConstArray(ChcSort::Int, a(ChcExpr::Int(0)));
    let stored = ChcExpr::Op(
        ChcOp::Store,
        vec![a(const_arr), a(ChcExpr::Int(5)), a(ChcExpr::Int(100))],
    );
    let selected = ChcExpr::Op(ChcOp::Select, vec![a(stored), a(ChcExpr::Int(5))]);
    assert_eq!(evaluate_expr(&selected, &model), Some(SmtValue::Int(100)));
}

#[test]
fn test_evaluate_expr_select_miss() {
    let model = FxHashMap::default();
    // select(store(const(0), 5, 100), 3) → 0 (default)
    let const_arr = ChcExpr::ConstArray(ChcSort::Int, a(ChcExpr::Int(0)));
    let stored = ChcExpr::Op(
        ChcOp::Store,
        vec![a(const_arr), a(ChcExpr::Int(5)), a(ChcExpr::Int(100))],
    );
    let selected = ChcExpr::Op(ChcOp::Select, vec![a(stored), a(ChcExpr::Int(3))]);
    assert_eq!(evaluate_expr(&selected, &model), Some(SmtValue::Int(0)));
}

#[test]
fn test_evaluate_expr_eq_with_opaque_value_returns_none_6289() {
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Opaque("__au_k0".to_string()));

    let expr = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32))),
        ChcExpr::BitVec(0, 32),
    );

    assert_eq!(evaluate_expr(&expr, &model), None);
}

#[test]
fn test_evaluate_expr_eq_array_overwrite_uses_last_store_wins_1753() {
    let lhs = ChcVar::new(
        "lhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let rhs = ChcVar::new(
        "rhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(ChcExpr::var(lhs.clone()), ChcExpr::var(rhs.clone()));

    let mut model = FxHashMap::default();
    model.insert(
        lhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![
                (SmtValue::Int(1), SmtValue::Int(10)),
                (SmtValue::Int(1), SmtValue::Int(20)),
            ],
        },
    );
    model.insert(
        rhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(1), SmtValue::Int(20))],
        },
    );

    assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
}

#[test]
fn test_evaluate_expr_nested_store_select() {
    let model = FxHashMap::default();
    // store(store(const(false), bv0, true), bv1, true)
    // then select at bv0 → true, select at bv2 → false (default)
    let const_arr = ChcExpr::ConstArray(ChcSort::BitVec(32), a(ChcExpr::Bool(false)));
    let s1 = ChcExpr::Op(
        ChcOp::Store,
        vec![
            a(const_arr),
            a(ChcExpr::BitVec(0, 32)),
            a(ChcExpr::Bool(true)),
        ],
    );
    let s2 = ChcExpr::Op(
        ChcOp::Store,
        vec![a(s1), a(ChcExpr::BitVec(1, 32)), a(ChcExpr::Bool(true))],
    );
    let sel0 = ChcExpr::Op(
        ChcOp::Select,
        vec![a(s2.clone()), a(ChcExpr::BitVec(0, 32))],
    );
    let sel2 = ChcExpr::Op(ChcOp::Select, vec![a(s2), a(ChcExpr::BitVec(2, 32))]);
    assert_eq!(evaluate_expr(&sel0, &model), Some(SmtValue::Bool(true)));
    assert_eq!(evaluate_expr(&sel2, &model), Some(SmtValue::Bool(false)));
}

#[test]
fn test_evaluate_expr_select_with_model_var() {
    let mut model = FxHashMap::default();
    // Model: arr = store(const(0), 3, 99)
    model.insert(
        "arr".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(3), SmtValue::Int(99))],
        },
    );
    let arr_var = ChcExpr::Var(int_var("arr"));
    // select(arr, 3) → 99
    let sel = ChcExpr::Op(ChcOp::Select, vec![a(arr_var.clone()), a(ChcExpr::Int(3))]);
    assert_eq!(evaluate_expr(&sel, &model), Some(SmtValue::Int(99)));
    // select(arr, 0) → 0 (default)
    let sel0 = ChcExpr::Op(ChcOp::Select, vec![a(arr_var), a(ChcExpr::Int(0))]);
    assert_eq!(evaluate_expr(&sel0, &model), Some(SmtValue::Int(0)));
}

#[test]
fn test_evaluate_expr_datatype_selector_and_tester() {
    let pair_sort = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    };
    let constructor = ChcExpr::FuncApp(
        "mk".to_string(),
        pair_sort.clone(),
        vec![a(ChcExpr::Int(10)), a(ChcExpr::Int(42))],
    );
    let expected_value =
        SmtValue::Datatype("mk".to_string(), vec![SmtValue::Int(10), SmtValue::Int(42)]);
    let mut model = FxHashMap::default();
    model.insert("p".to_string(), expected_value.clone());

    assert_eq!(
        evaluate_expr(&constructor, &model),
        Some(expected_value.clone())
    );

    let p_var = ChcExpr::Var(ChcVar::new("p", pair_sort));
    let selector = ChcExpr::FuncApp("fst".to_string(), ChcSort::Int, vec![a(p_var.clone())]);
    let tester = ChcExpr::FuncApp("is-mk".to_string(), ChcSort::Bool, vec![a(p_var.clone())]);
    let equality = ChcExpr::eq(p_var, constructor);

    assert_eq!(evaluate_expr(&selector, &model), Some(SmtValue::Int(10)));
    assert_eq!(evaluate_expr(&tester, &model), Some(SmtValue::Bool(true)));
    assert_eq!(evaluate_expr(&equality, &model), Some(SmtValue::Bool(true)));
}

mod wide_bitvec {
    use super::super::value_ops::smt_values_equal;
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn high_bit_129() -> ChcExpr {
        ChcExpr::Op(
            ChcOp::BvConcat,
            vec![a(ChcExpr::BitVec(1, 1)), a(ChcExpr::BitVec(0, 128))],
        )
    }

    #[test]
    fn concat_preserves_bit_128_exactly() {
        assert_eq!(
            evaluate_expr(&high_bit_129(), &FxHashMap::default()),
            Some(SmtValue::bitvec_from_biguint(
                BigUint::from(1u8) << 128,
                129
            ))
        );
    }

    #[test]
    fn concat_normalizes_direct_legacy_model_payloads() {
        let x = ChcVar::new("x", ChcSort::BitVec(1));
        let concat = ChcExpr::Op(
            ChcOp::BvConcat,
            vec![a(ChcExpr::BitVec(0, 1)), a(ChcExpr::var(x))],
        );
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::BitVec(2, 1));
        assert_eq!(evaluate_expr(&concat, &model), Some(SmtValue::BitVec(0, 2)));
    }

    #[test]
    fn equality_distinguishes_wide_high_bits() {
        let exact = SmtValue::bitvec_from_biguint(BigUint::from(1u8) << 128, 129);
        let low_only_legacy = SmtValue::BitVec(0, 129);
        assert_eq!(smt_values_equal(&exact, &exact), Some(true));
        assert_eq!(smt_values_equal(&exact, &low_only_legacy), Some(false));

        let x = ChcVar::new("x", ChcSort::BitVec(129));
        let equality = ChcExpr::eq(ChcExpr::var(x), high_bit_129());
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), exact);
        assert_eq!(evaluate_expr(&equality, &model), Some(SmtValue::Bool(true)));
        model.insert("x".to_string(), low_only_legacy);
        assert_eq!(
            evaluate_expr(&equality, &model),
            Some(SmtValue::Bool(false))
        );
    }

    #[test]
    fn extend_extract_repeat_and_bv2nat_are_exact_above_128_bits() {
        let model = FxHashMap::default();

        let zero_extended = ChcExpr::Op(ChcOp::BvZeroExtend(128), vec![a(ChcExpr::BitVec(1, 1))]);
        assert_eq!(
            evaluate_expr(&zero_extended, &model),
            Some(SmtValue::bitvec_from_biguint(BigUint::from(1u8), 129))
        );

        let sign_extended = ChcExpr::Op(ChcOp::BvSignExtend(128), vec![a(ChcExpr::BitVec(1, 1))]);
        let all_ones = (BigUint::from(1u8) << 129) - BigUint::from(1u8);
        assert_eq!(
            evaluate_expr(&sign_extended, &model),
            Some(SmtValue::bitvec_from_biguint(all_ones, 129))
        );

        let high = high_bit_129();
        let extracted = ChcExpr::Op(ChcOp::BvExtract(128, 128), vec![a(high.clone())]);
        assert_eq!(
            evaluate_expr(&extracted, &model),
            Some(SmtValue::BitVec(1, 1))
        );

        let repeated = ChcExpr::Op(ChcOp::BvRepeat(129), vec![a(ChcExpr::BitVec(1, 1))]);
        assert_eq!(
            evaluate_expr(&repeated, &model),
            Some(SmtValue::bitvec_from_biguint(
                (BigUint::from(1u8) << 129) - BigUint::from(1u8),
                129
            ))
        );

        let to_int = ChcExpr::Op(ChcOp::Bv2Nat, vec![a(high)]);
        assert_eq!(
            evaluate_expr(&to_int, &model),
            Some(SmtValue::int_from_bigint(BigInt::from(1u8) << 128))
        );
    }

    fn wide_var(name: &str, width: u32) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(width)))
    }

    fn binary(op: ChcOp, lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::Op(op, vec![a(lhs), a(rhs)])
    }

    #[test]
    fn wide_arithmetic_bitwise_and_comparisons_are_exact() {
        let width = 192;
        let modulus = BigUint::from(1u8) << width;
        let mask = &modulus - BigUint::from(1u8);
        let x_value: BigUint = (BigUint::from(1u8) << 191_usize) | BigUint::from(5u8);
        let y_value = BigUint::from(7u8);
        let mut model = FxHashMap::default();
        model.insert(
            "x".to_string(),
            SmtValue::bitvec_from_biguint(x_value.clone(), width),
        );
        model.insert(
            "y".to_string(),
            SmtValue::bitvec_from_biguint(y_value.clone(), width),
        );
        let x = || wide_var("x", width);
        let y = || wide_var("y", width);

        for (op, expected) in [
            (ChcOp::BvAdd, (&x_value + &y_value) & &mask),
            (ChcOp::BvSub, (&x_value + &modulus - &y_value) & &mask),
            (ChcOp::BvMul, (&x_value * &y_value) & &mask),
            (ChcOp::BvUDiv, &x_value / &y_value),
            (ChcOp::BvURem, &x_value % &y_value),
            (ChcOp::BvAnd, &x_value & &y_value),
            (ChcOp::BvOr, &x_value | &y_value),
            (ChcOp::BvXor, &x_value ^ &y_value),
            (ChcOp::BvNand, &mask ^ (&x_value & &y_value)),
            (ChcOp::BvNor, &mask ^ (&x_value | &y_value)),
            (ChcOp::BvXnor, &mask ^ (&x_value ^ &y_value)),
        ] {
            assert_eq!(
                evaluate_expr(&binary(op, x(), y()), &model),
                Some(SmtValue::bitvec_from_biguint(expected, width))
            );
        }

        for (op, expected) in [
            (ChcOp::BvULt, false),
            (ChcOp::BvULe, false),
            (ChcOp::BvUGt, true),
            (ChcOp::BvUGe, true),
            (ChcOp::BvSLt, true),
            (ChcOp::BvSLe, true),
            (ChcOp::BvSGt, false),
            (ChcOp::BvSGe, false),
        ] {
            assert_eq!(
                evaluate_expr(&binary(op, x(), y()), &model),
                Some(SmtValue::Bool(expected))
            );
        }

        assert_eq!(
            evaluate_expr(&ChcExpr::Op(ChcOp::BvNeg, vec![a(x())]), &model),
            Some(SmtValue::bitvec_from_biguint(&modulus - &x_value, width))
        );
        assert_eq!(
            evaluate_expr(&ChcExpr::Op(ChcOp::BvNot, vec![a(x())]), &model),
            Some(SmtValue::bitvec_from_biguint(&mask ^ &x_value, width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvComp, x(), x()), &model),
            Some(SmtValue::BitVec(1, 1))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvComp, x(), y()), &model),
            Some(SmtValue::BitVec(0, 1))
        );
    }

    #[test]
    fn wide_signed_corner_cases_and_division_by_zero_match_smtlib() {
        let width = 129;
        let min_signed: BigUint = BigUint::from(1u8) << 128_usize;
        let all_ones: BigUint = (BigUint::from(1u8) << (width as usize)) - BigUint::from(1u8);
        let mut model = FxHashMap::default();
        for (name, value) in [
            ("min", min_signed.clone()),
            ("minus_one", all_ones.clone()),
            ("zero", BigUint::from(0u8)),
            ("positive", BigUint::from(9u8)),
            ("four", BigUint::from(4u8)),
            ("minus_nine", (&all_ones - BigUint::from(8u8))),
        ] {
            model.insert(
                name.to_string(),
                SmtValue::bitvec_from_biguint(value, width),
            );
        }
        let v = |name| wide_var(name, width);

        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvSDiv, v("min"), v("minus_one")), &model),
            Some(SmtValue::bitvec_from_biguint(min_signed.clone(), width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvSRem, v("min"), v("minus_one")), &model),
            Some(SmtValue::bitvec_from_biguint(BigUint::from(0u8), width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvSDiv, v("positive"), v("zero")), &model),
            Some(SmtValue::bitvec_from_biguint(all_ones.clone(), width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvSDiv, v("min"), v("zero")), &model),
            Some(SmtValue::bitvec_from_biguint(BigUint::from(1u8), width))
        );
        for op in [ChcOp::BvSRem, ChcOp::BvSMod, ChcOp::BvURem] {
            assert_eq!(
                evaluate_expr(&binary(op, v("min"), v("zero")), &model),
                Some(SmtValue::bitvec_from_biguint(min_signed.clone(), width))
            );
        }
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvUDiv, v("min"), v("zero")), &model),
            Some(SmtValue::bitvec_from_biguint(all_ones, width))
        );

        let minus_two = (BigUint::from(1u8) << width) - BigUint::from(2u8);
        let minus_one = (BigUint::from(1u8) << width) - BigUint::from(1u8);
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvSDiv, v("minus_nine"), v("four")), &model),
            Some(SmtValue::bitvec_from_biguint(minus_two, width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvSRem, v("minus_nine"), v("four")), &model),
            Some(SmtValue::bitvec_from_biguint(minus_one, width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvSMod, v("minus_nine"), v("four")), &model),
            Some(SmtValue::bitvec_from_biguint(BigUint::from(3u8), width))
        );
    }

    #[test]
    fn wide_shifts_rotate_zero_and_int2bv_are_exact() {
        let width = 192;
        let top_bit: BigUint = BigUint::from(1u8) << 191_usize;
        let all_ones = (BigUint::from(1u8) << width) - BigUint::from(1u8);
        let mut model = FxHashMap::default();
        model.insert(
            "negative".to_string(),
            SmtValue::bitvec_from_biguint(top_bit.clone(), width),
        );
        model.insert(
            "amount".to_string(),
            SmtValue::bitvec_from_biguint(BigUint::from(width), width),
        );
        model.insert(
            "one".to_string(),
            SmtValue::bitvec_from_biguint(BigUint::from(1u8), width),
        );
        let negative = || wide_var("negative", width);
        let amount = || wide_var("amount", width);
        let one = || wide_var("one", width);

        for op in [ChcOp::BvShl, ChcOp::BvLShr] {
            assert_eq!(
                evaluate_expr(&binary(op, negative(), amount()), &model),
                Some(SmtValue::bitvec_from_biguint(BigUint::from(0u8), width))
            );
        }
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvAShr, negative(), amount()), &model),
            Some(SmtValue::bitvec_from_biguint(all_ones.clone(), width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvShl, negative(), one()), &model),
            Some(SmtValue::bitvec_from_biguint(BigUint::from(0u8), width))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvLShr, negative(), one()), &model),
            Some(SmtValue::bitvec_from_biguint(
                BigUint::from(1u8) << 190,
                width
            ))
        );
        assert_eq!(
            evaluate_expr(&binary(ChcOp::BvAShr, negative(), one()), &model),
            Some(SmtValue::bitvec_from_biguint(
                &top_bit | (BigUint::from(1u8) << 190),
                width
            ))
        );

        for op in [ChcOp::BvRotateLeft(0), ChcOp::BvRotateRight(0)] {
            assert_eq!(
                evaluate_expr(&ChcExpr::Op(op, vec![a(negative())]), &model),
                Some(SmtValue::bitvec_from_biguint(top_bit.clone(), width))
            );
        }
        assert_eq!(
            evaluate_expr(
                &ChcExpr::Op(ChcOp::BvRotateLeft(1), vec![a(negative())]),
                &model
            ),
            Some(SmtValue::bitvec_from_biguint(BigUint::from(1u8), width))
        );
        assert_eq!(
            evaluate_expr(
                &ChcExpr::Op(ChcOp::BvRotateRight(1), vec![a(negative())]),
                &model
            ),
            Some(SmtValue::bitvec_from_biguint(
                BigUint::from(1u8) << 190,
                width
            ))
        );
        // The u128 fast path must also avoid shifting by 128 when rotate=0.
        assert_eq!(
            evaluate_expr(
                &ChcExpr::Op(ChcOp::BvRotateLeft(0), vec![a(ChcExpr::BitVec(1, 128))]),
                &FxHashMap::default()
            ),
            Some(SmtValue::BitVec(1, 128))
        );

        let integer = ChcVar::new("integer", ChcSort::Int);
        let big_integer = (BigInt::from(1u8) << 191) + BigInt::from(5u8);
        model.insert(integer.name.clone(), SmtValue::int_from_bigint(big_integer));
        let int2bv = ChcExpr::Op(ChcOp::Int2Bv(width), vec![a(ChcExpr::var(integer))]);
        assert_eq!(
            evaluate_expr(&int2bv, &model),
            Some(SmtValue::bitvec_from_biguint(
                top_bit + BigUint::from(5u8),
                width
            ))
        );
    }

    #[test]
    fn malformed_or_resource_unbounded_indexed_bv_ops_fail_closed() {
        let model = FxHashMap::default();
        let too_wide_extend = ChcExpr::Op(
            ChcOp::BvZeroExtend(crate::MAX_BITVECTOR_WIDTH),
            vec![a(ChcExpr::BitVec(0, 1))],
        );
        let zero_repeat = ChcExpr::Op(ChcOp::BvRepeat(0), vec![a(ChcExpr::BitVec(1, 1))]);
        let too_wide_int2bv = ChcExpr::Op(
            ChcOp::Int2Bv(crate::MAX_BITVECTOR_WIDTH + 1),
            vec![a(ChcExpr::Int(0))],
        );
        let zero_width_concat = ChcExpr::Op(
            ChcOp::BvConcat,
            vec![a(ChcExpr::BitVec(0, 0)), a(ChcExpr::BitVec(1, 1))],
        );
        let zero_width_rotate = ChcExpr::Op(ChcOp::BvRotateLeft(1), vec![a(ChcExpr::BitVec(0, 0))]);

        for expr in [
            too_wide_extend,
            zero_repeat,
            too_wide_int2bv,
            zero_width_concat,
            zero_width_rotate,
        ] {
            assert_eq!(evaluate_expr(&expr, &model), None);
        }
    }
}

// --- Phase-2 BigInt escape: value_ops internals ---
// (End-to-end coverage lives in expr/tests/bigint_escape.rs, smt/tests_model_verify.rs,
// smt/tests_check_sat.rs, and lib_tests.rs.)

mod bigint_escape_value_ops {
    use super::super::value_ops::{eval_int_big, smt_values_equal};
    use super::*;
    use crate::expr::ChcVar;
    use crate::ChcSort;
    use num_bigint::BigInt;
    use std::sync::Arc;

    fn big_probe() -> BigInt {
        (BigInt::from(1u8) << 128) + 1
    }

    /// smt_values_equal BigInt arms: equal bigs true, big vs big+1 false,
    /// big vs Int false-by-canonicality, Opaque still abstains.
    #[test]
    fn smt_values_equal_bigint_arms() {
        let a = SmtValue::int_from_bigint(big_probe());
        let b = SmtValue::int_from_bigint(big_probe());
        let c = SmtValue::int_from_bigint(big_probe() + 1);
        assert_eq!(smt_values_equal(&a, &b), Some(true));
        assert_eq!(smt_values_equal(&a, &c), Some(false));
        // Cross-kind: canonicality makes Int vs BigInt decidedly unequal.
        assert_eq!(smt_values_equal(&a, &SmtValue::Int(1)), Some(false));
        assert_eq!(smt_values_equal(&SmtValue::Int(i128::MAX), &a), Some(false));
        // Bool vs BigInt: false by canonicality (BigInt is never 0/1).
        assert_eq!(smt_values_equal(&SmtValue::Bool(true), &a), Some(false));
        // Opaque abstains, never decides.
        assert_eq!(smt_values_equal(&SmtValue::Opaque("@v1".into()), &a), None);
    }

    /// Lockstep property: on expressions the i128 fast lane CAN fold,
    /// `eval_int_big` must agree exactly — including the SMT-LIB div/mod
    /// totals `(div x 0) = 0`, `(mod x 0) = x` and Euclidean semantics on
    /// every sign combination. A semantics split between the two lanes would
    /// be a soundness bug.
    #[test]
    fn eval_int_big_lockstep_with_evaluate_expr() {
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);
        let vx = || ChcExpr::var(x.clone());
        let vy = || ChcExpr::var(y.clone());
        let grid: [i128; 9] = [-9, -7, -2, -1, 0, 1, 2, 5, 9];

        for &a in &grid {
            for &b in &grid {
                let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
                model.insert("x".to_string(), SmtValue::Int(a));
                model.insert("y".to_string(), SmtValue::Int(b));

                let exprs = vec![
                    ChcExpr::add(vx(), vy()),
                    ChcExpr::Op(
                        ChcOp::Add,
                        vec![Arc::new(vx()), Arc::new(vy()), Arc::new(ChcExpr::int(3))],
                    ),
                    ChcExpr::sub(vx(), vy()),
                    ChcExpr::Op(ChcOp::Sub, vec![Arc::new(vx())]),
                    ChcExpr::mul(vx(), vy()),
                    ChcExpr::neg(vx()),
                    ChcExpr::Op(ChcOp::Div, vec![Arc::new(vx()), Arc::new(vy())]),
                    ChcExpr::Op(ChcOp::Mod, vec![Arc::new(vx()), Arc::new(vy())]),
                    ChcExpr::ite(
                        ChcExpr::lt(vx(), vy()),
                        ChcExpr::add(vx(), ChcExpr::int(1)),
                        ChcExpr::mul(vy(), ChcExpr::int(2)),
                    ),
                ];
                for expr in &exprs {
                    let fast = evaluate_expr(expr, &model);
                    let slow = eval_int_big(expr, &model);
                    match (fast, slow) {
                        (Some(SmtValue::Int(f)), Some(s)) => assert_eq!(
                            BigInt::from(f),
                            s,
                            "lane divergence on {expr} with x={a}, y={b}"
                        ),
                        (Some(other), _) => {
                            panic!("non-Int fold {other:?} on {expr} with x={a}, y={b}")
                        }
                        (None, slow) => panic!(
                            "fast lane abstained on in-range {expr} (x={a}, y={b}); slow lane: {slow:?}"
                        ),
                    }
                }
            }
        }
    }

    /// eval_int_big accepts BigInt model values and folds Horner trees
    /// exactly; unsupported shapes abstain (fail-closed).
    #[test]
    fn eval_int_big_bigint_vars_and_fail_closed() {
        let x = ChcVar::new("x", ChcSort::Int);
        let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::int_from_bigint(big_probe()));

        // Var reads the BigInt value; arithmetic over it is exact.
        let expr = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
        assert_eq!(eval_int_big(&expr, &model), Some(big_probe() + 1));

        // Horner literal folds exactly.
        let horner = ChcExpr::from_bigint(big_probe());
        assert_eq!(eval_int_big(&horner, &model), Some(big_probe()));

        // Missing var: abstain.
        let missing = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
        assert_eq!(eval_int_big(&missing, &model), None);

        // Bool-sorted model value in an int position: abstain.
        model.insert("x".to_string(), SmtValue::Bool(true));
        assert_eq!(
            eval_int_big(&ChcExpr::var(x), &model),
            None,
            "non-integer model value must abstain, not coerce"
        );
    }

    /// A concrete Int-valued array select must participate in the exact
    /// comparison retry when the opposite operand is a beyond-i128 Horner
    /// literal. This is the shape emitted by Solidity LIA-Array benchmarks.
    #[test]
    fn eval_int_big_array_select_against_horner_literal() {
        let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let arr = ChcVar::new("arr", int_array);
        let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
        model.insert(
            "arr".to_string(),
            SmtValue::ArrayMap {
                default: Box::new(SmtValue::Int(0)),
                entries: vec![(SmtValue::Int(7), SmtValue::Int(42))],
            },
        );

        let selected = ChcExpr::select(ChcExpr::var(arr), ChcExpr::int(7));
        assert_eq!(eval_int_big(&selected, &model), Some(BigInt::from(42)));

        let two_256_minus_one = (BigInt::from(1u8) << 256) - 1;
        let lhs = ChcExpr::add(selected, ChcExpr::int(5));
        let rhs = ChcExpr::from_bigint(two_256_minus_one);
        let comparison = ChcExpr::le(lhs.clone(), rhs.clone());
        assert_eq!(
            evaluate_expr(&comparison, &model),
            Some(SmtValue::Bool(true))
        );
        let false_control = ChcExpr::gt(lhs, rhs);
        assert_eq!(
            evaluate_expr(&false_control, &model),
            Some(SmtValue::Bool(false))
        );
    }

    /// BigInt array elements remain exact, while a non-integer selected value
    /// must abstain rather than being coerced into the integer lane.
    #[test]
    fn eval_int_big_array_select_value_type_controls() {
        let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let ints = ChcVar::new("ints", int_array);
        let bool_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool));
        let bools = ChcVar::new("bools", bool_array);
        let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
        model.insert(
            "ints".to_string(),
            SmtValue::ConstArray(Box::new(SmtValue::int_from_bigint(big_probe()))),
        );
        model.insert(
            "bools".to_string(),
            SmtValue::ConstArray(Box::new(SmtValue::Bool(true))),
        );

        let selected_int = ChcExpr::select(ChcExpr::var(ints), ChcExpr::int(0));
        assert_eq!(eval_int_big(&selected_int, &model), Some(big_probe()));
        let selected_bool = ChcExpr::select(ChcExpr::var(bools), ChcExpr::int(0));
        assert_eq!(eval_int_big(&selected_bool, &model), None);
    }
}

// --- Real (LRA) arithmetic evaluation (#LRA-Lin) -----------------------------
// The canonical evaluator was previously Real-blind: `ChcExpr::Real` literals
// and all Real arithmetic/comparisons abstained (`None` -> Indeterminate), so
// the strict model verifier could never validate an LRA witness (every Real
// atom stayed Indeterminate, and a violating fully-assigned Real model was
// accepted via the #4712 trust-the-theory-solver path). These tests pin the
// exact-rational lanes added to `evaluate_expr` / `eval_int_cmp`.
mod real_eval {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn real(n: i64, d: i64) -> SmtValue {
        SmtValue::Real(BigRational::new(BigInt::from(n), BigInt::from(d)))
    }

    #[test]
    fn real_comparison_between_vars_evaluates() {
        // A < B with A = 1/2, B = 1 -> true (was None pre-fix).
        let expr = ChcExpr::lt(
            ChcExpr::var(ChcVar::new("A", ChcSort::Real)),
            ChcExpr::var(ChcVar::new("B", ChcSort::Real)),
        );
        let mut model = FxHashMap::default();
        model.insert("A".to_string(), real(1, 2));
        model.insert("B".to_string(), real(1, 1));
        assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
    }

    #[test]
    fn real_add_equality_evaluates_exactly() {
        // C = A + B with A = B = 1/2, C = 1 -> true.
        let sum = ChcExpr::add(
            ChcExpr::var(ChcVar::new("A", ChcSort::Real)),
            ChcExpr::var(ChcVar::new("B", ChcSort::Real)),
        );
        let expr = ChcExpr::eq(ChcExpr::var(ChcVar::new("C", ChcSort::Real)), sum);
        let mut model = FxHashMap::default();
        model.insert("A".to_string(), real(1, 2));
        model.insert("B".to_string(), real(1, 2));
        model.insert("C".to_string(), real(1, 1));
        assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
    }

    #[test]
    fn real_literal_bound_detects_violation() {
        // A <= 3.5: satisfied at A=2 (true); VIOLATED at A=4 (false, NOT None).
        // Pre-fix this abstained to None, so the verifier's #4712 path could
        // accept a violating Real model as Sat; now it evaluates to false.
        let expr = ChcExpr::le(
            ChcExpr::var(ChcVar::new("A", ChcSort::Real)),
            ChcExpr::Real(7, 2),
        );
        let mut model = FxHashMap::default();
        model.insert("A".to_string(), real(2, 1));
        assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(true)));
        model.insert("A".to_string(), real(4, 1));
        assert_eq!(evaluate_expr(&expr, &model), Some(SmtValue::Bool(false)));
    }

    #[test]
    fn named_int_real_conversions_evaluate_exactly() {
        let model = FxHashMap::default();
        let to_real = ChcExpr::FuncApp(
            "to_real".to_string(),
            ChcSort::Real,
            vec![ChcExpr::Int(-3).into()],
        );
        let to_int = ChcExpr::FuncApp(
            "to_int".to_string(),
            ChcSort::Int,
            vec![ChcExpr::Real(-3, 2).into()],
        );
        let is_int_true = ChcExpr::FuncApp(
            "is_int".to_string(),
            ChcSort::Bool,
            vec![ChcExpr::Real(4, 2).into()],
        );
        let is_int_false = ChcExpr::FuncApp(
            "is_int".to_string(),
            ChcSort::Bool,
            vec![ChcExpr::Real(3, 2).into()],
        );

        assert_eq!(evaluate_expr(&to_real, &model), Some(real(-3, 1)));
        assert_eq!(evaluate_expr(&to_int, &model), Some(SmtValue::Int(-2)));
        assert_eq!(
            evaluate_expr(&is_int_true, &model),
            Some(SmtValue::Bool(true))
        );
        assert_eq!(
            evaluate_expr(&is_int_false, &model),
            Some(SmtValue::Bool(false))
        );
    }

    #[test]
    fn malformed_named_conversion_fails_closed() {
        let model = FxHashMap::default();
        let wrong_argument_sort = ChcExpr::FuncApp(
            "to_real".to_string(),
            ChcSort::Real,
            vec![ChcExpr::Bool(true).into()],
        );
        let wrong_return_sort = ChcExpr::FuncApp(
            "to_int".to_string(),
            ChcSort::Real,
            vec![ChcExpr::Real(3, 2).into()],
        );
        assert_eq!(evaluate_expr(&wrong_argument_sort, &model), None);
        assert_eq!(evaluate_expr(&wrong_return_sort, &model), None);
    }
}
