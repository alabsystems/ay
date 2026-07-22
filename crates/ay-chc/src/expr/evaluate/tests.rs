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
}
