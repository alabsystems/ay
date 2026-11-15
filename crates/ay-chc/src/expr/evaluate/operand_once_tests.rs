// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every bit-vector operator evaluates each operand exactly once.
//!
//! The narrow (`u128`) and exact (`BigUint`) lanes used to evaluate an
//! operand separately, so an operand that evaluates in neither lane cost two
//! evaluations per enclosing operator: `2^depth` on a chain. A 250-deep
//! `(bvsdiv (bvmul .. 4) 4)` chain from CEGAR's equality resolution held a
//! portfolio worker in model verification past its deadline (model-checker-consumer
//! `safe_symbolic_from_elem`, 875 s against a 30 s budget).

use super::*;
use crate::{ChcSort, ChcVar};
use std::sync::Arc;

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

/// `depth` nested `(bvsdiv (bvmul x 4) 4)` over `x` of `width` bits.
fn chain(x: &ChcVar, width: u32, depth: usize) -> ChcExpr {
    let four = ChcExpr::BitVec(4, width);
    let mut expr = ChcExpr::var(x.clone());
    for _ in 0..depth {
        expr = op(
            ChcOp::BvSDiv,
            vec![op(ChcOp::BvMul, vec![expr, four.clone()]), four.clone()],
        );
    }
    expr
}

#[test]
#[ntest::timeout(20_000)]
fn a_deep_chain_over_an_unassigned_variable_is_linear() {
    let x = ChcVar::new("x", ChcSort::BitVec(64));
    let model = FxHashMap::default();
    // 2^96 evaluations before; 96 now.
    assert_eq!(evaluate_expr(&chain(&x, 64, 96), &model), None);
    for unary in [ChcOp::BvNeg, ChcOp::BvNot, ChcOp::BvRotateLeft(3)] {
        let mut expr = ChcExpr::var(x.clone());
        for _ in 0..96 {
            expr = op(
                ChcOp::BvAdd,
                vec![op(unary, vec![expr]), ChcExpr::BitVec(1, 64)],
            );
        }
        assert_eq!(evaluate_expr(&expr, &model), None, "{unary:?}");
    }
}

#[test]
fn a_chain_keeps_its_value_in_both_lanes() {
    for width in [64, 200] {
        let x = ChcVar::new("x", ChcSort::BitVec(width));
        let model: FxHashMap<String, SmtValue> =
            [("x".to_string(), SmtValue::bitvec_from_u128(3, width))]
                .into_iter()
                .collect();
        assert_eq!(
            evaluate_expr(&chain(&x, width, 12), &model),
            Some(SmtValue::bitvec_from_u128(3, width)),
            "width {width}"
        );
        let shifted = op(
            ChcOp::BvLShr,
            vec![
                op(
                    ChcOp::BvShl,
                    vec![ChcExpr::var(x.clone()), ChcExpr::BitVec(5, width)],
                ),
                ChcExpr::BitVec(5, width),
            ],
        );
        assert_eq!(
            evaluate_expr(&shifted, &model),
            Some(SmtValue::bitvec_from_u128(3, width)),
            "width {width}"
        );
    }
}
