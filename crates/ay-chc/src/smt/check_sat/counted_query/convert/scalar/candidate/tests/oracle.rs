// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

//! Independent existing evaluator, never a copy of the new scalar operations.
//! These test-only models deliberately use BigBitVec even below 129 bits to
//! enter eval_bv_operand's BigUint/BigInt lane. The public value normalization
//! accepts these exact non-canonical representations; production models are
//! still canonical. A second evaluation checks the ordinary narrow lane too.
//! Oracle evaluation and ordinary SAT search are NOT counted production work.

use super::*;
use ay_core::kani_compat::DetHashMap;
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use std::sync::Arc;

pub(super) type Model = DetHashMap<String, crate::smt::SmtValue>;

pub(super) const BINARY: [ChcOp; 28] = [
    ChcOp::BvAdd,
    ChcOp::BvSub,
    ChcOp::BvMul,
    ChcOp::BvUDiv,
    ChcOp::BvURem,
    ChcOp::BvSDiv,
    ChcOp::BvSRem,
    ChcOp::BvSMod,
    ChcOp::BvAnd,
    ChcOp::BvOr,
    ChcOp::BvXor,
    ChcOp::BvNand,
    ChcOp::BvNor,
    ChcOp::BvXnor,
    ChcOp::BvShl,
    ChcOp::BvLShr,
    ChcOp::BvAShr,
    ChcOp::BvULt,
    ChcOp::BvULe,
    ChcOp::BvUGt,
    ChcOp::BvUGe,
    ChcOp::BvSLt,
    ChcOp::BvSLe,
    ChcOp::BvSGt,
    ChcOp::BvSGe,
    ChcOp::BvComp,
    ChcOp::Eq,
    ChcOp::Ne,
];

pub(super) fn constant(value: ScalarValue) -> ChcExpr {
    match value {
        ScalarValue::Bool(value) => ChcExpr::Bool(value),
        ScalarValue::BitVec(value, width) => ChcExpr::BitVec(value, width),
    }
}

pub(super) fn value(value: ScalarValue) -> crate::smt::SmtValue {
    match value {
        ScalarValue::Bool(value) => crate::smt::SmtValue::Bool(value),
        ScalarValue::BitVec(value, width) => crate::smt::SmtValue::BitVec(value, width),
    }
}

pub(super) fn sort(value: ScalarValue) -> ChcSort {
    match value {
        ScalarValue::Bool(_) => ChcSort::Bool,
        ScalarValue::BitVec(_, width) => ChcSort::BitVec(width),
    }
}

pub(super) fn variable(index: usize, value: ScalarValue) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Var(crate::ChcVar::new(
        format!("operand_{index}"),
        sort(value),
    )))
}

pub(super) fn models(args: &[ScalarValue]) -> (Model, Model) {
    let mut narrow = Model::default();
    let mut wide = Model::default();
    for (index, &arg) in args.iter().enumerate() {
        let name = format!("operand_{index}");
        narrow.insert(name.clone(), value(arg));
        wide.insert(
            name,
            match arg {
                ScalarValue::Bool(value) => crate::smt::SmtValue::Bool(value),
                ScalarValue::BitVec(value, width) => {
                    assert!((1..=128).contains(&width));
                    assert!(BigUint::from(value).bits() <= u64::from(width));
                    crate::smt::SmtValue::BigBitVec(Arc::new(BigUint::from(value)), width)
                }
            },
        );
    }
    (narrow, wide)
}

pub(super) fn definite(expr: &ChcExpr, model: &Model) -> ScalarValue {
    let actual = crate::expr::evaluate_expr(expr, model)
        .unwrap_or_else(|| panic!("existing evaluator must decide {expr:?}"));
    if let crate::smt::SmtValue::Bool(value) = actual {
        return ScalarValue::Bool(value);
    }
    let (bits, width) = actual
        .bitvec_to_biguint()
        .expect("oracle output must be an exact scalar bitvector");
    assert!((1..=128).contains(&width));
    ScalarValue::BitVec(bits.to_u128().expect("oracle must fit its width"), width)
}

pub(super) fn expected(expr: &ChcExpr, args: &[ScalarValue]) -> ScalarValue {
    let (narrow, wide) = models(args);
    let expected = definite(expr, &wide);
    assert_eq!(definite(expr, &narrow), expected, "oracle lanes: {expr:?}");
    expected
}

fn expression(op: ChcOp, args: &[ScalarValue]) -> ChcExpr {
    ChcExpr::Op(
        op,
        args.iter()
            .enumerate()
            .map(|(index, &arg)| variable(index, arg))
            .collect(),
    )
}

pub(super) fn compare(op: ChcOp, args: &[ScalarValue], owner: &CountedAdmission) {
    let expr = expression(op, args);
    let expected = expected(&expr, args);
    assert_eq!(
        operations::apply(op, args, owner),
        Ok(expected),
        "operation {op:?}, inputs {args:?}"
    );
}

#[test]
fn independent_existing_oracle_decides_known_scalar_boundaries() {
    use ScalarValue::{BitVec as B, Bool as P};
    let min = 1u128 << 127;
    let cases = [
        (ChcOp::BvAdd, vec![B(u128::MAX, 128), B(1, 128)], B(0, 128)),
        (
            ChcOp::BvSDiv,
            vec![B(min, 128), B(u128::MAX, 128)],
            B(min, 128),
        ),
        (
            ChcOp::BvSRem,
            vec![B(min, 128), B(u128::MAX, 128)],
            B(0, 128),
        ),
        (ChcOp::BvUDiv, vec![B(7, 8), B(0, 8)], B(255, 8)),
        (ChcOp::BvSDiv, vec![B(255, 8), B(0, 8)], B(1, 8)),
        (ChcOp::BvSMod, vec![B(253, 8), B(2, 8)], B(1, 8)),
        (
            ChcOp::BvAShr,
            vec![B(min, 128), B(128, 128)],
            B(u128::MAX, 128),
        ),
        (ChcOp::BvRotateLeft(127), vec![B(1, 128)], B(min, 128)),
        (
            ChcOp::BvConcat,
            vec![B(u64::MAX as u128, 64), B(u64::MAX as u128, 64)],
            B(u128::MAX, 128),
        ),
        (ChcOp::Ite, vec![P(false), P(true), P(false)], P(false)),
    ];
    for (op, args, wanted) in cases {
        assert_eq!(expected(&expression(op, &args), &args), wanted, "{op:?}");
    }
}
