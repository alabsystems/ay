// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use std::sync::Arc;
use ScalarValue::{BitVec as B, Bool as P};

enum Shape {
    Symbolic,
    ConstantTail,
}

fn case(op: ChcOp, args: &[ScalarValue], shape: Shape) {
    let operands: Vec<_> = args
        .iter()
        .enumerate()
        .map(|(index, &arg)| {
            if index > 0 && matches!(shape, Shape::ConstantTail) {
                Arc::new(oracle::constant(arg))
            } else {
                oracle::variable(index, arg)
            }
        })
        .collect();
    source_case(Arc::new(ChcExpr::Op(op, operands.clone())), &operands, args);
}

fn source_case(expr: Arc<ChcExpr>, operands: &[Arc<ChcExpr>], args: &[ScalarValue]) {
    let expected = oracle::expected(&expr, args);
    let (narrow, wide) = oracle::models(args);
    let mut assertions = Vec::new();
    for (operand, &value) in operands.iter().zip(args) {
        if matches!(operand.as_ref(), ChcExpr::Var(_)) {
            assertions.push(Arc::new(ChcExpr::Op(
                ChcOp::Eq,
                vec![operand.clone(), Arc::new(oracle::constant(value))],
            )));
        }
    }
    assert!(
        !assertions.is_empty(),
        "must encode an actual source variable"
    );
    assertions.push(Arc::new(ChcExpr::Op(
        ChcOp::Eq,
        vec![expr.clone(), Arc::new(oracle::constant(expected))],
    )));
    let source = ChcExpr::Op(ChcOp::And, assertions);
    assert_eq!(oracle::definite(&source, &wide), P(true));
    assert_eq!(oracle::definite(&source, &narrow), P(true));
    let owner = ample();
    let mut built = convert(&source, &owner).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            // The ordinary SAT solver is an independent test oracle, not a
            // counted production solve. Any Unknown/Unsupported/Unsat fails.
            let assignment = model(encoding);
            let candidate = encoding.check_scalar_candidate(&assignment)?;
            assert_eq!(candidate.values().len(), encoding.context.bindings().len());
            let mut decoded = oracle::Model::default();
            for (binding, &value) in encoding.context.bindings().iter().zip(candidate.values()) {
                let name = &binding.original.name;
                assert_eq!(
                    Some(&oracle::value(value)),
                    narrow.get(name),
                    "{expr:?}: {name}"
                );
                assert!(decoded.insert(name.clone(), oracle::value(value)).is_none());
            }
            assert_eq!(oracle::definite(&expr, &decoded), expected);
            assert_eq!(oracle::definite(&source, &decoded), P(true));
            encoding.replay_scalar_candidate(&candidate)
        })
        .unwrap_or_else(|error| panic!("original source must replay: {expr:?}: {error:?}"));
    built.finish().unwrap();
    assert_eq!(owner.usage().unwrap().refusal, None);
}

#[test]
fn original_dag_replay_covers_every_binary_scalar_operator() {
    let mut cases = 0;
    for op in oracle::BINARY {
        for (a, b) in [(0, 0), (7, 1), (4, 7)] {
            case(op, &[B(a, 3), B(b, 3)], Shape::Symbolic);
            cases += 1;
        }
    }
    assert_eq!(cases, 84);
}

#[test]
fn original_dag_replay_covers_boolean_aliases_and_both_ite_sorts() {
    let mut cases = 0;
    for a in [false, true] {
        case(ChcOp::Not, &[P(a)], Shape::Symbolic);
        cases += 1;
        for b in [false, true] {
            for op in [
                ChcOp::And,
                ChcOp::Or,
                ChcOp::Implies,
                ChcOp::Iff,
                ChcOp::Eq,
                ChcOp::Ne,
            ] {
                case(op, &[P(a), P(b)], Shape::Symbolic);
                cases += 1;
            }
            for c in [false, true] {
                for op in [ChcOp::And, ChcOp::Or, ChcOp::Ite] {
                    case(op, &[P(a), P(b), P(c)], Shape::Symbolic);
                    cases += 1;
                }
                case(
                    ChcOp::Ite,
                    &[P(a), B(u128::from(b), 1), B(u128::from(c), 1)],
                    Shape::Symbolic,
                );
                cases += 1;
            }
        }
        let p = oracle::variable(0, P(a));
        let negative = Arc::new(ChcExpr::Op(ChcOp::Not, vec![p.clone()]));
        let alias = Arc::new(ChcExpr::Op(ChcOp::Not, vec![negative.clone()]));
        // Repeated Arc identities, nested signed aliases, and both branches
        // survive into the ORIGINAL DAG replay rather than a grounded copy.
        let condition = Arc::new(ChcExpr::Op(ChcOp::And, vec![p.clone(), alias]));
        let expression = Arc::new(ChcExpr::Op(
            ChcOp::Ite,
            vec![
                condition,
                Arc::new(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        negative,
                        Arc::new(ChcExpr::BitVec(1, 8)),
                        Arc::new(ChcExpr::BitVec(7, 8)),
                    ],
                )),
                Arc::new(ChcExpr::BitVec(9, 8)),
            ],
        ));
        source_case(expression, &[p], &[P(a)]);
        cases += 1;
    }
    assert_eq!(cases, 60);
}

#[test]
fn original_dag_replay_covers_every_unary_indexed_and_concat_operator() {
    let mut cases = 0;
    for op in [
        ChcOp::BvNot,
        ChcOp::BvNeg,
        ChcOp::BvExtract(7, 3),
        ChcOp::BvZeroExtend(3),
        ChcOp::BvSignExtend(3),
        ChcOp::BvRotateLeft(0),
        ChcOp::BvRotateLeft(9),
        ChcOp::BvRotateRight(0),
        ChcOp::BvRotateRight(9),
        ChcOp::BvRepeat(1),
        ChcOp::BvRepeat(2),
    ] {
        for a in [0, 0x81, 0xff] {
            case(op, &[B(a, 8)], Shape::Symbolic);
            cases += 1;
        }
    }
    for args in [
        [B(1, 1), B(0, 3)],
        [B(7, 3), B(1, 1)],
        [B(0x81, 8), B(0x7e, 8)],
    ] {
        case(ChcOp::BvConcat, &args, Shape::Symbolic);
        cases += 1;
    }
    assert_eq!(cases, 36);
}

#[test]
fn original_dag_replay_keeps_exact_128_bit_boundary_semantics() {
    let min = 1u128 << 127;
    let max = u128::MAX;
    let mut cases = 0;
    for (op, a, b) in [
        (ChcOp::BvAdd, max, 1),
        (ChcOp::BvSub, 0, 1),
        (ChcOp::BvMul, min, 2),
        (ChcOp::BvUDiv, max, 0),
        (ChcOp::BvUDiv, max, 2),
        (ChcOp::BvURem, max, 0),
        (ChcOp::BvURem, max, 2),
        (ChcOp::BvSDiv, min, max),
        (ChcOp::BvSDiv, min, 0),
        (ChcOp::BvSDiv, max, 0),
        (ChcOp::BvSRem, min, max),
        (ChcOp::BvSMod, min, max),
        (ChcOp::BvSMod, min, 3),
        (ChcOp::BvShl, 1, 127),
        (ChcOp::BvShl, 1, 128),
        (ChcOp::BvLShr, max, 128),
        (ChcOp::BvAShr, min, 127),
        (ChcOp::BvAShr, min, 128),
        (ChcOp::BvComp, max, max),
        (ChcOp::BvSLt, min, 0),
        (ChcOp::BvUGt, max, 0),
    ] {
        // A symbolic lhs keeps decoding meaningful. Constant divisors bound
        // this qualification's circuit cost; small-width tests above cover
        // fully symbolic divisors. The original 100M-unit grant is unchanged.
        case(op, &[B(a, 128), B(b, 128)], Shape::ConstantTail);
        cases += 1;
    }
    for (op, arg) in [
        (ChcOp::BvNot, B(max, 128)),
        (ChcOp::BvNeg, B(min, 128)),
        (ChcOp::BvExtract(127, 64), B(max, 128)),
        (ChcOp::BvExtract(0, 0), B(max, 128)),
        (ChcOp::BvZeroExtend(0), B(max, 128)),
        (ChcOp::BvSignExtend(0), B(min, 128)),
        (ChcOp::BvZeroExtend(120), B(0x80, 8)),
        (ChcOp::BvSignExtend(120), B(0x80, 8)),
        (ChcOp::BvRotateLeft(0), B(min, 128)),
        (ChcOp::BvRotateLeft(128), B(min, 128)),
        (ChcOp::BvRotateLeft(127), B(1, 128)),
        (ChcOp::BvRotateRight(0), B(1, 128)),
        (ChcOp::BvRotateRight(128), B(1, 128)),
        (ChcOp::BvRotateRight(1), B(1, 128)),
        (ChcOp::BvRepeat(1), B(min, 128)),
        (ChcOp::BvRepeat(16), B(0xff, 8)),
    ] {
        case(op, &[arg], Shape::Symbolic);
        cases += 1;
    }
    for args in [
        [B(u64::MAX as u128, 64), B(u64::MAX as u128, 64)],
        [B(1, 1), B(0, 127)],
    ] {
        case(ChcOp::BvConcat, &args, Shape::Symbolic);
        cases += 1;
    }
    assert_eq!(cases, 39);
}
