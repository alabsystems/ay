// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::super::tests::{ample, convert, formula, model};
use super::*;

mod exhaustive;
mod oracle;
mod source_replay;

#[test]
fn original_dag_replay_rejects_mutated_typed_values_and_missing_bindings() {
    let source = formula();
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let assignment = model(encoding);
            let mut candidate = encoding.check_scalar_candidate(&assignment)?;
            encoding.replay_scalar_candidate(&candidate)?;
            let pristine = candidate.values.clone();
            for wrong in [
                ScalarValue::BitVec(6, 8),
                ScalarValue::BitVec(7, 64),
                ScalarValue::Bool(true),
            ] {
                candidate.values[1] = wrong;
                assert_eq!(
                    encoding.replay_scalar_candidate(&candidate),
                    Err(Error::InvalidCandidate)
                );
            }
            candidate.values = pristine;
            candidate.values.pop();
            assert_eq!(
                encoding.replay_scalar_candidate(&candidate),
                Err(Error::InvalidCandidate)
            );
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn fixed_width_replay_uses_smtlib_signed_zero_shift_and_128_bit_semantics() {
    use ScalarValue::BitVec as B;
    let original = ample();
    let cases = [
        (ChcOp::BvAdd, B(u128::MAX, 128), B(1, 128), B(0, 128)),
        (ChcOp::BvMul, B(1 << 127, 128), B(2, 128), B(0, 128)),
        (
            ChcOp::BvSDiv,
            B(1 << 127, 128),
            B(u128::MAX, 128),
            B(1 << 127, 128),
        ),
        (
            ChcOp::BvSRem,
            B(1 << 127, 128),
            B(u128::MAX, 128),
            B(0, 128),
        ),
        (ChcOp::BvSMod, B(253, 8), B(2, 8), B(1, 8)),
        (ChcOp::BvSMod, B(3, 8), B(254, 8), B(255, 8)),
        (ChcOp::BvUDiv, B(7, 8), B(0, 8), B(255, 8)),
        (ChcOp::BvSDiv, B(255, 8), B(0, 8), B(1, 8)),
        (ChcOp::BvSDiv, B(7, 8), B(0, 8), B(255, 8)),
        (ChcOp::BvURem, B(7, 8), B(0, 8), B(7, 8)),
        (ChcOp::BvShl, B(1, 64), B(64, 64), B(0, 64)),
        (ChcOp::BvLShr, B(u64::MAX as u128, 64), B(64, 64), B(0, 64)),
        (ChcOp::BvAShr, B(128, 8), B(255, 8), B(255, 8)),
    ];
    for (op, a, b, expected) in cases {
        assert_eq!(
            operations::apply(op, &[a, b], &original),
            Ok(expected),
            "{op:?}"
        );
    }
}

#[test]
fn indexed_replay_is_exact_at_128_bits_and_never_truncates_wider_outputs() {
    use ScalarValue::BitVec as B;
    let original = ample();
    let cases = [
        (
            ChcOp::BvExtract(127, 64),
            B(u128::MAX, 128),
            B(u64::MAX as u128, 64),
        ),
        (ChcOp::BvSignExtend(120), B(128, 8), B(u128::MAX - 127, 128)),
        (ChcOp::BvZeroExtend(120), B(128, 8), B(128, 128)),
        (ChcOp::BvRotateLeft(128), B(1, 128), B(1, 128)),
        (ChcOp::BvRotateRight(1), B(1, 128), B(1 << 127, 128)),
        (ChcOp::BvRepeat(16), B(255, 8), B(u128::MAX, 128)),
    ];
    for (op, value, expected) in cases {
        assert_eq!(
            operations::apply(op, &[value], &original),
            Ok(expected),
            "{op:?}"
        );
    }
    assert_eq!(
        operations::apply(
            ChcOp::BvConcat,
            &[B(u64::MAX as u128, 64), B(u64::MAX as u128, 64)],
            &original
        ),
        Ok(B(u128::MAX, 128))
    );
    for op in [
        ChcOp::BvZeroExtend(1),
        ChcOp::BvSignExtend(1),
        ChcOp::BvRepeat(2),
    ] {
        assert_eq!(
            operations::apply(op, &[B(1, 128)], &original),
            Err(Error::Unsupported)
        );
    }
    assert_eq!(
        operations::apply(ChcOp::BvConcat, &[B(1, 128), B(1, 1)], &original),
        Err(Error::Unsupported)
    );
}
