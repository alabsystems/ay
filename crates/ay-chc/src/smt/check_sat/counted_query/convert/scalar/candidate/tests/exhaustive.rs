// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ScalarValue::{BitVec as B, Bool as P};

#[test]
fn exhaustive_small_binary_replay_matches_existing_bigint_evaluator() {
    let owner = ample();
    let mut comparisons = 0;
    for width in 1..=4 {
        for a in 0..1u128 << width {
            for b in 0..1u128 << width {
                for op in oracle::BINARY {
                    oracle::compare(op, &[B(a, width), B(b, width)], &owner);
                    comparisons += 1;
                }
            }
        }
    }
    // Includes every signed pair, zero divisor, MIN/-1 and representable
    // shift amount, including amounts equal to and greater than the width.
    assert_eq!(comparisons, 9_520);
    assert_eq!(owner.usage().unwrap().refusal, None);
}

#[test]
fn exhaustive_small_unary_indexed_replay_matches_existing_bigint_evaluator() {
    let owner = ample();
    let mut comparisons = 0;
    for width in 1..=4 {
        for a in 0..1u128 << width {
            let arg = [B(a, width)];
            for op in [ChcOp::BvNot, ChcOp::BvNeg] {
                oracle::compare(op, &arg, &owner);
                comparisons += 1;
            }
            for high in 0..width {
                for low in 0..=high {
                    oracle::compare(ChcOp::BvExtract(high, low), &arg, &owner);
                    comparisons += 1;
                }
            }
            for amount in 0..=2 * width {
                for op in [ChcOp::BvRotateLeft(amount), ChcOp::BvRotateRight(amount)] {
                    oracle::compare(op, &arg, &owner);
                    comparisons += 1;
                }
            }
            for amount in 0..=3 {
                for op in [ChcOp::BvZeroExtend(amount), ChcOp::BvSignExtend(amount)] {
                    oracle::compare(op, &arg, &owner);
                    comparisons += 1;
                }
            }
            for count in 1..=4 {
                oracle::compare(ChcOp::BvRepeat(count), &arg, &owner);
                comparisons += 1;
            }
        }
    }
    assert_eq!(comparisons, 1_094);
    assert_eq!(owner.usage().unwrap().refusal, None);
}

#[test]
fn exhaustive_small_concat_and_boolean_replay_match_existing_evaluator() {
    let owner = ample();
    let mut concatenations = 0;
    for left in 1..=3 {
        for right in 1..=3 {
            for a in 0..1u128 << left {
                for b in 0..1u128 << right {
                    oracle::compare(ChcOp::BvConcat, &[B(a, left), B(b, right)], &owner);
                    concatenations += 1;
                }
            }
        }
    }
    assert_eq!(concatenations, 196);
    let mut booleans = 0;
    for a in [false, true] {
        oracle::compare(ChcOp::Not, &[P(a)], &owner);
        booleans += 1;
        for b in [false, true] {
            for op in [
                ChcOp::And,
                ChcOp::Or,
                ChcOp::Implies,
                ChcOp::Iff,
                ChcOp::Eq,
                ChcOp::Ne,
            ] {
                oracle::compare(op, &[P(a), P(b)], &owner);
                booleans += 1;
            }
            for c in [false, true] {
                for op in [ChcOp::And, ChcOp::Or, ChcOp::Ite] {
                    oracle::compare(op, &[P(a), P(b), P(c)], &owner);
                    booleans += 1;
                }
                oracle::compare(
                    ChcOp::Ite,
                    &[P(a), B(u128::from(b), 1), B(u128::from(c), 1)],
                    &owner,
                );
                booleans += 1;
            }
        }
    }
    assert_eq!(booleans, 58);
    assert_eq!(owner.usage().unwrap().refusal, None);
}
