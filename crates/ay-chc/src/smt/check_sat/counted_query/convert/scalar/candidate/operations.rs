// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-width scalar evaluation of already-evaluated operands.
//!
//! Same SMT-LIB modular semantics as expr/evaluate/eval_bv, without its
//! recursive evaluator, TLS caches or BigUint allocations. A native arithmetic
//! operation is a bounded logical unit, not a CPU-instruction measurement.

use super::*;

pub(super) fn canonical(value: u128, width: u32) -> bool {
    (1..=128).contains(&width) && (width == 128 || value < (1u128 << width))
}

fn mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn signed(value: u128, width: u32) -> i128 {
    ((value << (128 - width)) as i128) >> (128 - width)
}

pub(super) fn apply(
    op: ChcOp,
    args: &[ScalarValue],
    owner: &CountedAdmission,
) -> Result<ScalarValue> {
    owner.admit(args.len().checked_add(32).ok_or(Error::Unsupported)?, 0)?;
    match (op, args) {
        (ChcOp::Not, [ScalarValue::Bool(value)]) => Ok(ScalarValue::Bool(!value)),
        (ChcOp::And | ChcOp::Or, _) => {
            let mut value = op == ChcOp::And;
            for arg in args {
                let ScalarValue::Bool(next) = arg else {
                    return Err(Error::InvalidCandidate);
                };
                value = if op == ChcOp::And {
                    value & *next
                } else {
                    value | *next
                };
            }
            Ok(ScalarValue::Bool(value))
        }
        (ChcOp::Implies, [ScalarValue::Bool(a), ScalarValue::Bool(b)]) => {
            Ok(ScalarValue::Bool(!a || *b))
        }
        (ChcOp::Eq | ChcOp::Ne | ChcOp::Iff, [a, b]) => Ok(ScalarValue::Bool(if op == ChcOp::Ne {
            a != b
        } else {
            a == b
        })),
        (ChcOp::Ite, [ScalarValue::Bool(c), t, e]) => Ok(if *c { *t } else { *e }),
        (ChcOp::BvConcat, _) => concat(args),
        (_, [ScalarValue::BitVec(value, width)]) if canonical(*value, *width) => {
            unary(op, *value, *width, owner)
        }
        (_, [ScalarValue::BitVec(a, width), ScalarValue::BitVec(b, other)])
            if width == other && canonical(*a, *width) && canonical(*b, *width) =>
        {
            binary(op, *a, *b, *width)
        }
        _ => Err(Error::Unsupported),
    }
}

fn binary(op: ChcOp, a: u128, b: u128, width: u32) -> Result<ScalarValue> {
    let (sa, sb) = (signed(a, width), signed(b, width));
    let comparison = match op {
        ChcOp::BvULt => Some(a < b),
        ChcOp::BvULe => Some(a <= b),
        ChcOp::BvUGt => Some(a > b),
        ChcOp::BvUGe => Some(a >= b),
        ChcOp::BvSLt => Some(sa < sb),
        ChcOp::BvSLe => Some(sa <= sb),
        ChcOp::BvSGt => Some(sa > sb),
        ChcOp::BvSGe => Some(sa >= sb),
        _ => None,
    };
    if let Some(value) = comparison {
        return Ok(ScalarValue::Bool(value));
    }
    let value = match op {
        ChcOp::BvAdd => a.wrapping_add(b),
        ChcOp::BvSub => a.wrapping_sub(b),
        ChcOp::BvMul => a.wrapping_mul(b),
        ChcOp::BvAnd => a & b,
        ChcOp::BvOr => a | b,
        ChcOp::BvXor => a ^ b,
        ChcOp::BvNand => !(a & b),
        ChcOp::BvNor => !(a | b),
        ChcOp::BvXnor => !(a ^ b),
        ChcOp::BvUDiv => {
            if b == 0 {
                mask(width)
            } else {
                a / b
            }
        }
        ChcOp::BvURem => {
            if b == 0 {
                a
            } else {
                a % b
            }
        }
        ChcOp::BvSDiv | ChcOp::BvSRem | ChcOp::BvSMod => signed_division(op, a, b, width),
        ChcOp::BvShl => {
            if b >= u128::from(width) {
                0
            } else {
                a << b as u32
            }
        }
        ChcOp::BvLShr => {
            if b >= u128::from(width) {
                0
            } else {
                a >> b as u32
            }
        }
        ChcOp::BvAShr => {
            if b >= u128::from(width) {
                if sa < 0 {
                    mask(width)
                } else {
                    0
                }
            } else {
                (sa >> b as u32) as u128
            }
        }
        ChcOp::BvComp => return Ok(ScalarValue::BitVec(u128::from(a == b), 1)),
        _ => return Err(Error::Unsupported),
    };
    Ok(ScalarValue::BitVec(value & mask(width), width))
}

fn signed_division(op: ChcOp, a: u128, b: u128, width: u32) -> u128 {
    let (sa, sb) = (signed(a, width), signed(b, width));
    if b == 0 {
        return if op == ChcOp::BvSDiv {
            if sa < 0 {
                1
            } else {
                mask(width)
            }
        } else {
            a
        };
    }
    if op == ChcOp::BvSDiv {
        // The only overflowing i128 quotient is MIN/-1; modular BV division
        // returns the MIN bit pattern in that case.
        return sa.checked_div(sb).unwrap_or(i128::MIN) as u128;
    }
    let remainder = sa.checked_rem(sb).unwrap_or(0);
    if op == ChcOp::BvSMod && remainder != 0 && (remainder < 0) != (sb < 0) {
        remainder.wrapping_add(sb) as u128
    } else {
        remainder as u128
    }
}

fn unary(op: ChcOp, value: u128, width: u32, owner: &CountedAdmission) -> Result<ScalarValue> {
    let (value, output) = match op {
        ChcOp::BvNot => (!value, width),
        ChcOp::BvNeg => (0u128.wrapping_sub(value), width),
        ChcOp::BvExtract(high, low) if low <= high && high < width => {
            (value >> low, high - low + 1)
        }
        ChcOp::BvZeroExtend(extra) | ChcOp::BvSignExtend(extra) => {
            let output = width
                .checked_add(extra)
                .filter(|w| *w <= 128)
                .ok_or(Error::Unsupported)?;
            let value = if matches!(op, ChcOp::BvSignExtend(_)) && signed(value, width) < 0 {
                value | !mask(width)
            } else {
                value
            };
            (value, output)
        }
        ChcOp::BvRotateLeft(amount) | ChcOp::BvRotateRight(amount) => {
            let amount = amount % width;
            let value = if amount == 0 {
                value
            } else if matches!(op, ChcOp::BvRotateLeft(_)) {
                (value << amount) | (value >> (width - amount))
            } else {
                (value >> amount) | (value << (width - amount))
            };
            (value, width)
        }
        ChcOp::BvRepeat(count) if count != 0 => {
            let output = width
                .checked_mul(count)
                .filter(|w| *w <= 128)
                .ok_or(Error::Unsupported)?;
            owner.admit(count as usize, 0)?;
            let mut repeated = value;
            for _ in 1..count {
                repeated = (repeated << width) | value;
            }
            (repeated, output)
        }
        _ => return Err(Error::Unsupported),
    };
    Ok(ScalarValue::BitVec(value & mask(output), output))
}

fn concat(args: &[ScalarValue]) -> Result<ScalarValue> {
    let mut value = 0u128;
    let mut width = 0u32;
    for arg in args {
        let ScalarValue::BitVec(next, bits) = arg else {
            return Err(Error::InvalidCandidate);
        };
        if !canonical(*next, *bits) {
            return Err(Error::InvalidCandidate);
        }
        let total = width
            .checked_add(*bits)
            .filter(|w| *w <= 128)
            .ok_or(Error::Unsupported)?;
        value = if width == 0 {
            *next
        } else {
            (value << *bits) | *next
        };
        width = total;
    }
    if width == 0 {
        return Err(Error::InvalidCandidate);
    }
    Ok(ScalarValue::BitVec(value, width))
}
