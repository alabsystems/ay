// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed admission before copying an owned evaluator value.

use std::mem::size_of;

use ay_core::term::Constant;
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::{ArrayValue, ModelValue};

const MAX_VALUE_COPY_DEPTH: usize = 256;

type Admit<'a> = dyn FnMut(usize, usize) -> Result<(), String> + 'a;

fn overflow() -> String {
    "evaluator payload accounting overflow".to_owned()
}

fn integer(value: &BigInt, admit: &mut Admit<'_>) -> Result<(), String> {
    // A final partial limb can occupy up to eight bytes. No digits are copied
    // while computing this bound.
    let bytes = usize::try_from(value.bits().div_ceil(8))
        .map_err(|_| overflow())?
        .checked_add(8)
        .ok_or_else(overflow)?;
    admit(1, bytes)
}

fn rational(value: &BigRational, admit: &mut Admit<'_>) -> Result<(), String> {
    integer(value.numer(), admit)?;
    integer(value.denom(), admit)
}

fn word_buffer(words: usize, admit: &mut Admit<'_>) -> Result<(), String> {
    let bytes = words.checked_mul(size_of::<u64>()).ok_or_else(overflow)?;
    admit(1, bytes)
}

/// Scratch used by the existing num-bigint 0.4.6 power-of-two remainder.
/// Its borrowed div_rem path still clones the dividend and computes a quotient.
/// Price those buffers and possible Vec growth/shrink destinations before any
/// normalization. Eight-byte cells conservatively cover both limb widths.
fn normalization(value: &BigInt, width: u32, admit: &mut Admit<'_>) -> Result<(), String> {
    let input = usize::try_from(value.bits().div_ceil(64)).map_err(|_| overflow())?;
    let modulus = usize::try_from(u64::from(width) / 64 + 1).map_err(|_| overflow())?;
    // The one-digit power base and the destination of its left shift.
    word_buffer(1, admit)?;
    word_buffer(modulus.checked_add(1).ok_or_else(overflow)?, admit)?;
    word_buffer(input, admit)?;
    if value.bits() > u64::from(width) {
        // Knuth's left-shift normalization can grow the dividend by one digit,
        // reallocating to twice its capacity (at least four). Conservatively
        // retain that payment for the multi-limb path even at shift zero.
        if width >= 32 {
            word_buffer(input.checked_mul(2).ok_or_else(overflow)?.max(4), admit)?;
            if width % 64 != 63 {
                word_buffer(modulus, admit)?;
            }
        }
        let dividend = input.checked_add(1).ok_or_else(overflow)?;
        let quotient = dividend
            .saturating_sub(modulus)
            .checked_add(1)
            .ok_or_else(overflow)?;
        // Quotient plus a possible normalize/shrink destination. The two
        // remainder destinations cover core normalization and its right shift.
        word_buffer(quotient, admit)?;
        word_buffer(quotient, admit)?;
        word_buffer(modulus, admit)?;
        word_buffer(modulus, admit)?;
    }
    if value.sign() == num_bigint::Sign::Minus {
        // r + modulus can grow the remainder's destination, then shrink it.
        word_buffer(modulus.checked_mul(2).ok_or_else(overflow)?.max(4), admit)?;
        word_buffer(modulus, admit)?;
    }
    Ok(())
}

fn children(count: usize, admit: &mut Admit<'_>) -> Result<(), String> {
    // Debit before growing the traversal stack, including for a wide aggregate.
    let bytes = count
        .checked_mul(size_of::<(&ModelValue, usize)>())
        .ok_or_else(overflow)?;
    admit(count, bytes)
}

/// Admit a complete owned-value copy using only borrowed source data.
///
/// `work` counts visited value nodes, aggregate edges, and numeric payloads;
/// `bytes` conservatively accounts for copied value slots, strings, numeric
/// limbs and traversal entries. Every child fanout is admitted BEFORE allocating
/// its traversal entries, and no `ModelValue` is cloned by this function.
/// Copies deeper than the existing 256-level typed-value envelope decline.
/// Refusal, excessive depth or accounting overflow must remain sticky in the caller's owner
/// ledger. This routine grants no value, interpretation, or completion authority.
/// It does not meter arithmetic performed to compute a new value. Resource-only
/// callers invoke it only while their explicit admission scope is active;
/// default-absent model views do not call it.
pub fn admit_model_value_work(
    value: &ModelValue,
    admit: &mut dyn FnMut(usize, usize) -> Result<(), String>,
) -> Result<(), String> {
    admit(1, size_of::<(&ModelValue, usize)>())?;
    let mut pending = vec![(value, 0usize)];
    while let Some((value, depth)) = pending.pop() {
        admit(1, size_of::<ModelValue>())?;
        // ModelValue::clone itself is recursive. Bound its native stack before
        // admitting the copy, matching the evaluator's typed-value depth cap.
        if depth > MAX_VALUE_COPY_DEPTH {
            return Err("model value copy depth limit exceeded".to_owned());
        }
        let child_depth = depth + 1;
        match value {
            // Exact FP limbs are immutable Arc-backed DATA: cloning retains
            // them rather than copying their payload. The value slot itself
            // was admitted above, just as for native fixed-size FP fields.
            ModelValue::Bool(_)
            | ModelValue::FloatingPoint { .. }
            | ModelValue::FloatingPointExact { .. } => {}
            ModelValue::Int(value) => integer(value, admit)?,
            ModelValue::Real(value) => rational(value, admit)?,
            ModelValue::BitVec { value, .. } => integer(value, admit)?,
            ModelValue::Str(value) | ModelValue::Uninterpreted(value) => admit(0, value.len())?,
            ModelValue::Array(array) => {
                admit(0, size_of::<ArrayValue>())?;
                let count = array
                    .store
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(1))
                    .ok_or_else(overflow)?;
                children(count, admit)?;
                pending.push((&array.default, child_depth));
                for (index, value) in &array.store {
                    pending.push((index, child_depth));
                    pending.push((value, child_depth));
                }
            }
            ModelValue::Seq(values) => {
                children(values.len(), admit)?;
                pending.extend(values.iter().map(|value| (value, child_depth)));
            }
            ModelValue::Datatype { ctor, args } => {
                admit(0, ctor.len())?;
                children(args.len(), admit)?;
                pending.extend(args.iter().map(|value| (value, child_depth)));
            }
            ModelValue::Algebraic(value) => {
                admit(0, size_of::<crate::algebraic::Algebraic>())?;
                for polynomial in [value.minimal_polynomial(), value.representation()] {
                    let bytes = polynomial
                        .len()
                        .checked_mul(size_of::<BigRational>())
                        .ok_or_else(overflow)?;
                    admit(polynomial.len(), bytes)?;
                    for coefficient in polynomial {
                        rational(coefficient, admit)?;
                    }
                }
                let (lower, upper) = value.interval();
                rational(lower, admit)?;
                rational(upper, admit)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn admit_constant_work(value: &Constant, admit: &mut Admit<'_>) -> Result<(), String> {
    admit(1, size_of::<ModelValue>())?;
    match value {
        Constant::Int(value) => integer(value, admit),
        Constant::Rational(value) => rational(&value.0, admit),
        Constant::BitVec { value, width } => {
            // Match bitvec::normalize: an already normalized nonnegative
            // payload is copied directly, without a declared-width modulus.
            // Negative or overflowing inputs need that modulus before reduction.
            if *width == 0 {
                admit(1, 0)
            } else if value.sign() == num_bigint::Sign::Minus || value.bits() > u64::from(*width) {
                normalization(value, *width, admit)
            } else {
                integer(value, admit)
            }
        }
        Constant::String(value) => admit(0, value.len()),
        _ => Ok(()),
    }
}
