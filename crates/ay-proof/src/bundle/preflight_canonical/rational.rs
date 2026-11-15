// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Numeric rational equality with locally metered, iterative arithmetic.
//!
//! num-rational's Eq recurses through division; num-bigint multiplication can
//! select Karatsuba or Toom-3 with internal scratch allocations. Neither is a
//! caller-metered operation. Only borrowed digit iterators are used here.

use num_bigint::BigInt;
use num_rational::BigRational;

use super::*;

pub(super) fn equal(
    left: &BigRational,
    right: &BigRational,
    meter: &mut CanonicalMeter<'_>,
) -> Result<bool, ProofCheckError> {
    meter.charge(1, 0)?;
    if left.denom().sign() == Sign::NoSign || right.denom().sign() == Sign::NoSign {
        meter.charge(64, 64)?;
        return Err(malformed_bundle(
            "rational canonical entry has a zero denominator",
        ));
    }
    let left_zero = left.numer().sign() == Sign::NoSign;
    let right_zero = right.numer().sign() == Sign::NoSign;
    if left_zero || right_zero {
        return Ok(left_zero && right_zero);
    }
    let left_negative = (left.numer().sign() == Sign::Minus) ^ (left.denom().sign() == Sign::Minus);
    let right_negative =
        (right.numer().sign() == Sign::Minus) ^ (right.denom().sign() == Sign::Minus);
    if left_negative != right_negative {
        return Ok(false);
    }
    if integers_equal(left.denom(), right.denom(), meter)? {
        return integers_equal(left.numer(), right.numer(), meter);
    }
    if integers_equal(left.numer(), right.numer(), meter)? {
        return Ok(false);
    }
    let left_product = product(left.numer(), right.denom(), meter)?;
    let right_product = product(right.numer(), left.denom(), meter)?;
    limbs_equal(&left_product, &right_product, meter)
}

fn integers_equal(
    left: &BigInt,
    right: &BigInt,
    meter: &mut CanonicalMeter<'_>,
) -> Result<bool, ProofCheckError> {
    meter.charge(1, 0)?;
    if left.sign() != right.sign() {
        return Ok(false);
    }
    let mut left_digits = left.iter_u32_digits();
    let mut right_digits = right.iter_u32_digits();
    if left_digits.len() != right_digits.len() {
        return Ok(false);
    }
    loop {
        meter.charge(1, 0)?;
        match (left_digits.next(), right_digits.next()) {
            (None, None) => return Ok(true),
            (Some(left), Some(right)) if left == right => {}
            _ => return Ok(false),
        }
    }
}

fn product(
    left: &BigInt,
    right: &BigInt,
    meter: &mut CanonicalMeter<'_>,
) -> Result<Vec<u32>, ProofCheckError> {
    meter.charge(1, 0)?;
    let mut left_digits = left.iter_u32_digits();
    let right_len = right.iter_u32_digits().len();
    let length = meter::add(left_digits.len(), right_len)?;
    let mut output = meter.zero_limbs(length)?;
    let mut row = 0usize;
    loop {
        meter.charge(1, 0)?;
        let Some(left_digit) = left_digits.next() else {
            break;
        };
        let mut right_digits = right.iter_u32_digits();
        let mut column = 0usize;
        let mut carry = 0u64;
        loop {
            meter.charge(1, 0)?;
            let Some(right_digit) = right_digits.next() else {
                break;
            };
            let index = meter::add(row, column)?;
            let slot = output
                .get_mut(index)
                .ok_or(ProofCheckError::ResourceLimit)?;
            // With base B=2^32, (B-1)^2 + (B-1) + (B-1) = 2^64-1.
            // Checked arithmetic keeps that bound fail-closed if this changes.
            let sum = u64::from(left_digit)
                .checked_mul(u64::from(right_digit))
                .and_then(|value| value.checked_add(u64::from(*slot)))
                .and_then(|value| value.checked_add(carry))
                .ok_or(ProofCheckError::ResourceLimit)?;
            *slot = sum as u32;
            carry = sum >> 32;
            column = meter::add(column, 1)?;
        }
        meter.charge(1, 0)?;
        let index = meter::add(row, right_len)?;
        // Earlier rows end strictly before this slot, so it is still zero:
        // assigning the final carry needs no unmetered propagation chain.
        *output
            .get_mut(index)
            .ok_or(ProofCheckError::ResourceLimit)? = carry as u32;
        row = meter::add(row, 1)?;
    }
    loop {
        meter.charge(1, 0)?;
        match output.last() {
            Some(0) => {
                output.pop();
            }
            _ => break,
        }
    }
    Ok(output)
}

fn limbs_equal(
    left: &[u32],
    right: &[u32],
    meter: &mut CanonicalMeter<'_>,
) -> Result<bool, ProofCheckError> {
    meter.charge(1, 0)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    let mut left_digits = left.iter();
    let mut right_digits = right.iter();
    loop {
        meter.charge(1, 0)?;
        match (left_digits.next(), right_digits.next()) {
            (None, None) => return Ok(true),
            (Some(left), Some(right)) if left == right => {}
            _ => return Ok(false),
        }
    }
}
