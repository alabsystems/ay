// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, canonical exact coefficients. Every operation polls the existing
//! proof caller before allocating and rejects growth before the next operation.

use super::super::nra_poly::{bit_scaled, rat_bits};
use super::*;
use num_bigint::BigInt;

pub(super) fn fits(value: &BigRational) -> Result<(), String> {
    if value.numer().bits() > NraSosRational::MAX_BITS
        || value.denom().bits() > NraSosRational::MAX_BITS
    {
        return Err(WORK_METER_RESOURCE_LIMIT.to_string());
    }
    if !value.denom().is_positive() {
        return Err("invalid rational denominator".to_string());
    }
    Ok(())
}

pub(super) fn decode(
    value: &NraSosRational,
    meter: &mut WorkMeter<'_>,
) -> Result<BigRational, String> {
    value.validate_shape().map_err(|error| match error {
        NraSosShapeError::Limit => WORK_METER_RESOURCE_LIMIT.to_string(),
        NraSosShapeError::Malformed => "invalid rational denominator".to_string(),
    })?;
    let bits = value.numerator.bits() + value.denominator.bits();
    meter.charge_ops(bit_scaled(1, bits))?;
    meter.charge_rational_scratch(bits.saturating_mul(2))?;
    let mut numerator = value.numerator.abs();
    let mut denominator = value.denominator.clone();
    while !denominator.is_zero() {
        meter.charge_ops(bit_scaled(1, numerator.bits().max(denominator.bits())))?;
        meter.charge_rational_scratch(numerator.bits() + denominator.bits())?;
        let remainder = &numerator % &denominator;
        numerator = denominator;
        denominator = remainder;
    }
    if numerator != BigInt::one() {
        return Err("noncanonical rational coefficient".to_string());
    }
    meter.charge_rational_scratch(bits)?;
    Ok(BigRational::new_raw(
        value.numerator.clone(),
        value.denominator.clone(),
    ))
}

pub(super) fn copy(value: &BigRational, meter: &mut WorkMeter<'_>) -> Result<BigRational, String> {
    fits(value)?;
    meter.charge_ops(bit_scaled(1, rat_bits(value)))?;
    meter.charge_rational_scratch(rat_bits(value))?;
    Ok(value.clone())
}

pub(super) enum Operation {
    Subtract,
    Multiply,
    Divide,
}

pub(super) fn binary(
    left: &BigRational,
    right: &BigRational,
    operation: Operation,
    meter: &mut WorkMeter<'_>,
) -> Result<BigRational, String> {
    fits(left)?;
    fits(right)?;
    meter.charge_ops(bit_scaled(1, rat_bits(left).max(rat_bits(right))))?;
    meter.charge_rational_scratch(rat_bits(left) + rat_bits(right) + 2)?;
    let result = match operation {
        Operation::Subtract => left - right,
        Operation::Multiply => left * right,
        Operation::Divide => {
            if right.is_zero() {
                return Err("zero matrix pivot divisor".to_string());
            }
            left / right
        }
    };
    fits(&result)?;
    Ok(result)
}
