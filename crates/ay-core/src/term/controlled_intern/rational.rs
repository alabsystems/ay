// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ratio equality uses recursive Euclidean continued fractions, including for
//! new_raw values. Admit actual division operands before copies/arithmetic and
//! bound its recursion independently of the wrapper's magnitude-only hash.

use super::*;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

pub(super) fn admit(value: &BigRational, admission: &mut Admission<'_>) -> Result<()> {
    if !value.denom().is_positive() {
        return Err(ControlledTermInternError::InvalidInput);
    }
    let payload = value
        .numer()
        .bits()
        .checked_add(value.denom().bits())
        .and_then(|bits| usize::try_from(bits).ok())
        .and_then(|bits| bits.checked_add(7))
        .map(|bits| bits / 8)
        .ok_or(ControlledTermInternError::ResourceLimit)?;
    admission.pay(
        payload
            .checked_add(1)
            .ok_or(ControlledTermInternError::ResourceLimit)?,
        payload
            .checked_mul(4)
            .and_then(|n| n.checked_add(512))
            .ok_or(ControlledTermInternError::ResourceLimit)?,
    )?;
    let mut numerator = value.numer().clone();
    let mut denominator = value.denom().clone();
    let mut work = 0usize;
    let mut bytes = 0usize;
    for _ in 0..128 {
        if denominator.is_zero() {
            // Prepay the subsequent Eq continuation too, before the caller
            // can enter Ratio's recursive comparison implementation.
            admission.pay(work, bytes)?;
            return Ok(());
        }
        let bits = numerator
            .bits()
            .checked_add(denominator.bits())
            .and_then(|bits| usize::try_from(bits).ok())
            .and_then(|bits| bits.checked_add(1))
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        let step_work = bits
            .checked_mul(bits)
            .and_then(|n| n.checked_add(64))
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        let step_bytes = bits
            .checked_add(7)
            .and_then(|n| (n / 8).checked_mul(8))
            .and_then(|n| n.checked_add(512))
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        admission.pay(step_work, step_bytes)?;
        work = work
            .checked_add(step_work)
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        bytes = bytes
            .checked_add(step_bytes)
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        let remainder = numerator.mod_floor(&denominator);
        numerator = denominator;
        denominator = remainder;
    }
    Err(ControlledTermInternError::ResourceLimit)
}
