// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, partial IEEE float-to-bitvector evaluation for strict replay.
use super::*;

#[derive(Clone, Copy)]
pub(super) enum IntTarget {
    Signed,
    Unsigned,
}

/// SMT-LIB checks range AFTER rounding. NaN, infinity and rounded values
/// outside the destination range are under-specified and must remain unknown.
#[cfg(test)]
pub(super) fn fp_to_bv(value: &Fp, rm: Rm, width: u32, target: IntTarget) -> Option<BigInt> {
    with_local_meter(|meter| fp_to_bv_owned(value, rm, width, target, meter))
}

pub(super) fn fp_to_bv_owned(
    value: &Fp,
    rm: Rm,
    width: u32,
    target: IntTarget,
    meter: &mut Meter<'_>,
) -> Option<BigInt> {
    if width == 0 || width > MAX_BV_WIDTH {
        return None;
    }
    let signed = matches!(target, IntTarget::Signed);
    let exact = value.to_rational_owned(meter)?;
    if !rational_is_bounded(&exact) {
        return None;
    }
    let negative = exact.is_negative();
    let absolute = meter.rational_abs(&exact)?;
    let magnitude = round_magnitude_owned(&absolute, rm, negative, meter)?;
    let rounded = if negative { -magnitude } else { magnitude };
    let one = meter.integer(1)?;
    let modulus = meter.shift(&one, i64::from(width))?;
    let upper = if signed {
        meter.shift(&modulus, -1)?
    } else {
        meter.integer_copy(&modulus)?
    };
    let lower = if signed {
        -meter.integer_copy(&upper)?
    } else {
        meter.integer(0)?
    };
    if meter.integer_compare(&rounded, &lower)?.is_lt()
        || !meter.integer_compare(&rounded, &upper)?.is_lt()
    {
        return None;
    }
    if rounded.is_negative() {
        meter.integer_binary(&rounded, &modulus, Arithmetic::Add)
    } else {
        Some(rounded)
    }
}
