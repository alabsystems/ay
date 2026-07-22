// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared bitvector arithmetic utilities for ay-chc.
//!
//! Consolidates `bv_mask`, `bv_apply_mask`, and `bv_to_signed` which were
//! previously duplicated across problem.rs, expr/evaluate.rs, mbp/eval_bv.rs,
//! and mbp/theory.rs.

/// Return a u128 with the lower `width` bits set: `(1 << w) - 1`.
/// Returns `u128::MAX` for `width >= 128`.
pub(crate) fn bv_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Mask a u128 value to the lower `width` bits.
pub(crate) fn bv_apply_mask(val: u128, width: u32) -> u128 {
    if width >= 128 {
        val
    } else {
        val & ((1u128 << width) - 1)
    }
}

/// Interpret an unsigned BV value as signed (two's complement).
///
/// For `width < 128`: if the sign bit is set, sign-extend to i128.
/// For `width == 128`: reinterpret bits as i128.
/// For `width == 0`: returns 0.
pub(crate) fn bv_to_signed(val: u128, width: u32) -> i128 {
    if width == 0 {
        return 0;
    }
    let masked = bv_apply_mask(val, width);
    if width >= 128 {
        return masked as i128;
    }
    let sign_bit = 1u128 << (width - 1);
    if masked & sign_bit != 0 {
        // Negative: sign-extend by ORing with high bits
        (masked | !bv_mask(width)) as i128
    } else {
        masked as i128
    }
}
