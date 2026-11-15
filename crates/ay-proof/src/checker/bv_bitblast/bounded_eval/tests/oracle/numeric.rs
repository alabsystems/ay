// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

pub(super) fn eval_bv_shift(name: &str, lhs: u64, rhs: u64, width: u32) -> u64 {
    let mask = bv_mask(width);
    let shift = rhs;
    match name {
        "bvshl" if shift < u64::from(width) => (lhs << shift) & mask,
        "bvlshr" if shift < u64::from(width) => (lhs >> shift) & mask,
        // shl / lshr over-shift (shift >= width) saturate to zero.
        "bvshl" | "bvlshr" => 0,
        "bvashr" => {
            let negative = width > 0 && (lhs >> (width - 1)) & 1 == 1;
            if shift >= u64::from(width) {
                // Over-shift fills with the sign bit: all-ones / all-zeros.
                if negative {
                    mask
                } else {
                    0
                }
            } else {
                let logical = (lhs >> shift) & mask;
                if negative {
                    // Set the top `shift` vacated bits to 1 (sign fill).
                    (logical | (mask ^ (mask >> shift))) & mask
                } else {
                    logical
                }
            }
        }
        _ => unreachable!("eval_bv_shift only called for bvshl/bvlshr/bvashr"),
    }
}

pub(super) fn to_signed_u64(value: u64, width: u32) -> i64 {
    if width == 0 {
        return 0;
    }
    if width >= u64::BITS {
        return value as i64;
    }
    if (value >> (width - 1)) & 1 == 1 {
        (value as i64).wrapping_sub(1i64 << width)
    } else {
        value as i64
    }
}

pub(super) fn eval_bv_signed_divrem(name: &str, lhs: u64, rhs: u64, width: u32) -> u64 {
    let mask = bv_mask(width);
    let a = to_signed_u64(lhs, width);
    let b = to_signed_u64(rhs, width);
    let pack = |s: i64| -> u64 { (s as u64) & mask };
    match name {
        "bvsdiv" => {
            if b == 0 {
                pack(if a >= 0 { -1 } else { 1 })
            } else {
                pack(a.wrapping_div(b))
            }
        }
        "bvsrem" => {
            if b == 0 {
                lhs
            } else {
                pack(a.wrapping_rem(b))
            }
        }
        "bvsmod" => {
            if b == 0 {
                lhs
            } else {
                let r = a.wrapping_rem(b);
                let m = if r == 0 || (r < 0) == (b < 0) {
                    r
                } else {
                    r + b
                };
                pack(m)
            }
        }
        _ => unreachable!("eval_bv_signed_divrem only for bvsdiv/bvsrem/bvsmod"),
    }
}

pub(super) fn bv_mask(width: u32) -> u64 {
    if width >= u64::BITS {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}
