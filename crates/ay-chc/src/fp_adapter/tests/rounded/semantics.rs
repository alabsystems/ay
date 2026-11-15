// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use support::{nan, word};

#[test]
fn square_root_exact_squares_and_irrational_rounding_have_manual_words() {
    with_owner(20, |budget| {
        for (width, four, two, root_two, nearest_up) in [
            (32, 0x40800000u64, 0x40000000u64, 0x3fb504f3u64, false),
            (
                64,
                0x4010000000000000,
                0x4000000000000000,
                0x3ff6a09e667f3bcc,
                true,
            ),
        ] {
            for rm in ay_fp::RM_ORDER {
                let up = match rm {
                    RoundingMode::RNE | RoundingMode::RNA => nearest_up,
                    RoundingMode::RTP => true,
                    RoundingMode::RTN | RoundingMode::RTZ => false,
                };
                word("fp.sqrt", width, &[four], rm, two, budget);
                word(
                    "fp.sqrt",
                    width,
                    &[two],
                    rm,
                    root_two + u64::from(up),
                    budget,
                );
            }
        }
    });
}

#[test]
fn fused_product_cancellation_retains_bits_lost_by_separate_mul_and_add() {
    with_owner(10, |budget| {
        for (width, x, y, z, expected) in [
            (
                32,
                0x3f800001u64,
                0x3f7ffffeu64,
                0xbf800000u64,
                0xa8800000u64,
            ),
            (
                64,
                0x3ff0000000000001,
                0x3feffffffffffffe,
                0xbff0000000000000,
                0xb970000000000000,
            ),
        ] {
            // (1+2^-p)*(1-2^-p)-1 = -2^(-2p), p=23/52.
            for rm in ay_fp::RM_ORDER {
                word("fp.fma", width, &[x, y, z], rm, expected, budget);
            }
        }
    });
}

#[test]
fn fused_half_ulp_ties_keep_both_signs_under_all_five_modes() {
    with_owner(20, |budget| {
        for (width, one, half, sign) in [
            (32, 0x3f800000u64, 0x33800000u64, 1u64 << 31),
            (64, 0x3ff0000000000000, 0x3ca0000000000000, 1u64 << 63),
        ] {
            for rm in ay_fp::RM_ORDER {
                let up = matches!(rm, RoundingMode::RNA | RoundingMode::RTP);
                let down = matches!(rm, RoundingMode::RNA | RoundingMode::RTN);
                word(
                    "fp.fma",
                    width,
                    &[one, one, half],
                    rm,
                    one + u64::from(up),
                    budget,
                );
                word(
                    "fp.fma",
                    width,
                    &[sign | one, one, sign | half],
                    rm,
                    sign | (one + u64::from(down)),
                    budget,
                );
            }
        }
    });
}

#[test]
fn square_root_preserves_signed_zero_and_exact_min_normal_square_root() {
    with_owner(30, |budget| {
        for (width, sign, min_normal, expected) in [
            (32, 1u64 << 31, 0x00800000u64, 0x20000000u64),
            (64, 1u64 << 63, 0x0010000000000000, 0x2000000000000000),
        ] {
            for rm in ay_fp::RM_ORDER {
                word("fp.sqrt", width, &[0], rm, 0, budget);
                word("fp.sqrt", width, &[sign], rm, sign, budget);
                word("fp.sqrt", width, &[min_normal], rm, expected, budget);
            }
        }
    });
}

#[test]
fn fused_cancellation_zero_factor_and_min_subnormal_keep_exact_signs() {
    with_owner(30, |budget| {
        for (width, one, two, sign) in [
            (32, 0x3f800000u64, 0x40000000u64, 1u64 << 31),
            (64, 0x3ff0000000000000, 0x4000000000000000, 1u64 << 63),
        ] {
            for rm in ay_fp::RM_ORDER {
                let zero = if rm == RoundingMode::RTN { sign } else { 0 };
                word("fp.fma", width, &[one, two, sign | two], rm, zero, budget);
                word("fp.fma", width, &[0, one, sign], rm, zero, budget);
                word("fp.fma", width, &[1, one, 0], rm, 1, budget);
            }
        }
    });
}

#[test]
fn rounded_invalid_and_nonfinite_arithmetic_never_promises_nan_payloads() {
    with_owner(16, |budget| {
        for (width, one, sign, infinity, quiet) in [
            (32, 0x3f800000u64, 1u64 << 31, 0x7f800000u64, 0x7fc00001u64),
            (
                64,
                0x3ff0000000000000,
                1u64 << 63,
                0x7ff0000000000000,
                0x7ff8000000000001,
            ),
        ] {
            for x in [sign | one, quiet, sign | infinity] {
                nan("fp.sqrt", width, &[x], budget);
            }
            word(
                "fp.sqrt",
                width,
                &[infinity],
                RoundingMode::RNE,
                infinity,
                budget,
            );
            for args in [
                [0, infinity, one],
                [infinity, one, sign | infinity],
                [quiet, one, 0],
            ] {
                nan("fp.fma", width, &args, budget);
            }
            word(
                "fp.fma",
                width,
                &[infinity, one, one],
                RoundingMode::RNE,
                infinity,
                budget,
            );
        }
    });
}

#[test]
fn fused_overflow_selects_inf_or_maximum_without_rounding_mode_refund() {
    with_owner(20, |budget| {
        for (width, max, two, sign, inf) in [
            (32, 0x7f7fffffu64, 0x40000000u64, 1u64 << 31, 0x7f800000u64),
            (
                64,
                0x7fefffffffffffff,
                0x4000000000000000,
                1u64 << 63,
                0x7ff0000000000000,
            ),
        ] {
            for rm in ay_fp::RM_ORDER {
                let pos = if matches!(rm, RoundingMode::RTN | RoundingMode::RTZ) {
                    max
                } else {
                    inf
                };
                let neg = if matches!(rm, RoundingMode::RTP | RoundingMode::RTZ) {
                    max
                } else {
                    inf
                };
                word("fp.fma", width, &[max, two, 0], rm, pos, budget);
                word(
                    "fp.fma",
                    width,
                    &[sign | max, two, sign],
                    rm,
                    sign | neg,
                    budget,
                );
            }
        }
    });
}
