// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use support::{case, with_owner};

#[test]
fn float16_square_and_minimum_subnormal_have_manual_exact_words_in_every_mode() {
    with_owner(|work| {
        for mode in RM_ORDER {
            // 4 = 2^2, sqrt(4) = 2; minimum f16 subnormal = 2^-24,
            // sqrt(2^-24) = 2^-12. No host floating-point oracle.
            case((5, 11), mode, (false, 17, 0), (false, 16, 0), work);
            case((5, 11), mode, (false, 0, 1), (false, 3, 0), work);
        }
    });
}

#[test]
fn float16_and_small_format_sqrt_two_exclude_every_incorrect_rounded_word() {
    // Exact integer intervals prove the independently written rounding table.
    assert!(1448u64.pow(2) < 2 * 1024u64.pow(2));
    assert!(1449u64.pow(2) > 2 * 1024u64.pow(2));
    assert!(2897u64.pow(2) > 8 * 1024u64.pow(2)); // below midpoint
    assert!(11u64.pow(2) < 2 * 8u64.pow(2));
    assert!(12u64.pow(2) > 2 * 8u64.pow(2));
    assert!(23u64.pow(2) > 8 * 8u64.pow(2)); // below midpoint
    assert!(5u64.pow(2) < 2 * 4u64.pow(2));
    assert!(6u64.pow(2) > 2 * 4u64.pow(2));
    assert!(11u64.pow(2) < 8 * 4u64.pow(2)); // above midpoint
    with_owner(|work| {
        for mode in RM_ORDER {
            let half_sig = if mode == RoundingMode::RTP { 425 } else { 424 };
            case((5, 11), mode, (false, 16, 0), (false, 15, half_sig), work);
            let small_sig = if mode == RoundingMode::RTP { 4 } else { 3 };
            case((3, 4), mode, (false, 4, 0), (false, 3, small_sig), work);
            let tiny_sig = if matches!(mode, RoundingMode::RTZ | RoundingMode::RTN) {
                1
            } else {
                2
            };
            case((2, 3), mode, (false, 2, 0), (false, 1, tiny_sig), work);
        }
    });
}

#[test]
fn native_sqrt_preserves_both_signed_zeros_in_every_mode() {
    with_owner(|work| {
        for mode in RM_ORDER {
            for negative in [false, true] {
                case((5, 11), mode, (negative, 0, 0), (negative, 0, 0), work);
                case((3, 4), mode, (negative, 0, 0), (negative, 0, 0), work);
            }
        }
    });
}

#[test]
fn uninterrupted_public_sqrt_keeps_exact_original_cnf_for_all_literal_modes() {
    let end = Instant::now() + Duration::from_secs(20);
    let terms = TermStore::new();
    for precision in [FpPrecision::Float16, FpPrecision::Custom { eb: 3, sb: 8 }] {
        for mode in RM_ORDER {
            let mut old = FpSolver::new(&terms);
            let old_x = old.fresh_decomposed(precision);
            let expected = old.legacy_make_sqrt(&old_x, mode);
            let mut healthy = FpSolver::new(&terms);
            let x = healthy.fresh_decomposed(precision);
            let actual = healthy.make_sqrt(&x, mode);
            parity::assert_fp(&actual, &expected);
            assert_eq!(healthy.clauses(), old.clauses());
            parity::assert_cache(&healthy.export_cache(), &old.export_cache());
            drop((old, healthy));
            assert!(Instant::now() < end);
        }
    }
}
