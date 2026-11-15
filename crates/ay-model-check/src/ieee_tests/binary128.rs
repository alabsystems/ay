// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn power(exponent: i32) -> BigRational {
    if exponent >= 0 {
        BigRational::from_integer(BigInt::from(1) << exponent as usize)
    } else {
        BigRational::new(BigInt::from(1), BigInt::from(1) << (-exponent) as usize)
    }
}

fn fields(sign: bool, exponent: u64, significand: u128) -> FpFields {
    FpFields {
        sign,
        exponent,
        significand,
    }
}

#[test]
fn full_stored_fraction_rounding_sqrt_and_overflow_are_exact() {
    let expected = power(0) + power(-128);
    let square = &expected * &expected;
    let value = Some(fields(false, 3, 1));
    for mode in [
        RoundingMode::NearestTiesToEven,
        RoundingMode::NearestTiesToAway,
        RoundingMode::TowardPositive,
        RoundingMode::TowardNegative,
        RoundingMode::TowardZero,
    ] {
        assert_eq!(round_rational(&expected, 3, 129, mode), value);
        assert_eq!(super::super::sqrt_rational(&square, 3, 129, mode), value);
    }
    assert_eq!(
        round_rational(&power(2), 2, 129, RoundingMode::TowardZero),
        Some(fields(false, 2, u128::MAX))
    );
}

#[test]
fn binary128_round_rational_matches_explicit_boundary_fields() {
    fn require_copy<T: Copy>() {}
    require_copy::<FpFields>();
    let fraction = (1u128 << 112) - 1;
    let max_finite = BigRational::from_integer((BigInt::from(1) << 113usize) - 1) * power(16271);
    for negative in [false, true] {
        for rm in ALL_MODES {
            let away = match rm {
                RoundingMode::TowardPositive => !negative,
                RoundingMode::TowardNegative => negative,
                _ => false,
            };
            let nearest = matches!(
                rm,
                RoundingMode::NearestTiesToEven | RoundingMode::NearestTiesToAway
            );
            for (magnitude, exponent, significand) in [
                (
                    power(0) + power(-113),
                    0x3fff,
                    u128::from(away || rm == RoundingMode::NearestTiesToAway),
                ),
                (
                    power(0) + power(-113) * BigInt::from(3),
                    0x3fff,
                    1 + u128::from(away || nearest),
                ),
                (
                    power(-16495),
                    0,
                    u128::from(away || rm == RoundingMode::NearestTiesToAway),
                ),
                (
                    power(-16382) - power(-16495),
                    u64::from(away || nearest),
                    if away || nearest { 0 } else { fraction },
                ),
                (
                    &max_finite + power(16270),
                    if away || nearest { 0x7fff } else { 0x7ffe },
                    if away || nearest { 0 } else { fraction },
                ),
            ] {
                let input = if negative { -magnitude } else { magnitude };
                assert_eq!(
                    round_rational(&input, 15, 113, rm),
                    Some(fields(negative, exponent, significand))
                );
            }
        }
    }
    let witness = power(0) + power(-1) + power(-112);
    assert_eq!(
        round_rational(&witness, 15, 113, RoundingMode::NearestTiesToEven),
        Some(fields(false, 0x3fff, (1u128 << 111) + 1))
    );
    for (eb, sb) in [(15, 130), (1, 24), (33, 24), (15, u32::MAX)] {
        assert!(round_rational(&power(0), eb, sb, RoundingMode::NearestTiesToEven).is_none());
    }
}

#[test]
fn binary128_sqrt_midpoints_and_carry_use_integer_comparisons() {
    let fraction = (1u128 << 112) - 1;
    for rm in ALL_MODES {
        let up = matches!(
            rm,
            RoundingMode::NearestTiesToAway | RoundingMode::TowardPositive
        );
        let nearest_or_up = matches!(
            rm,
            RoundingMode::NearestTiesToEven
                | RoundingMode::NearestTiesToAway
                | RoundingMode::TowardPositive
        );
        for (root, expected) in [
            (
                power(0) + power(-113),
                fields(false, 0x3fff, u128::from(up)),
            ),
            (
                power(0) + power(-113) * BigInt::from(3),
                fields(false, 0x3fff, 1 + u128::from(nearest_or_up)),
            ),
            (
                power(1) - power(-113),
                if nearest_or_up {
                    fields(false, 0x4000, 0)
                } else {
                    fields(false, 0x3fff, fraction)
                },
            ),
            (power(-16495), fields(false, 0, u128::from(up))),
            (power(-16494), fields(false, 0, 1)),
            (power(-16382), fields(false, 1, 0)),
            (power(1), fields(false, 0x4000, 0)),
        ] {
            // Expectations follow the explicit target midpoint and parity,
            // not either checker kernel or any producer operation.
            let square = &root * &root;
            assert_eq!(
                super::super::sqrt_rational(&square, 15, 113, rm),
                Some(expected)
            );
        }
    }
    for (epsilon, fraction) in [(-power(-115), 0), (power(-115), 1)] {
        let root = power(0) + power(-113) + epsilon;
        assert_eq!(
            super::super::sqrt_rational(&(&root * &root), 15, 113, RoundingMode::NearestTiesToEven),
            Some(fields(false, 0x3fff, fraction))
        );
    }
    for value in [int(-4), int(0)] {
        assert!(
            super::super::sqrt_rational(&value, 15, 113, RoundingMode::NearestTiesToEven).is_none()
        );
    }
    for (eb, sb) in [(1, 113), (15, 130), (15, u32::MAX)] {
        assert!(
            super::super::sqrt_rational(&int(4), eb, sb, RoundingMode::NearestTiesToEven).is_none()
        );
    }
}
