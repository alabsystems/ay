// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Correctly-rounded conversion of a rational CONSTANT to an IEEE-754 bit
//! pattern.
//!
//! This is the exact value of `((_ to_fp eb sb) rm <real-literal>)` when both
//! the rounding mode and the real are constants — the standard way FP literals
//! are written in SMT-LIB. The result is the IEEE bit pattern, which the caller
//! reinterprets via the (already supported) 1-argument `(_ to_fp eb sb) <BV>`
//! form, so no new bit-blasting path is required.

use crate::RoundingMode;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// `2^e` as an exact rational (handles negative `e`).
fn pow2_rational(e: i64) -> BigRational {
    if e >= 0 {
        BigRational::from(BigInt::from(2).pow(e as u32))
    } else {
        BigRational::new(BigInt::one(), BigInt::from(2).pow((-e) as u32))
    }
}

/// Correctly round `value` to the IEEE-754 format with `eb` exponent bits and
/// `sb` significand bits (INCLUDING the hidden bit), under rounding mode `rm`,
/// returning the `eb + sb`-bit pattern as a non-negative [`BigInt`].
///
/// Layout (most- to least-significant): `[sign:1][biased_exp:eb][stored_sig:sb-1]`.
///
/// Handles signed zero, normals, subnormals, rounding carry (significand
/// overflow bumping the exponent), and overflow to infinity / max-finite per the
/// rounding mode. `value == 0` yields `+0` (a literal `-0.0` is interned as `0`
/// before this point, matching the other solvers).
pub fn round_rational_to_ieee_bits(
    value: &BigRational,
    eb: u32,
    sb: u32,
    rm: RoundingMode,
) -> BigInt {
    debug_assert!(eb >= 2 && sb >= 2, "degenerate FP format eb={eb} sb={sb}");

    let sign_neg = value.is_negative();
    let sign_bit = if sign_neg {
        BigInt::one()
    } else {
        BigInt::zero()
    };
    let total_bits = eb + sb;
    let sig_field_bits = sb - 1; // stored significand width (no hidden bit)

    let bias: i64 = (1i64 << (eb - 1)) - 1;
    let emin: i64 = 1 - bias; // smallest unbiased exponent of a normal
                              // (the largest normal exponent is `bias`; overflow is detected below via
                              // `biased_exp >= max_biased`.)
    let max_biased = (BigInt::from(1) << eb) - 1; // all-ones exponent (inf/nan)

    let assemble = |sign: &BigInt, biased_exp: &BigInt, stored_sig: &BigInt| -> BigInt {
        (sign << (total_bits - 1)) + (biased_exp << sig_field_bits) + stored_sig
    };

    let a = value.abs();
    if a.is_zero() {
        // Signed zero: biased_exp = 0, stored_sig = 0.
        return assemble(&sign_bit, &BigInt::zero(), &BigInt::zero());
    }

    // Unbiased exponent e = floor(log2(a)). Start from a bit-length estimate,
    // then correct by at most a couple of steps.
    let num_bits = a.numer().abs().bits() as i64;
    let den_bits = a.denom().abs().bits() as i64;
    let mut e = num_bits - den_bits;
    while pow2_rational(e) > a {
        e -= 1;
    }
    while pow2_rational(e + 1) <= a {
        e += 1;
    }

    // Scale so the unit-in-the-last-place sits at 2^(target_exp - (sb-1)).
    let target_exp = e.max(emin);
    let shift = (sb as i64 - 1) - target_exp;
    let scaled = &a * pow2_rational(shift);
    let q_floor = scaled.floor().to_integer();
    let frac = &scaled - BigRational::from(q_floor.clone());
    let half = BigRational::new(BigInt::one(), BigInt::from(2));

    // Decide whether to round the magnitude up by one ULP.
    let q_floor_is_odd = (&q_floor % BigInt::from(2)).is_one();
    let round_up = match rm {
        RoundingMode::RNE => frac > half || (frac == half && q_floor_is_odd),
        RoundingMode::RNA => frac >= half,
        RoundingMode::RTZ => false,
        RoundingMode::RTP => !sign_neg && frac.is_positive(),
        RoundingMode::RTN => sign_neg && frac.is_positive(),
    };
    let mut q = if round_up { q_floor + 1 } else { q_floor };

    let sig_top = BigInt::from(1) << sig_field_bits; // 2^(sb-1): the hidden-bit weight
    let two_sb = BigInt::from(1) << sb; // 2^sb

    // Resolve into (biased_exp, stored_sig), handling rounding carry.
    let (biased_exp, stored_sig): (BigInt, BigInt) = if target_exp == emin {
        // Subnormal regime (or the smallest normal after a carry).
        if q < sig_top {
            (BigInt::zero(), q) // subnormal
        } else {
            // Carried up to (or past) the smallest normal.
            let mut e_norm = emin;
            while q >= two_sb {
                q >>= 1;
                e_norm += 1;
            }
            (BigInt::from(e_norm + bias), &q - &sig_top)
        }
    } else {
        // Normal regime; a rounding carry can push q to 2^sb (→ exponent + 1).
        let mut e_norm = e;
        if q >= two_sb {
            q >>= 1;
            e_norm += 1;
        }
        (BigInt::from(e_norm + bias), &q - &sig_top)
    };

    // Overflow: a biased exponent of all-ones (or beyond) is reserved for
    // inf/nan, so a finite result that lands there overflows per `rm`.
    if biased_exp >= max_biased {
        let to_infinity = match rm {
            RoundingMode::RNE | RoundingMode::RNA => true,
            RoundingMode::RTZ => false,
            RoundingMode::RTP => !sign_neg,
            RoundingMode::RTN => sign_neg,
        };
        return if to_infinity {
            assemble(&sign_bit, &max_biased, &BigInt::zero())
        } else {
            // Largest finite: biased_exp = max_biased - 1, stored_sig = all ones.
            let max_finite_exp = &max_biased - 1;
            let all_ones_sig = (BigInt::from(1) << sig_field_bits) - 1;
            assemble(&sign_bit, &max_finite_exp, &all_ones_sig)
        };
    }

    assemble(&sign_bit, &biased_exp, &stored_sig)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bits_f32(v: f64, rm: RoundingMode) -> u32 {
        let r = BigRational::from_float(v).unwrap();
        round_rational_to_ieee_bits(&r, 8, 24, rm)
            .try_into()
            .unwrap()
    }

    #[test]
    fn round_f32_exact_powers_and_simple() {
        // Exactly representable values must match Rust's f32 bit pattern.
        for v in [0.0f32, 1.0, 0.5, 2.0, -1.0, 1.5, -0.25, 3.0, 256.0, 0.125] {
            let got = bits_f32(v as f64, RoundingMode::RNE);
            assert_eq!(
                got,
                v.to_bits(),
                "value {v}: got {got:#x} want {:#x}",
                v.to_bits()
            );
        }
    }

    #[test]
    fn round_f32_rne_matches_native() {
        // Native f32 conversion rounds to nearest-even; our RNE must agree.
        for v in [0.1f64, 0.2, 1.0 / 3.0, 123456.789, -98765.4321, 1e20, 1e-20] {
            let got = bits_f32(v, RoundingMode::RNE);
            assert_eq!(got, (v as f32).to_bits(), "value {v}");
        }
    }

    #[test]
    fn round_f32_overflow_to_infinity() {
        // Above the largest finite f32 (~3.4e38): RNE/RNA -> inf, RTZ -> max finite.
        let big = BigRational::from_integer(BigInt::from(10).pow(40));
        let inf = round_rational_to_ieee_bits(&big, 8, 24, RoundingMode::RNE);
        assert_eq!(u32::try_from(inf).unwrap(), f32::INFINITY.to_bits());
        let maxf = round_rational_to_ieee_bits(&big, 8, 24, RoundingMode::RTZ);
        assert_eq!(u32::try_from(maxf).unwrap(), f32::MAX.to_bits());
    }

    #[test]
    fn round_f32_directed_modes() {
        // 1/3 is not representable: RTP yields the ceiling neighbor, RTN the
        // floor neighbor (positive value); they are adjacent and RNE picks one.
        let third = BigRational::new(BigInt::one(), BigInt::from(3));
        let up = u32::try_from(round_rational_to_ieee_bits(
            &third,
            8,
            24,
            RoundingMode::RTP,
        ))
        .unwrap();
        let down = u32::try_from(round_rational_to_ieee_bits(
            &third,
            8,
            24,
            RoundingMode::RTN,
        ))
        .unwrap();
        let rtz = u32::try_from(round_rational_to_ieee_bits(
            &third,
            8,
            24,
            RoundingMode::RTZ,
        ))
        .unwrap();
        let native = (1.0f32 / 3.0).to_bits();
        assert_eq!(up, down + 1, "RTP/RTN neighbors must be adjacent");
        assert!(native == up || native == down, "RNE must pick a neighbor");
        // Positive value: round-toward-zero == round-toward-negative == floor.
        assert_eq!(rtz, down, "RTZ on a positive value equals RTN");
    }

    #[test]
    fn round_f64_matches_native() {
        for v in [0.1f64, 1.0 / 7.0, -2.5, 1e300, 5e-324, 1.0] {
            let r = BigRational::from_float(v).unwrap();
            let got = round_rational_to_ieee_bits(&r, 11, 53, RoundingMode::RNE);
            assert_eq!(u64::try_from(got).unwrap(), v.to_bits(), "value {v}");
        }
    }

    #[test]
    fn round_f16_smallest_subnormal() {
        // Float16 smallest positive subnormal = 2^-24; bit pattern 0x0001.
        let tiny = pow2_rational(-24);
        let bits = round_rational_to_ieee_bits(&tiny, 5, 11, RoundingMode::RNE);
        assert_eq!(u16::try_from(bits).unwrap(), 0x0001);
    }
}
