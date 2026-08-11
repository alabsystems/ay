// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact IEEE 754 rounding, for confirming floating-point models.
//!
//! # Why this exists
//!
//! `(_ to_fp eb sb) rm x` rounds an exact value into a floating-point format.
//! The independent gate declined every rounding form on purpose: confirming a
//! rounded model with the SOLVER's rounding routine is not independent, and an
//! approximate reimplementation could confirm a WRONG model. Only the exact
//! bit-reinterpret form was handled.
//!
//! So this is a second, separate implementation, written from the IEEE 754
//! rounding rules rather than from `ay-theories/fp`. Every step is exact
//! rational arithmetic — no `f32`/`f64` appears anywhere, because rounding
//! through a hardware float is precisely the approximation that would let a
//! wrong witness through.
//!
//! # What is covered
//!
//! Rounding an exact rational to a format `(eb, sb)` under all five SMT-LIB
//! modes, including subnormals, the carry out of a rounded significand,
//! and overflow (which yields infinity or the largest finite value, per mode).

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// The five SMT-LIB rounding modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoundingMode {
    /// `RNE` — nearest, ties to even.
    NearestTiesToEven,
    /// `RNA` — nearest, ties away from zero.
    NearestTiesToAway,
    /// `RTP` — toward positive infinity.
    TowardPositive,
    /// `RTN` — toward negative infinity.
    TowardNegative,
    /// `RTZ` — toward zero.
    TowardZero,
}

impl RoundingMode {
    /// Parse an SMT-LIB rounding-mode name, short or long spelling.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "RNE" | "roundNearestTiesToEven" => Self::NearestTiesToEven,
            "RNA" | "roundNearestTiesToAway" => Self::NearestTiesToAway,
            "RTP" | "roundTowardPositive" => Self::TowardPositive,
            "RTN" | "roundTowardNegative" => Self::TowardNegative,
            "RTZ" | "roundTowardZero" => Self::TowardZero,
            _ => return None,
        })
    }
}

/// The encoded fields of a floating-point value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FpFields {
    /// Sign bit (`true` means negative).
    pub sign: bool,
    /// Biased exponent field.
    pub exponent: u64,
    /// Stored fraction, without the hidden bit.
    pub significand: u64,
}

/// `2^e` exactly, or `None` when the shift would be absurd.
///
/// The bound is not defensive padding: a shift width is an allocation size, and
/// clamping an out-of-range one (rather than refusing) would turn a nonsense
/// exponent into a multi-gigabyte integer.
fn pow2(e: i64) -> Option<BigRational> {
    const MAX_SHIFT: i64 = 1 << 24;
    if !(-MAX_SHIFT..=MAX_SHIFT).contains(&e) {
        return None;
    }
    let one = BigInt::one();
    Some(if e >= 0 {
        BigRational::from(one << u32::try_from(e).ok()?)
    } else {
        BigRational::new(one.clone(), one << u32::try_from(-e).ok()?)
    })
}

/// `floor(log2(a))` for `a > 0`, exactly.
///
/// The bit-length difference is within one of the answer, so the correction
/// runs at most a couple of times.
fn floor_log2(a: &BigRational) -> Option<i64> {
    let estimate = i64::try_from(a.numer().bits()).ok()? - i64::try_from(a.denom().bits()).ok()?;
    correct_log2(a, estimate)
}

/// Walk an estimate of `floor(log2(a))` to the exact answer, for `a > 0`.
///
/// The bit-length estimate is never *below* the true value — `floor(log2 n) -
/// floor(log2 d) >= floor(log2(n/d))` for every reduced `n/d` — so from
/// `floor_log2` only the downward loop ever fires. The upward loop is kept so
/// the routine is correct for ANY starting estimate rather than resting on that
/// argument; `log2_correction_converges_from_a_wrong_start` exercises it.
fn correct_log2(a: &BigRational, mut e: i64) -> Option<i64> {
    while pow2(e)? > *a {
        e = e.checked_sub(1)?;
    }
    while pow2(e.checked_add(1)?)? <= *a {
        e = e.checked_add(1)?;
    }
    Some(e)
}

/// Round a rational to an integer under `rm`, honouring its sign.
///
/// This is `fp.roundToIntegral` and the integer half of `fp.to_ubv` /
/// `fp.to_sbv` / `fp.rem`: the same tie and direction rules as
/// [`round_rational`], stopping at the integer rather than continuing into a
/// format.
#[must_use]
pub fn round_to_integer(value: &BigRational, rm: RoundingMode) -> BigInt {
    let negative = value.is_negative();
    let magnitude = round_magnitude(&value.abs(), negative, rm);
    if negative {
        -magnitude
    } else {
        magnitude
    }
}

/// Round a non-negative rational to an integer under `rm`, given the value's
/// sign (which the directed modes need).
fn round_magnitude(q: &BigRational, negative: bool, rm: RoundingMode) -> BigInt {
    let floor = q.floor().to_integer();
    let remainder = q - BigRational::from(floor.clone());
    if remainder.is_zero() {
        return floor;
    }
    let up = floor.clone() + 1;
    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    match rm {
        RoundingMode::TowardZero => floor,
        // The magnitude grows only when rounding away from zero, so a directed
        // mode depends on the SIGN of the value it is rounding.
        RoundingMode::TowardPositive => {
            if negative {
                floor
            } else {
                up
            }
        }
        RoundingMode::TowardNegative => {
            if negative {
                up
            } else {
                floor
            }
        }
        RoundingMode::NearestTiesToAway => {
            if remainder < half {
                floor
            } else {
                up
            }
        }
        RoundingMode::NearestTiesToEven => {
            if remainder < half {
                floor
            } else if remainder > half {
                up
            } else if floor.is_even() {
                floor
            } else {
                up
            }
        }
    }
}

trait IsEven {
    fn is_even(&self) -> bool;
}

impl IsEven for BigInt {
    fn is_even(&self) -> bool {
        (self % BigInt::from(2)).is_zero()
    }
}

/// Round an exact rational into the format `(eb, sb)` under `rm`.
///
/// `sb` counts the hidden bit, so the stored fraction has `sb - 1` bits.
///
/// Returns `None` rather than a guess whenever an invariant does not hold — an
/// unrepresentable format, or a significand that lands outside its own range.
/// This routine backs a model-confirmation gate, and a clamped-to-something
/// answer there is a wrong float that *looks* well-formed, which is exactly how
/// a bad witness gets confirmed. `None` makes the gate report
/// `CannotConfirm` instead.
#[must_use]
pub fn round_rational(value: &BigRational, eb: u32, sb: u32, rm: RoundingMode) -> Option<FpFields> {
    // The fields are returned in a `u64` each, and `1 << (eb - 1)` must not
    // wrap; every SMT-LIB format in practice is far inside this.
    if !(2..=32).contains(&eb) || !(2..=64).contains(&sb) {
        return None;
    }
    let negative = value.is_negative();
    let max_exponent_field = (1u64 << eb) - 1;
    let bias = (1i64 << (eb - 1)) - 1;
    let emax = bias;
    let emin = 1 - bias;
    let fraction_bits = sb - 1;
    let hidden = BigInt::one() << fraction_bits;

    if value.is_zero() {
        // An exact rational zero carries no sign, so this is `+0`. The signed
        // zero that DOES arise — a tiny negative value underflowing — comes out
        // of the subnormal path below, which keeps the value's sign.
        return Some(FpFields {
            sign: false,
            exponent: 0,
            significand: 0,
        });
    }

    let magnitude = value.abs();
    let exponent = floor_log2(&magnitude)?;

    // Subnormal: the value is below the smallest normal, so the significand is
    // scaled against a FIXED exponent rather than the value's own.
    if exponent < emin {
        let scale = pow2(emin - i64::from(fraction_bits))?;
        let scaled = &magnitude / &scale;
        let rounded = round_magnitude(&scaled, negative, rm);
        // Rounding up can push a subnormal onto the smallest NORMAL value.
        if rounded >= hidden {
            return Some(FpFields {
                sign: negative,
                exponent: u64::try_from(emin + bias).ok()?,
                significand: 0,
            });
        }
        return Some(FpFields {
            sign: negative,
            exponent: 0,
            significand: u64::try_from(rounded).ok()?,
        });
    }

    let scale = pow2(exponent - i64::from(fraction_bits))?;
    let scaled = &magnitude / &scale;
    let mut rounded = round_magnitude(&scaled, negative, rm);
    let mut exponent = exponent;

    // A significand that rounds up to 2^sb carries into the exponent. The carry
    // is checked BEFORE the overflow test below, because it is what pushes a
    // value just under `2^(emax+1)` over the top.
    if rounded >= (BigInt::one() << sb) {
        rounded >>= 1u32;
        exponent += 1;
    }

    if exponent > emax {
        return Some(overflow(negative, rm, sb, max_exponent_field));
    }

    // The significand must now be normalized — in `[2^(sb-1), 2^sb)`. No input
    // can violate this, so no test can trigger it; it is here because the cost
    // of being wrong is a well-formed float holding a DIFFERENT number, which
    // the gate would happily confirm. A refusal is the recoverable failure.
    if rounded < hidden || rounded >= (BigInt::one() << sb) {
        return None;
    }

    Some(FpFields {
        sign: negative,
        exponent: u64::try_from(exponent + bias).ok()?,
        significand: u64::try_from(rounded - hidden).ok()?,
    })
}

/// Round `sqrt(value)` into the format `(eb, sb)` under `rm`, for `value > 0`.
///
/// A square root is generally irrational, so it cannot be handed to
/// [`round_rational`]. Approximating it first would be wrong at the boundaries:
/// `sqrt` CAN land exactly halfway between two floats — `sqrt((2^24+1)^2 *
/// 2^-48)` is one — and an approximation cannot tell that tie from the values
/// either side of it, which is exactly where the modes disagree.
///
/// So the rounding decision is made in integers. With `q = n/d`, the scaled
/// root is `sqrt(n*d*2^j) / d`, whose floor is `isqrt(n*d*2^j) / d`; comparing
/// it against the midpoint `m + 1/2` is the exact integer test
/// `4*n*d*2^j  vs  ((2m+1)*d)^2`.
#[must_use]
pub fn sqrt_rational(value: &BigRational, eb: u32, sb: u32, rm: RoundingMode) -> Option<FpFields> {
    if !(2..=32).contains(&eb) || !(2..=64).contains(&sb) || !value.is_positive() {
        return None;
    }
    let bias = (1i64 << (eb - 1)) - 1;
    let emin = 1 - bias;
    let fraction_bits = i64::from(sb - 1);

    // `floor(log2(sqrt(q)))` is `floor(floor(log2 q) / 2)`: if `2^L <= q <
    // 2^(L+1)` then `2^(2e) <= q < 2^(2e+2)` for `e = floor(L/2)`, whichever
    // parity `L` has.
    let log2_q = floor_log2(value)?;
    let mut exponent = log2_q.div_euclid(2);
    // A subnormal result is scaled against a FIXED exponent, as in
    // `round_rational`.
    if exponent < emin {
        exponent = emin;
    }

    // Scale so the rounded significand lands in `[2^(sb-1), 2^sb)`:
    // `m ~ sqrt(q) * 2^shift`. Scaling INSIDE the root keeps one integer
    // radicand whichever sign the shift has: `sqrt(q)*2^s = sqrt(q*2^(2s))`,
    // and `sqrt(n/d) = sqrt(n*d)/d`.
    let shift = fraction_bits - exponent;
    let scaled = value * pow2(shift.checked_mul(2)?)?;
    let denom = scaled.denom();
    let radicand = scaled.numer() * denom;
    let m = radicand.sqrt() / denom;

    // Exact position relative to the midpoint `m + 1/2`:
    //   sqrt(n*d)/d  vs  m + 1/2   <=>   4*n*d  vs  ((2m+1)*d)^2
    let midpoint = (BigInt::from(2u8) * &m + BigInt::one()) * denom;
    let ordering = (BigInt::from(4u8) * &radicand).cmp(&(&midpoint * &midpoint));
    let exact_root = {
        let floor_scaled = &m * denom;
        &floor_scaled * &floor_scaled == radicand
    };

    let mut rounded = match rm {
        RoundingMode::TowardZero | RoundingMode::TowardNegative => m,
        RoundingMode::TowardPositive => {
            if exact_root {
                m
            } else {
                m + 1u8
            }
        }
        RoundingMode::NearestTiesToAway => match ordering {
            core::cmp::Ordering::Less => m,
            _ => m + 1u8,
        },
        RoundingMode::NearestTiesToEven => match ordering {
            core::cmp::Ordering::Less => m,
            core::cmp::Ordering::Greater => m + 1u8,
            core::cmp::Ordering::Equal => {
                if m.is_even() {
                    m
                } else {
                    m + 1u8
                }
            }
        },
    };

    // A carry out of the significand raises the exponent, exactly as in
    // `round_rational`.
    let hidden = BigInt::one() << (sb - 1);
    if rounded >= (BigInt::one() << sb) {
        rounded >>= 1u32;
        exponent += 1;
    }
    // A square root cannot overflow a format it is taken within, so the only
    // boundary left is the subnormal one.
    if rounded < hidden {
        return Some(FpFields {
            sign: false,
            exponent: 0,
            significand: u64::try_from(rounded).ok()?,
        });
    }
    Some(FpFields {
        sign: false,
        exponent: u64::try_from(exponent + bias).ok()?,
        significand: u64::try_from(rounded - hidden).ok()?,
    })
}

/// What overflow produces: infinity, or the largest finite value when the mode
/// rounds toward it.
fn overflow(negative: bool, rm: RoundingMode, sb: u32, max_field: u64) -> FpFields {
    let to_largest_finite = match rm {
        RoundingMode::TowardZero => true,
        RoundingMode::TowardPositive => negative,
        RoundingMode::TowardNegative => !negative,
        RoundingMode::NearestTiesToEven | RoundingMode::NearestTiesToAway => false,
    };
    if to_largest_finite {
        FpFields {
            sign: negative,
            exponent: max_field - 1,
            significand: (1u64 << (sb - 1)) - 1,
        }
    } else {
        FpFields {
            sign: negative,
            exponent: max_field,
            significand: 0,
        }
    }
}

#[cfg(test)]
#[path = "ieee_tests.rs"]
mod tests;
