// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FpModelValue conversions, comparisons, construction, and formatting.
//!
//! Contains: to_ieee_bv, to_f64, to_rational, fp_lt/fp_leq/fp_gt/fp_geq,
//! from_f64_with_format, to_smtlib.
//!
//! Extracted from model_value.rs as part of #5970 code-health splits.

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::{model_value::FpModelValue, RoundingMode};

impl FpModelValue {
    /// Convert to IEEE 754 bitvector value as BigInt.
    ///
    /// Layout (MSB to LSB): sign(1) | exponent(eb) | stored_significand(sb-1)
    /// Returns the total width (eb + sb) alongside the value.
    ///
    /// For NaN, returns a quiet NaN encoding (no exact payload guarantee).
    pub fn to_ieee_bv(&self) -> (BigInt, u32) {
        let eb = self.eb();
        let sb = self.sb();
        let width = eb + sb;
        let stored_bits = sb - 1;
        let (sign_bit, exp_val, sig_val): (u64, u64, u64) = match self {
            Self::PosZero { .. } => (0, 0, 0),
            Self::NegZero { .. } => (1, 0, 0),
            Self::PosInf { .. } => (0, (1u64 << eb) - 1, 0),
            Self::NegInf { .. } => (1, (1u64 << eb) - 1, 0),
            Self::NaN { .. } => {
                // Quiet NaN: exponent all-ones, significand MSB set
                (0, (1u64 << eb) - 1, 1u64 << (stored_bits - 1))
            }
            Self::Fp {
                sign,
                exponent,
                significand,
                ..
            } => (if *sign { 1 } else { 0 }, *exponent, *significand),
        };
        let val = (BigInt::from(sign_bit) << (eb + stored_bits) as usize)
            | (BigInt::from(exp_val) << stored_bits as usize)
            | BigInt::from(sig_val);
        (val, width)
    }

    /// Convert to `f64` for ground evaluation. Returns `None` if the format
    /// cannot be faithfully represented (eb > 11 or sb > 53).
    pub fn to_f64(&self) -> Option<f64> {
        match self {
            Self::PosZero { .. } => Some(0.0),
            Self::NegZero { .. } => Some(-0.0),
            Self::PosInf { .. } => Some(f64::INFINITY),
            Self::NegInf { .. } => Some(f64::NEG_INFINITY),
            Self::NaN { .. } => Some(f64::NAN),
            Self::Fp {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => {
                // Only support Float16 (5,11), Float32 (8,24), Float64 (11,53)
                if *eb > 11 || *sb > 53 {
                    return None;
                }
                let bias = (1u64 << (*eb - 1)) - 1;
                let stored_bits = *sb - 1; // significand bits excluding hidden bit

                if *exponent == 0 {
                    // Subnormal: value = (-1)^sign * 2^(1-bias) * (0.significand)
                    let frac = *significand as f64 / (1u64 << stored_bits) as f64;
                    let val = f64::exp2(1.0 - bias as f64) * frac;
                    Some(if *sign { -val } else { val })
                } else {
                    // Normal: value = (-1)^sign * 2^(exponent-bias) * (1.significand)
                    let frac = 1.0 + (*significand as f64 / (1u64 << stored_bits) as f64);
                    let val = f64::exp2(*exponent as f64 - bias as f64) * frac;
                    Some(if *sign { -val } else { val })
                }
            }
        }
    }

    /// Convert to exact `BigRational` for fp.to_real semantics.
    ///
    /// Returns `None` for NaN and infinity (unspecified in SMT-LIB).
    /// Returns the exact rational value for finite numbers (including
    /// subnormals and zeros). Unlike `to_f64()`, this has no precision
    /// limitations — it works for all FP formats.
    pub fn to_rational(&self) -> Option<BigRational> {
        use num_bigint::BigInt;
        use num_rational::BigRational;

        match self {
            Self::PosZero { .. } | Self::NegZero { .. } => {
                Some(BigRational::from_integer(BigInt::from(0)))
            }
            Self::PosInf { .. } | Self::NegInf { .. } | Self::NaN { .. } => None,
            Self::Fp {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => {
                let bias = (1u64 << (*eb - 1)) - 1;
                let stored_bits = *sb - 1; // significand bits excluding hidden bit

                // Build the exact rational value.
                // Significand as integer (including implicit leading 1 for normals)
                let sig_int = if *exponent == 0 {
                    // Subnormal: no implicit leading 1
                    // value = (-1)^sign * 2^(1-bias) * sig / 2^stored_bits
                    //       = (-1)^sign * sig / 2^(stored_bits + bias - 1)
                    BigInt::from(*significand)
                } else {
                    // Normal: implicit leading 1
                    // value = (-1)^sign * 2^(exp-bias) * (1 + sig / 2^stored_bits)
                    //       = (-1)^sign * (2^stored_bits + sig) / 2^stored_bits * 2^(exp-bias)
                    //       = (-1)^sign * (2^stored_bits + sig) * 2^(exp-bias) / 2^stored_bits
                    (BigInt::from(1u64) << stored_bits) + BigInt::from(*significand)
                };

                if sig_int == BigInt::from(0) {
                    return Some(BigRational::from_integer(BigInt::from(0)));
                }

                // Compute the exponent shift.
                // For subnormals: effective exponent = 1 - bias - stored_bits
                // For normals: effective exponent = exponent - bias - stored_bits
                let exp_shift: i64 = if *exponent == 0 {
                    1i64 - bias as i64 - i64::from(stored_bits)
                } else {
                    *exponent as i64 - bias as i64 - i64::from(stored_bits)
                };

                // result = sig_int * 2^exp_shift
                let result = if exp_shift >= 0 {
                    let numerator = sig_int << (exp_shift as u64);
                    BigRational::from_integer(numerator)
                } else {
                    let denominator = BigInt::from(1u64) << ((-exp_shift) as u64);
                    BigRational::new(sig_int, denominator)
                };

                Some(if *sign { -result } else { result })
            }
        }
    }

    /// IEEE 754 less-than. Returns `None` if f64 conversion fails.
    /// NaN comparisons return `false` per IEEE 754 (#6020).
    pub fn fp_lt(&self, other: &Self) -> Option<bool> {
        if self.is_nan() || other.is_nan() {
            return Some(false);
        }
        let a = self.to_f64()?;
        let b = other.to_f64()?;
        Some(a < b)
    }

    /// IEEE 754 less-than-or-equal. Returns `None` if f64 conversion fails.
    /// NaN comparisons return `false` per IEEE 754 (#6020).
    pub fn fp_leq(&self, other: &Self) -> Option<bool> {
        if self.is_nan() || other.is_nan() {
            return Some(false);
        }
        let a = self.to_f64()?;
        let b = other.to_f64()?;
        Some(a <= b)
    }

    /// IEEE 754 greater-than. Returns `None` if f64 conversion fails.
    /// NaN comparisons return `false` per IEEE 754 (#6020).
    pub fn fp_gt(&self, other: &Self) -> Option<bool> {
        if self.is_nan() || other.is_nan() {
            return Some(false);
        }
        let a = self.to_f64()?;
        let b = other.to_f64()?;
        Some(a > b)
    }

    /// IEEE 754 greater-than-or-equal. Returns `None` if f64 conversion fails.
    /// NaN comparisons return `false` per IEEE 754 (#6020).
    pub fn fp_geq(&self, other: &Self) -> Option<bool> {
        if self.is_nan() || other.is_nan() {
            return Some(false);
        }
        let a = self.to_f64()?;
        let b = other.to_f64()?;
        Some(a >= b)
    }

    /// Construct an `FpModelValue` from an f64 value for a given FP format.
    ///
    /// Converts the f64 to the nearest representable value in the target format
    /// (eb, sb). Returns `None` if the format is too wide for f64 precision
    /// (eb > 11 or sb > 53). For Float32 (8, 24), rounds through f32 first.
    pub fn from_f64_with_format(value: f64, eb: u32, sb: u32) -> Option<Self> {
        if eb > 11 || sb > 53 {
            return None;
        }
        if value.is_nan() {
            return Some(Self::NaN { eb, sb });
        }
        if value.is_infinite() {
            return if value > 0.0 {
                Some(Self::PosInf { eb, sb })
            } else {
                Some(Self::NegInf { eb, sb })
            };
        }
        if value == 0.0 {
            return if value.is_sign_negative() {
                Some(Self::NegZero { eb, sb })
            } else {
                Some(Self::PosZero { eb, sb })
            };
        }

        let sign = value < 0.0;
        let abs_val = value.abs();
        let bias = (1u64 << (eb - 1)) - 1;
        let stored_bits = sb - 1;

        // For Float32, round through f32 to get the nearest representable value
        let abs_val = if eb == 8 && sb == 24 {
            f64::from(abs_val as f32)
        } else {
            abs_val
        };

        // Handle special case: value rounds to zero in target format
        if abs_val == 0.0 {
            return Some(if sign {
                Self::NegZero { eb, sb }
            } else {
                Self::PosZero { eb, sb }
            });
        }

        // Compute biased exponent: floor(log2(abs_val))
        let log2 = abs_val.log2().floor() as i64;
        let biased = log2 + bias as i64;

        if biased <= 0 {
            // Subnormal: exponent = 0, significand encodes the value directly
            let scale = f64::exp2(1.0 - bias as f64 - f64::from(stored_bits));
            let sig = (abs_val / scale).round() as u64;
            if sig == 0 {
                return Some(if sign {
                    Self::NegZero { eb, sb }
                } else {
                    Self::PosZero { eb, sb }
                });
            }
            Some(Self::Fp {
                sign,
                exponent: 0,
                significand: sig,
                eb,
                sb,
            })
        } else if biased >= ((1u64 << eb) - 1) as i64 {
            // Overflow to infinity
            Some(if sign {
                Self::NegInf { eb, sb }
            } else {
                Self::PosInf { eb, sb }
            })
        } else {
            // Normal: significand = (abs_val / 2^(exp-bias) - 1) * 2^stored_bits
            let exp_val = f64::exp2(log2 as f64);
            let frac = abs_val / exp_val - 1.0;
            let sig = (frac * f64::exp2(f64::from(stored_bits))).round() as u64;
            // Clamp significand to valid range
            let max_sig = (1u64 << stored_bits) - 1;
            let sig = sig.min(max_sig);
            Some(Self::Fp {
                sign,
                exponent: biased as u64,
                significand: sig,
                eb,
                sb,
            })
        }
    }

    /// Construct an `FpModelValue` by exactly rounding a rational value into
    /// the target FP format.
    ///
    /// Unlike `from_f64_with_format`, this does not lose precision on formats
    /// wider than Float64. It currently supports formats that fit the existing
    /// `FpModelValue` representation (`eb < 64`, `2 <= sb <= 64`).
    pub fn from_rational_with_format(
        value: &BigRational,
        eb: u32,
        sb: u32,
        rm: RoundingMode,
    ) -> Option<Self> {
        let zero = BigInt::from(0);
        let one = BigInt::from(1);
        if eb == 0 || eb >= 64 || !(2..=64).contains(&sb) {
            return None;
        }
        if value.numer() == &zero {
            return Some(Self::PosZero { eb, sb });
        }

        let negative = value.numer() < &zero;
        let abs_value = if negative {
            -value.clone()
        } else {
            value.clone()
        };
        let bias = (1u64 << (eb - 1)) - 1;
        let max_exp_field = (1u64 << eb) - 1;
        let hidden_bit = &one << (sb - 1) as usize;
        let full_precision = &one << sb as usize;
        let exponent = floor_log2_positive(&abs_value);
        let min_normal_exp = 1i64 - bias as i64;

        if exponent >= min_normal_exp {
            let shift = i64::from(sb - 1) - exponent;
            let scaled = scale_rational_by_pow2(&abs_value, shift);
            let mut significand = round_positive_rational_to_integer(&scaled, rm, negative);
            let mut rounded_exponent = exponent;

            if significand == full_precision {
                significand = hidden_bit.clone();
                rounded_exponent += 1;
            }

            let exponent_field = rounded_exponent + bias as i64;
            if exponent_field >= max_exp_field as i64 {
                return Some(if negative {
                    Self::NegInf { eb, sb }
                } else {
                    Self::PosInf { eb, sb }
                });
            }

            let stored_significand = u64::try_from(significand - &hidden_bit).ok()?;
            return Some(Self::Fp {
                sign: negative,
                exponent: exponent_field as u64,
                significand: stored_significand,
                eb,
                sb,
            });
        }

        let shift = bias as i64 + i64::from(sb) - 2;
        let scaled = scale_rational_by_pow2(&abs_value, shift);
        let significand = round_positive_rational_to_integer(&scaled, rm, negative);

        if significand == zero {
            return Some(if negative {
                Self::NegZero { eb, sb }
            } else {
                Self::PosZero { eb, sb }
            });
        }

        if significand >= hidden_bit {
            return Some(Self::Fp {
                sign: negative,
                exponent: 1,
                significand: 0,
                eb,
                sb,
            });
        }

        Some(Self::Fp {
            sign: negative,
            exponent: 0,
            significand: u64::try_from(significand).ok()?,
            eb,
            sb,
        })
    }

    /// Format as SMT-LIB FP literal.
    pub fn to_smtlib(&self) -> String {
        match self {
            Self::PosZero { eb, sb } => format!("(_ +zero {eb} {sb})"),
            Self::NegZero { eb, sb } => format!("(_ -zero {eb} {sb})"),
            Self::PosInf { eb, sb } => format!("(_ +oo {eb} {sb})"),
            Self::NegInf { eb, sb } => format!("(_ -oo {eb} {sb})"),
            Self::NaN { eb, sb } => format!("(_ NaN {eb} {sb})"),
            Self::Fp {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => {
                let sign_bv = if *sign { "#b1" } else { "#b0" };
                // Exponent: eb bits wide
                let exp_str = format!("#b{:0width$b}", exponent, width = *eb as usize);
                // Stored significand: sb-1 bits wide (excludes hidden bit)
                let sig_str = format!("#b{:0width$b}", significand, width = (*sb - 1) as usize);
                format!("(fp {sign_bv} {exp_str} {sig_str})")
            }
        }
    }
}

fn floor_log2_positive(value: &BigRational) -> i64 {
    debug_assert!(value.numer() > &BigInt::from(0));
    let numer = value.numer().clone();
    let denom = value.denom().clone();
    let mut exponent = numer.bits() as i64 - denom.bits() as i64;

    let below_bound = if exponent >= 0 {
        numer < (denom << exponent as usize)
    } else {
        (numer << (-exponent) as usize) < denom
    };
    if below_bound {
        exponent -= 1;
    }
    exponent
}

fn scale_rational_by_pow2(value: &BigRational, shift: i64) -> BigRational {
    if shift >= 0 {
        BigRational::new(
            value.numer().clone() << shift as usize,
            value.denom().clone(),
        )
    } else {
        BigRational::new(
            value.numer().clone(),
            value.denom().clone() << (-shift) as usize,
        )
    }
}

fn round_positive_rational_to_integer(
    value: &BigRational,
    rm: RoundingMode,
    negative: bool,
) -> BigInt {
    let zero = BigInt::from(0);
    let one = BigInt::from(1);
    debug_assert!(value.numer() >= &zero);
    let quotient = value.numer() / value.denom();
    let remainder = value.numer() % value.denom();
    if remainder == zero {
        return quotient;
    }

    match rm {
        RoundingMode::RNE => {
            let twice_remainder = &remainder << 1usize;
            match twice_remainder.cmp(value.denom()) {
                std::cmp::Ordering::Less => quotient,
                std::cmp::Ordering::Greater => quotient + 1,
                std::cmp::Ordering::Equal => {
                    if (&quotient & &one) == zero {
                        quotient
                    } else {
                        quotient + 1
                    }
                }
            }
        }
        RoundingMode::RNA => {
            if (&remainder << 1usize) >= *value.denom() {
                quotient + 1
            } else {
                quotient
            }
        }
        RoundingMode::RTZ => quotient,
        RoundingMode::RTP => {
            if negative {
                quotient
            } else {
                quotient + 1
            }
        }
        RoundingMode::RTN => {
            if negative {
                quotient + 1
            } else {
                quotient
            }
        }
    }
}
