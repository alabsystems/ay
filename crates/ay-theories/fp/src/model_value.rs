// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Concrete IEEE 754 floating-point model values.
//!
//! `FpModelValue` represents a concrete FP value reconstructed from a SAT model.
//! It supports IEEE 754 comparison semantics, SMT-LIB formatting, and
//! conversion to native f64 and exact BigRational.

/// A concrete IEEE 754 floating-point value reconstructed from a SAT model.
#[derive(Debug, Clone)]
pub enum FpModelValue {
    /// Positive zero
    PosZero {
        /// Exponent bit width
        eb: u32,
        /// Significand bit width (including hidden bit)
        sb: u32,
    },
    /// Negative zero
    NegZero {
        /// Exponent bit width
        eb: u32,
        /// Significand bit width (including hidden bit)
        sb: u32,
    },
    /// Positive infinity
    PosInf {
        /// Exponent bit width
        eb: u32,
        /// Significand bit width (including hidden bit)
        sb: u32,
    },
    /// Negative infinity
    NegInf {
        /// Exponent bit width
        eb: u32,
        /// Significand bit width (including hidden bit)
        sb: u32,
    },
    /// NaN (quiet NaN with canonical payload)
    NaN {
        /// Exponent bit width
        eb: u32,
        /// Significand bit width (including hidden bit)
        sb: u32,
    },
    /// A normal or subnormal finite value represented as the IEEE 754 (fp ...) triple.
    /// sign=true means negative.
    Fp {
        /// True if negative
        sign: bool,
        /// Biased exponent (raw bit pattern)
        exponent: u64,
        /// Stored significand (without hidden bit)
        significand: u64,
        /// Exponent bit width
        eb: u32,
        /// Significand bit width (including hidden bit)
        sb: u32,
    },
}

impl FpModelValue {
    /// Returns the exponent bit width.
    pub fn eb(&self) -> u32 {
        match self {
            Self::PosZero { eb, .. }
            | Self::NegZero { eb, .. }
            | Self::PosInf { eb, .. }
            | Self::NegInf { eb, .. }
            | Self::NaN { eb, .. }
            | Self::Fp { eb, .. } => *eb,
        }
    }

    /// Returns the significand bit width (including hidden bit).
    pub fn sb(&self) -> u32 {
        match self {
            Self::PosZero { sb, .. }
            | Self::NegZero { sb, .. }
            | Self::PosInf { sb, .. }
            | Self::NegInf { sb, .. }
            | Self::NaN { sb, .. }
            | Self::Fp { sb, .. } => *sb,
        }
    }

    /// True if this value is NaN.
    pub fn is_nan(&self) -> bool {
        matches!(self, Self::NaN { .. })
    }

    /// True if this value is positive or negative infinity.
    pub fn is_infinite(&self) -> bool {
        matches!(self, Self::PosInf { .. } | Self::NegInf { .. })
    }

    /// True if this value is positive or negative zero.
    pub fn is_zero(&self) -> bool {
        matches!(self, Self::PosZero { .. } | Self::NegZero { .. })
    }

    /// True if this value is positive (sign bit = 0).
    /// +0 is positive, -0 is not. NaN is not positive.
    pub fn is_positive(&self) -> bool {
        match self {
            Self::PosZero { .. } | Self::PosInf { .. } => true,
            Self::NegZero { .. } | Self::NegInf { .. } | Self::NaN { .. } => false,
            Self::Fp { sign, .. } => !sign,
        }
    }

    /// True if this value is negative (sign bit = 1).
    /// -0 is negative, +0 is not. NaN is not negative.
    pub fn is_negative(&self) -> bool {
        match self {
            Self::NegZero { .. } | Self::NegInf { .. } => true,
            Self::PosZero { .. } | Self::PosInf { .. } | Self::NaN { .. } => false,
            Self::Fp { sign, .. } => *sign,
        }
    }

    /// True if this value is a normal (non-zero, non-subnormal, non-special) number.
    pub fn is_normal(&self) -> bool {
        match self {
            Self::Fp { exponent, eb, .. } => {
                let max_exp = (1u64 << eb) - 1;
                *exponent != 0 && *exponent != max_exp
            }
            _ => false,
        }
    }

    /// True if this value is subnormal (biased exponent = 0, significand != 0).
    pub fn is_subnormal(&self) -> bool {
        match self {
            Self::Fp {
                exponent,
                significand,
                ..
            } => *exponent == 0 && *significand != 0,
            _ => false,
        }
    }

    /// Negate this value: flip the sign.
    pub fn negate(&self) -> Self {
        match self {
            Self::PosZero { eb, sb } => Self::NegZero { eb: *eb, sb: *sb },
            Self::NegZero { eb, sb } => Self::PosZero { eb: *eb, sb: *sb },
            Self::PosInf { eb, sb } => Self::NegInf { eb: *eb, sb: *sb },
            Self::NegInf { eb, sb } => Self::PosInf { eb: *eb, sb: *sb },
            Self::NaN { eb, sb } => Self::NaN { eb: *eb, sb: *sb },
            Self::Fp {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => Self::Fp {
                sign: !sign,
                exponent: *exponent,
                significand: *significand,
                eb: *eb,
                sb: *sb,
            },
        }
    }

    /// Absolute value: clear the sign bit.
    pub fn abs(&self) -> Self {
        match self {
            Self::NegZero { eb, sb } => Self::PosZero { eb: *eb, sb: *sb },
            Self::NegInf { eb, sb } => Self::PosInf { eb: *eb, sb: *sb },
            Self::NaN { eb, sb } => Self::NaN { eb: *eb, sb: *sb },
            Self::Fp {
                exponent,
                significand,
                eb,
                sb,
                ..
            } => Self::Fp {
                sign: false,
                exponent: *exponent,
                significand: *significand,
                eb: *eb,
                sb: *sb,
            },
            other => other.clone(),
        }
    }

    /// IEEE 754 equality: NaN != NaN, +0 == -0.
    pub fn fp_eq(&self, other: &Self) -> bool {
        if self.is_nan() || other.is_nan() {
            return false;
        }
        if self.is_zero() && other.is_zero() {
            return true;
        }
        // For normal/subnormal: must match sign, exponent, significand
        match (self, other) {
            (
                Self::Fp {
                    sign: s1,
                    exponent: e1,
                    significand: g1,
                    ..
                },
                Self::Fp {
                    sign: s2,
                    exponent: e2,
                    significand: g2,
                    ..
                },
            ) => s1 == s2 && e1 == e2 && g1 == g2,
            (Self::PosInf { .. }, Self::PosInf { .. }) => true,
            (Self::NegInf { .. }, Self::NegInf { .. }) => true,
            _ => false,
        }
    }

    /// SMT-LIB structural equality (`=`): NaN == NaN (reflexive), +0 != -0.
    ///
    /// Unlike `fp_eq` (IEEE 754), structural equality is reflexive on NaN and
    /// distinguishes +0 from -0 by bit pattern. This is required for the SMT-LIB
    /// `=` operator, which is always reflexive per the standard.
    pub fn structural_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::NaN { eb: e1, sb: s1 }, Self::NaN { eb: e2, sb: s2 }) => e1 == e2 && s1 == s2,
            (Self::PosZero { eb: e1, sb: s1 }, Self::PosZero { eb: e2, sb: s2 }) => {
                e1 == e2 && s1 == s2
            }
            (Self::NegZero { eb: e1, sb: s1 }, Self::NegZero { eb: e2, sb: s2 }) => {
                e1 == e2 && s1 == s2
            }
            (Self::PosInf { eb: e1, sb: s1 }, Self::PosInf { eb: e2, sb: s2 }) => {
                e1 == e2 && s1 == s2
            }
            (Self::NegInf { eb: e1, sb: s1 }, Self::NegInf { eb: e2, sb: s2 }) => {
                e1 == e2 && s1 == s2
            }
            (
                Self::Fp {
                    sign: s1,
                    exponent: e1,
                    significand: g1,
                    eb: eb1,
                    sb: sb1,
                },
                Self::Fp {
                    sign: s2,
                    exponent: e2,
                    significand: g2,
                    eb: eb2,
                    sb: sb2,
                },
            ) => s1 == s2 && e1 == e2 && g1 == g2 && eb1 == eb2 && sb1 == sb2,
            _ => false,
        }
    }

    // to_ieee_bv, to_f64, to_rational, fp_lt/leq/gt/geq,
    // from_f64_with_format, to_smtlib extracted to model_value_convert.rs
}
