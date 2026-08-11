// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point proof annotations.

use serde::{Deserialize, Serialize};

/// IEEE 754 floating-point operation for FP→BV proof annotation.
///
/// Each variant corresponds to an SMT-LIB floating-point operation that the
/// FP solver lowers to bitvector circuits. Carrying the operation type in the
/// proof allows the checker and printer to emit `fp_to_bv` instead of the
/// unverified `trust` fallback.
///
/// Reference: SMT-LIB FloatingPoint theory definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FpOp {
    /// Floating-point addition (`fp.add`)
    Add,
    /// Floating-point subtraction (`fp.sub`)
    Sub,
    /// Floating-point multiplication (`fp.mul`)
    Mul,
    /// Floating-point division (`fp.div`)
    Div,
    /// Floating-point square root (`fp.sqrt`)
    Sqrt,
    /// Floating-point negation (`fp.neg`)
    Neg,
    /// Floating-point absolute value (`fp.abs`)
    Abs,
    /// Fused multiply-add (`fp.fma`)
    Fma,
    /// IEEE 754 equality (`fp.eq`)
    Eq,
    /// Floating-point less-than (`fp.lt`)
    Lt,
    /// Floating-point less-or-equal (`fp.leq`)
    Le,
    /// Floating-point greater-than (`fp.gt`)
    Gt,
    /// Floating-point greater-or-equal (`fp.geq`)
    Ge,
    /// Convert to real (`fp.to_real`)
    ToReal,
    /// Convert from real (to_fp from Real)
    FromReal,
    /// Convert to signed bitvector (`fp.to_sbv`)
    ToSbv,
    /// Convert to unsigned bitvector (`fp.to_ubv`)
    ToUbv,
    /// Convert from signed bitvector (to_fp from signed BV)
    FromSbv,
    /// Convert from unsigned bitvector (`to_fp_unsigned`)
    FromUbv,
    /// Round to integral (`fp.roundToIntegral`)
    RoundToIntegral,
    /// Floating-point minimum (`fp.min`)
    Min,
    /// Floating-point maximum (`fp.max`)
    Max,
    /// Floating-point remainder (`fp.rem`)
    Rem,
    /// Classification: isNaN (`fp.isNaN`)
    IsNaN,
    /// Classification: isInfinite (`fp.isInfinite`)
    IsInfinite,
    /// Classification: isZero (`fp.isZero`)
    IsZero,
    /// Classification: isNormal (`fp.isNormal`)
    IsNormal,
    /// Classification: isSubnormal (`fp.isSubnormal`)
    IsSubnormal,
    /// Classification: isPositive (`fp.isPositive`)
    IsPositive,
    /// Classification: isNegative (`fp.isNegative`)
    IsNegative,
    /// SMT-LIB structural equality on FP sort (`=` on FloatingPoint)
    StructuralEq,
    /// Convert to IEEE BV representation (`fp.to_ieee_bv`)
    ToIeeeBv,
    /// Convert from FP to FP (to_fp from FloatingPoint)
    FromFp,
}

impl std::fmt::Display for FpOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Self::Add => "fp.add",
            Self::Sub => "fp.sub",
            Self::Mul => "fp.mul",
            Self::Div => "fp.div",
            Self::Sqrt => "fp.sqrt",
            Self::Neg => "fp.neg",
            Self::Abs => "fp.abs",
            Self::Fma => "fp.fma",
            Self::Eq => "fp.eq",
            Self::Lt => "fp.lt",
            Self::Le => "fp.leq",
            Self::Gt => "fp.gt",
            Self::Ge => "fp.geq",
            Self::ToReal => "fp.to_real",
            Self::FromReal => "to_fp_real",
            Self::ToSbv => "fp.to_sbv",
            Self::ToUbv => "fp.to_ubv",
            Self::FromSbv => "to_fp_sbv",
            Self::FromUbv => "to_fp_unsigned",
            Self::RoundToIntegral => "fp.roundToIntegral",
            Self::Min => "fp.min",
            Self::Max => "fp.max",
            Self::Rem => "fp.rem",
            Self::IsNaN => "fp.isNaN",
            Self::IsInfinite => "fp.isInfinite",
            Self::IsZero => "fp.isZero",
            Self::IsNormal => "fp.isNormal",
            Self::IsSubnormal => "fp.isSubnormal",
            Self::IsPositive => "fp.isPositive",
            Self::IsNegative => "fp.isNegative",
            Self::StructuralEq => "fp_structural_eq",
            Self::ToIeeeBv => "fp.to_ieee_bv",
            Self::FromFp => "to_fp_fp",
        };
        f.write_str(name)
    }
}
