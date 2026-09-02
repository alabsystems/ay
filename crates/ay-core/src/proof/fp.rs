// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point proof annotations.

/// IEEE 754 floating-point operation for FP→BV proof annotation.
///
/// Each variant corresponds to an SMT-LIB floating-point operation that the
/// FP solver lowers to bitvector circuits. Carrying the operation type in the
/// proof allows the checker and printer to emit `fp_to_bv` instead of the
/// unverified `trust` fallback.
///
/// Reference: SMT-LIB FloatingPoint theory definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

// Hand-written serde impls (byte-identical to the removed derives — same type
// name, variant names, and indices) so no derive-generated code with
// unverifiable panic paths enters the L0 verification surface. Mirrors the
// `sort_serde` precedent in `crate::sort`.
mod fp_serde {
    use super::FpOp;
    use serde::de::{
        Deserialize, Deserializer, EnumAccess, Error as DeError, Unexpected, VariantAccess, Visitor,
    };
    use serde::ser::{Serialize, Serializer};
    use std::fmt;

    const FP_OP_VARIANTS: &[&str] = &[
        "Add",
        "Sub",
        "Mul",
        "Div",
        "Sqrt",
        "Neg",
        "Abs",
        "Fma",
        "Eq",
        "Lt",
        "Le",
        "Gt",
        "Ge",
        "ToReal",
        "FromReal",
        "ToSbv",
        "ToUbv",
        "FromSbv",
        "FromUbv",
        "RoundToIntegral",
        "Min",
        "Max",
        "Rem",
        "IsNaN",
        "IsInfinite",
        "IsZero",
        "IsNormal",
        "IsSubnormal",
        "IsPositive",
        "IsNegative",
        "StructuralEq",
        "ToIeeeBv",
        "FromFp",
    ];

    impl Serialize for FpOp {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            match self {
                Self::Add => serializer.serialize_unit_variant("FpOp", 0, "Add"),
                Self::Sub => serializer.serialize_unit_variant("FpOp", 1, "Sub"),
                Self::Mul => serializer.serialize_unit_variant("FpOp", 2, "Mul"),
                Self::Div => serializer.serialize_unit_variant("FpOp", 3, "Div"),
                Self::Sqrt => serializer.serialize_unit_variant("FpOp", 4, "Sqrt"),
                Self::Neg => serializer.serialize_unit_variant("FpOp", 5, "Neg"),
                Self::Abs => serializer.serialize_unit_variant("FpOp", 6, "Abs"),
                Self::Fma => serializer.serialize_unit_variant("FpOp", 7, "Fma"),
                Self::Eq => serializer.serialize_unit_variant("FpOp", 8, "Eq"),
                Self::Lt => serializer.serialize_unit_variant("FpOp", 9, "Lt"),
                Self::Le => serializer.serialize_unit_variant("FpOp", 10, "Le"),
                Self::Gt => serializer.serialize_unit_variant("FpOp", 11, "Gt"),
                Self::Ge => serializer.serialize_unit_variant("FpOp", 12, "Ge"),
                Self::ToReal => serializer.serialize_unit_variant("FpOp", 13, "ToReal"),
                Self::FromReal => serializer.serialize_unit_variant("FpOp", 14, "FromReal"),
                Self::ToSbv => serializer.serialize_unit_variant("FpOp", 15, "ToSbv"),
                Self::ToUbv => serializer.serialize_unit_variant("FpOp", 16, "ToUbv"),
                Self::FromSbv => serializer.serialize_unit_variant("FpOp", 17, "FromSbv"),
                Self::FromUbv => serializer.serialize_unit_variant("FpOp", 18, "FromUbv"),
                Self::RoundToIntegral => {
                    serializer.serialize_unit_variant("FpOp", 19, "RoundToIntegral")
                }
                Self::Min => serializer.serialize_unit_variant("FpOp", 20, "Min"),
                Self::Max => serializer.serialize_unit_variant("FpOp", 21, "Max"),
                Self::Rem => serializer.serialize_unit_variant("FpOp", 22, "Rem"),
                Self::IsNaN => serializer.serialize_unit_variant("FpOp", 23, "IsNaN"),
                Self::IsInfinite => serializer.serialize_unit_variant("FpOp", 24, "IsInfinite"),
                Self::IsZero => serializer.serialize_unit_variant("FpOp", 25, "IsZero"),
                Self::IsNormal => serializer.serialize_unit_variant("FpOp", 26, "IsNormal"),
                Self::IsSubnormal => serializer.serialize_unit_variant("FpOp", 27, "IsSubnormal"),
                Self::IsPositive => serializer.serialize_unit_variant("FpOp", 28, "IsPositive"),
                Self::IsNegative => serializer.serialize_unit_variant("FpOp", 29, "IsNegative"),
                Self::StructuralEq => serializer.serialize_unit_variant("FpOp", 30, "StructuralEq"),
                Self::ToIeeeBv => serializer.serialize_unit_variant("FpOp", 31, "ToIeeeBv"),
                Self::FromFp => serializer.serialize_unit_variant("FpOp", 32, "FromFp"),
            }
        }
    }

    struct FpOpVisitor;

    impl<'de> Visitor<'de> for FpOpVisitor {
        type Value = FpOp;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("enum FpOp")
        }

        fn visit_enum<A>(self, data: A) -> Result<FpOp, A::Error>
        where
            A: EnumAccess<'de>,
        {
            let (ident, variant): (FpOpIdent, _) = data.variant()?;
            variant.unit_variant()?;
            Ok(ident.0)
        }
    }

    struct FpOpFieldVisitor;

    impl<'de> Visitor<'de> for FpOpFieldVisitor {
        type Value = FpOp;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("variant identifier")
        }

        fn visit_u64<E>(self, value: u64) -> Result<FpOp, E>
        where
            E: DeError,
        {
            match value {
                0 => Ok(FpOp::Add),
                1 => Ok(FpOp::Sub),
                2 => Ok(FpOp::Mul),
                3 => Ok(FpOp::Div),
                4 => Ok(FpOp::Sqrt),
                5 => Ok(FpOp::Neg),
                6 => Ok(FpOp::Abs),
                7 => Ok(FpOp::Fma),
                8 => Ok(FpOp::Eq),
                9 => Ok(FpOp::Lt),
                10 => Ok(FpOp::Le),
                11 => Ok(FpOp::Gt),
                12 => Ok(FpOp::Ge),
                13 => Ok(FpOp::ToReal),
                14 => Ok(FpOp::FromReal),
                15 => Ok(FpOp::ToSbv),
                16 => Ok(FpOp::ToUbv),
                17 => Ok(FpOp::FromSbv),
                18 => Ok(FpOp::FromUbv),
                19 => Ok(FpOp::RoundToIntegral),
                20 => Ok(FpOp::Min),
                21 => Ok(FpOp::Max),
                22 => Ok(FpOp::Rem),
                23 => Ok(FpOp::IsNaN),
                24 => Ok(FpOp::IsInfinite),
                25 => Ok(FpOp::IsZero),
                26 => Ok(FpOp::IsNormal),
                27 => Ok(FpOp::IsSubnormal),
                28 => Ok(FpOp::IsPositive),
                29 => Ok(FpOp::IsNegative),
                30 => Ok(FpOp::StructuralEq),
                31 => Ok(FpOp::ToIeeeBv),
                32 => Ok(FpOp::FromFp),
                _ => Err(E::invalid_value(
                    Unexpected::Unsigned(value),
                    &"variant index 0 <= i < 33",
                )),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<FpOp, E>
        where
            E: DeError,
        {
            match value {
                "Add" => Ok(FpOp::Add),
                "Sub" => Ok(FpOp::Sub),
                "Mul" => Ok(FpOp::Mul),
                "Div" => Ok(FpOp::Div),
                "Sqrt" => Ok(FpOp::Sqrt),
                "Neg" => Ok(FpOp::Neg),
                "Abs" => Ok(FpOp::Abs),
                "Fma" => Ok(FpOp::Fma),
                "Eq" => Ok(FpOp::Eq),
                "Lt" => Ok(FpOp::Lt),
                "Le" => Ok(FpOp::Le),
                "Gt" => Ok(FpOp::Gt),
                "Ge" => Ok(FpOp::Ge),
                "ToReal" => Ok(FpOp::ToReal),
                "FromReal" => Ok(FpOp::FromReal),
                "ToSbv" => Ok(FpOp::ToSbv),
                "ToUbv" => Ok(FpOp::ToUbv),
                "FromSbv" => Ok(FpOp::FromSbv),
                "FromUbv" => Ok(FpOp::FromUbv),
                "RoundToIntegral" => Ok(FpOp::RoundToIntegral),
                "Min" => Ok(FpOp::Min),
                "Max" => Ok(FpOp::Max),
                "Rem" => Ok(FpOp::Rem),
                "IsNaN" => Ok(FpOp::IsNaN),
                "IsInfinite" => Ok(FpOp::IsInfinite),
                "IsZero" => Ok(FpOp::IsZero),
                "IsNormal" => Ok(FpOp::IsNormal),
                "IsSubnormal" => Ok(FpOp::IsSubnormal),
                "IsPositive" => Ok(FpOp::IsPositive),
                "IsNegative" => Ok(FpOp::IsNegative),
                "StructuralEq" => Ok(FpOp::StructuralEq),
                "ToIeeeBv" => Ok(FpOp::ToIeeeBv),
                "FromFp" => Ok(FpOp::FromFp),
                _ => Err(E::unknown_variant(value, FP_OP_VARIANTS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<FpOp, E>
        where
            E: DeError,
        {
            match core::str::from_utf8(value) {
                Ok(value) => self.visit_str(value),
                Err(_) => Err(E::invalid_value(Unexpected::Bytes(value), &self)),
            }
        }
    }

    // The variant-identifier newtype the derive would have generated as its
    // internal `__Field`, consumed by `visit_enum` through `data.variant()`.
    struct FpOpIdent(FpOp);

    impl<'de> Deserialize<'de> for FpOpIdent {
        fn deserialize<D>(deserializer: D) -> Result<FpOpIdent, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer
                .deserialize_identifier(FpOpFieldVisitor)
                .map(FpOpIdent)
        }
    }

    impl<'de> Deserialize<'de> for FpOp {
        fn deserialize<D>(deserializer: D) -> Result<FpOp, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_enum("FpOp", FP_OP_VARIANTS, FpOpVisitor)
        }
    }
}
