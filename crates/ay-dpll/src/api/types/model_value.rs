// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model value types and extraction methods.

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;

use super::SolverError;

/// Refusal to decode a complete batch of closed, caller-sorted model literals.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("typed model literals are malformed, unsupported, ill-sorted or over budget")]
pub struct TypedModelValueDecodeError;

/// A model value obtained through evaluation or exact data-only decoding.
///
/// This enum represents values from term-based model evaluation, supporting
/// more sorts than the legacy [`Model`](super::Model) struct.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ModelValue {
    /// Exact floating-point fields beyond the native field-based variants.
    /// Immutable shared fields preserve every occupied bit when models clone.
    FloatingPointExact(ay_fp::FpFields),
    /// Boolean value.
    Bool(bool),
    /// Unbounded integer value.
    Int(BigInt),
    /// Rational (real) value.
    Real(BigRational),
    /// Bitvector value with width.
    BitVec {
        /// The numeric value (interpreted modulo 2^width).
        value: BigInt,
        /// The bit width.
        width: u32,
    },
    /// String value.
    String(String),
    /// Uninterpreted sort element (symbolic name).
    Uninterpreted(String),
    /// Array value as SMT-LIB expression string (fallback for unparseable arrays).
    ArraySmtlib(String),
    /// Structured array value: a default element plus point-wise stores.
    ///
    /// Represents `(store (store ... ((as const ...) default) i1 v1) i2 v2)`.
    Array {
        /// The default element value (from `(as const ...)` base).
        default: Box<Self>,
        /// Point-wise stores: `(index, value)` pairs applied on top of the default.
        stores: Vec<(Self, Self)>,
    },
    /// IEEE 754 floating-point value.
    FloatingPoint {
        /// Sign bit: true = negative.
        sign: bool,
        /// Raw biased exponent bits.
        exponent: u64,
        /// Raw stored significand bits (without hidden bit).
        significand: u64,
        /// Exponent bit width.
        eb: u32,
        /// Significand bit width (including hidden bit).
        sb: u32,
    },
    /// IEEE 754 value with a stored significand wider than 64 bits.
    ///
    /// Binary128 uses 112 stored bits. The narrow variant and its extraction
    /// signatures remain available; use [`Self::as_fp_wide`] for lossless
    /// extraction of either representation. Decoders select this variant by
    /// declared width, even when a particular fraction fits `u64`. Derived
    /// equality compares variants and fields, not IEEE numeric equivalence.
    FloatingPointWide {
        /// Sign bit: true = negative.
        sign: bool,
        /// Raw biased exponent bits.
        exponent: u64,
        /// Raw stored significand bits (without hidden bit).
        significand: u128,
        /// Exponent bit width.
        eb: u32,
        /// Significand bit width (including hidden bit).
        sb: u32,
    },
    /// Floating-point special value (+zero, -zero, +oo, -oo, NaN).
    FloatingPointSpecial {
        /// The kind of special value.
        kind: FpSpecialKind,
        /// Exponent bit width.
        eb: u32,
        /// Significand bit width (including hidden bit).
        sb: u32,
    },
    /// Datatype constructor application.
    Datatype {
        /// Constructor name.
        constructor: String,
        /// Constructor arguments (may be empty for nullary constructors).
        args: Vec<Self>,
    },
    /// Sequence value: ordered list of elements.
    Seq(Vec<Self>),
    /// Canonical prime-field residue with its checked field identity.
    FiniteField {
        /// Residue in `0..field.modulus()`.
        value: u32,
        /// Checked prime field.
        field: ay_core::FiniteFieldSort,
    },
    /// Value could not be determined.
    Unknown,
}

/// Special floating-point value kinds.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum FpSpecialKind {
    /// Positive zero.
    PosZero,
    /// Negative zero.
    NegZero,
    /// Positive infinity.
    PosInf,
    /// Negative infinity.
    NegInf,
    /// Not a number.
    NaN,
}

impl ModelValue {
    /// Decode one closed SMT-LIB literal per entry against its supplied sort.
    ///
    /// This is data-only: no solver, declaration context or term store is used,
    /// and success attests neither native-model provenance nor satisfiability.
    /// Caller sorts must contain complete finite datatype metadata; unresolved
    /// carriers, opaque arrays and missing defaults are refused. Every array
    /// default, ordered store (including duplicates), and constructor field is
    /// checked. No width truncation, invented value or partial batch is returned.
    ///
    /// At most 4096 literals share one 8 MiB/131072-conservative-token lexical
    /// envelope (depth 128), and one 1048576-work/16 MiB copy allowance for parser
    /// preflight, metadata and values (typed depth 64). All borrowed text and
    /// sorts are admitted before the first AST is built. These cumulative
    /// charges can refuse inputs below the outer limits; they are conservative
    /// allowances, not measured allocator/RSS or wall-clock latency bounds.
    /// Primitive, sequence and floating-point forms use the existing strict
    /// decoder grammar; arbitrary evaluated SMT expressions are not literals.
    pub fn decode_typed_literals(
        input: &[(&str, &ay_core::Sort)],
    ) -> Result<Vec<Self>, TypedModelValueDecodeError> {
        crate::api::model_parse::decode_typed_literals(input).ok_or(TypedModelValueDecodeError)
    }

    /// Returns true if this is an Unknown value.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Returns the variant name as a static string (for error messages).
    pub fn variant_name(&self) -> &'static str {
        match self {
            Self::FloatingPointExact(_) => "FloatingPointExact",
            Self::Bool(_) => "Bool",
            Self::Int(_) => "Int",
            Self::Real(_) => "Real",
            Self::BitVec { .. } => "BitVec",
            Self::String(_) => "String",
            Self::Uninterpreted(_) => "Uninterpreted",
            Self::ArraySmtlib(_) => "ArraySmtlib",
            Self::Array { .. } => "Array",
            Self::FloatingPoint { .. } => "FloatingPoint",
            Self::FloatingPointWide { .. } => "FloatingPointWide",
            Self::FloatingPointSpecial { .. } => "FloatingPointSpecial",
            Self::Datatype { .. } => "Datatype",
            Self::Seq(_) => "Seq",
            Self::FiniteField { .. } => "FiniteField",
            Self::Unknown => "Unknown",
        }
    }

    /// Fallible extraction as boolean. Returns `Err` with diagnostic if not `Bool`.
    pub fn try_bool(&self) -> Result<bool, SolverError> {
        self.as_bool()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "Bool",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as integer. Returns `Err` with diagnostic if not `Int`.
    pub fn try_int(&self) -> Result<&BigInt, SolverError> {
        self.as_int()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "Int",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as rational. Returns `Err` with diagnostic if not `Real`.
    pub fn try_real(&self) -> Result<&BigRational, SolverError> {
        self.as_real()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "Real",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as bitvector. Returns `Err` with diagnostic if not `BitVec`.
    pub fn try_bv(&self) -> Result<(&BigInt, u32), SolverError> {
        self.as_bv().ok_or_else(|| SolverError::ModelValueMismatch {
            expected: "BitVec",
            actual: self.variant_name().to_string(),
        })
    }

    /// Unwrap as a boolean, panicking if not Bool.
    ///
    /// Prefer [`try_bool`](Self::try_bool) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::Bool`].
    pub fn unwrap_bool(&self) -> bool {
        self.try_bool().expect("expected Bool ModelValue")
    }

    /// Unwrap as an integer, panicking if not Int.
    ///
    /// Prefer [`try_int`](Self::try_int) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::Int`].
    pub fn unwrap_int(&self) -> &BigInt {
        self.try_int().expect("expected Int ModelValue")
    }

    /// Unwrap as a rational, panicking if not Real.
    ///
    /// Prefer [`try_real`](Self::try_real) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::Real`].
    pub fn unwrap_real(&self) -> &BigRational {
        self.try_real().expect("expected Real ModelValue")
    }

    /// Unwrap as a bitvector, panicking if not BitVec.
    ///
    /// Prefer [`try_bv`](Self::try_bv) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::BitVec`].
    pub fn unwrap_bv(&self) -> (&BigInt, u32) {
        self.try_bv().expect("expected BitVec ModelValue")
    }

    /// Try to extract a boolean value. Returns `None` if not `Bool`.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Try to extract an integer value. Returns `None` if not `Int`.
    pub fn as_int(&self) -> Option<&BigInt> {
        match self {
            Self::Int(n) => Some(n),
            _ => None,
        }
    }

    /// Try to extract a rational value. Returns `None` if not `Real`.
    pub fn as_real(&self) -> Option<&BigRational> {
        match self {
            Self::Real(r) => Some(r),
            _ => None,
        }
    }

    /// Try to extract a bitvector value and width. Returns `None` if not `BitVec`.
    pub fn as_bv(&self) -> Option<(&BigInt, u32)> {
        match self {
            Self::BitVec { value, width } => Some((value, *width)),
            _ => None,
        }
    }

    /// Try to extract a string value. Returns `None` if not `String`.
    pub fn as_string(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    /// Try to extract an uninterpreted sort element name. Returns `None` if not `Uninterpreted`.
    pub fn as_uninterpreted(&self) -> Option<&str> {
        match self {
            Self::Uninterpreted(s) => Some(s),
            _ => None,
        }
    }

    /// Try to extract an array value as SMT-LIB string. Returns `None` if not `ArraySmtlib`.
    pub fn as_array_smtlib(&self) -> Option<&str> {
        match self {
            Self::ArraySmtlib(s) => Some(s),
            _ => None,
        }
    }

    /// Try to extract a structured array value. Returns `None` if not `Array`.
    pub fn as_array(&self) -> Option<(&Self, &[(Self, Self)])> {
        match self {
            Self::Array { default, stores } => Some((default, stores)),
            _ => None,
        }
    }

    /// Extract floating-point fields if the stored significand fits in `u64`.
    ///
    /// A wide value is narrowed only when exact. Use [`Self::as_fp_wide`] to
    /// preserve every bit of a binary128 value. Special-value variants are
    /// handled separately by [`Self::as_fp_special`].
    pub fn as_fp(&self) -> Option<(bool, u64, u64, u32, u32)> {
        let (sign, exponent, significand, eb, sb) = self.as_fp_wide()?;
        Some((sign, exponent, u64::try_from(significand).ok()?, eb, sb))
    }

    /// Extract raw floating-point fields without narrowing the significand.
    ///
    /// Accepts field-based variants when both actual fields fit; larger fields
    /// return `None` without truncation. See `as_fp_exact` for arbitrary fields.
    /// This accessor does not validate manually constructed field payloads.
    pub fn as_fp_wide(&self) -> Option<(bool, u64, u128, u32, u32)> {
        match self {
            Self::FloatingPointExact(fields) => Some((
                fields.sign(),
                u64::try_from(fields.exponent()).ok()?,
                u128::try_from(fields.significand()).ok()?,
                fields.exponent_bits(),
                fields.significand_bits(),
            )),
            Self::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => Some((*sign, *exponent, u128::from(*significand), *eb, *sb)),
            Self::FloatingPointWide {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => Some((*sign, *exponent, *significand, *eb, *sb)),
            _ => None,
        }
    }

    /// Read validated exact fields from any field-based FP representation.
    /// Cloning the exact variant shares its immutable integer payloads.
    /// Special-value variants are available separately through `as_fp_special`.
    pub fn as_fp_exact(&self) -> Option<ay_fp::FpFields> {
        if let Self::FloatingPointExact(fields) = self {
            return Some(fields.clone());
        }
        let (sign, exponent, significand, eb, sb) = self.as_fp_wide()?;
        ay_fp::FpFields::new(sign, exponent.into(), significand.into(), eb, sb)
    }

    /// Try to extract a floating-point special value. Returns `None` if not `FloatingPointSpecial`.
    pub fn as_fp_special(&self) -> Option<(&FpSpecialKind, u32, u32)> {
        match self {
            Self::FloatingPointSpecial { kind, eb, sb } => Some((kind, *eb, *sb)),
            _ => None,
        }
    }

    /// Try to extract a datatype value. Returns `None` if not `Datatype`.
    pub fn as_datatype(&self) -> Option<(&str, &[Self])> {
        match self {
            Self::Datatype { constructor, args } => Some((constructor, args)),
            _ => None,
        }
    }

    /// Try to extract a sequence value. Returns `None` if not `Seq`.
    pub fn as_seq(&self) -> Option<&[Self]> {
        match self {
            Self::Seq(elems) => Some(elems),
            _ => None,
        }
    }

    // --- try_* (Result) methods for String, Uninterpreted, ArraySmtlib, FP, Datatype, Array, Seq ---

    /// Fallible extraction as string. Returns `Err` with diagnostic if not `String`.
    pub fn try_string(&self) -> Result<&str, SolverError> {
        self.as_string()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "String",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as uninterpreted sort element. Returns `Err` if not `Uninterpreted`.
    pub fn try_uninterpreted(&self) -> Result<&str, SolverError> {
        self.as_uninterpreted()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "Uninterpreted",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as array SMT-LIB string. Returns `Err` if not `ArraySmtlib`.
    pub fn try_array_smtlib(&self) -> Result<&str, SolverError> {
        self.as_array_smtlib()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "ArraySmtlib",
                actual: self.variant_name().to_string(),
            })
    }

    /// Extract floating-point fields with a checked `u64` significand.
    ///
    /// Returns `(sign, exponent, significand, eb, sb)`. A wide significand that
    /// cannot be narrowed exactly returns `Err`; it is never truncated.
    pub fn try_fp(&self) -> Result<(bool, u64, u64, u32, u32), SolverError> {
        self.as_fp().ok_or_else(|| SolverError::ModelValueMismatch {
            expected: "FloatingPoint",
            actual: self.variant_name().to_string(),
        })
    }

    /// Extract `(sign, exponent, significand, eb, sb)` with no narrowing.
    pub fn try_fp_wide(&self) -> Result<(bool, u64, u128, u32, u32), SolverError> {
        self.as_fp_wide()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "FloatingPoint or FloatingPointWide",
                actual: self.variant_name().to_string(),
            })
    }

    /// Construct exact field-based data after validating its declared widths.
    ///
    /// This is representation admission, not permission to solve the format.
    pub(crate) fn from_fp_fields(
        sign: bool,
        exponent: u64,
        significand: u128,
        eb: u32,
        sb: u32,
    ) -> Option<Self> {
        if !(2..=64).contains(&eb) || !(2..=129).contains(&sb) {
            return None;
        }
        let fraction_width = sb - 1;
        if (eb < 64 && exponent >= 1u64 << eb)
            || (fraction_width < 128 && significand >= 1u128 << fraction_width)
        {
            return None;
        }
        if fraction_width <= 64 {
            Some(Self::FloatingPoint {
                sign,
                exponent,
                significand: u64::try_from(significand).ok()?,
                eb,
                sb,
            })
        } else {
            Some(Self::FloatingPointWide {
                sign,
                exponent,
                significand,
                eb,
                sb,
            })
        }
    }

    pub(crate) fn from_fp_exact_fields(
        sign: bool,
        exponent: BigUint,
        significand: BigUint,
        eb: u32,
        sb: u32,
    ) -> Option<Self> {
        if (2..=64).contains(&eb) && (2..=129).contains(&sb) {
            return Self::from_fp_fields(
                sign,
                u64::try_from(exponent).ok()?,
                u128::try_from(significand).ok()?,
                eb,
                sb,
            );
        }
        Some(Self::FloatingPointExact(ay_fp::FpFields::new(
            sign,
            exponent,
            significand,
            eb,
            sb,
        )?))
    }

    /// Fallible extraction as floating-point special value. Returns `Err` if not `FloatingPointSpecial`.
    ///
    /// Returns `(kind, eb, sb)`.
    pub fn try_fp_special(&self) -> Result<(&FpSpecialKind, u32, u32), SolverError> {
        self.as_fp_special()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "FloatingPointSpecial",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as datatype value. Returns `Err` if not `Datatype`.
    ///
    /// Returns `(constructor_name, args)`.
    pub fn try_datatype(&self) -> Result<(&str, &[Self]), SolverError> {
        self.as_datatype()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "Datatype",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as structured array. Returns `Err` if not `Array`.
    ///
    /// Returns `(default_element, stores)`.
    #[allow(clippy::type_complexity)]
    pub fn try_array(&self) -> Result<(&Self, &[(Self, Self)]), SolverError> {
        self.as_array()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "Array",
                actual: self.variant_name().to_string(),
            })
    }

    /// Fallible extraction as sequence. Returns `Err` if not `Seq`.
    pub fn try_seq(&self) -> Result<&[Self], SolverError> {
        self.as_seq()
            .ok_or_else(|| SolverError::ModelValueMismatch {
                expected: "Seq",
                actual: self.variant_name().to_string(),
            })
    }

    // --- unwrap_* (panicking) methods ---

    /// Unwrap as a string, panicking if not String.
    ///
    /// Prefer [`try_string`](Self::try_string) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::String`].
    pub fn unwrap_string(&self) -> &str {
        self.try_string().expect("expected String ModelValue")
    }

    /// Unwrap as an uninterpreted sort element, panicking if not Uninterpreted.
    ///
    /// Prefer [`try_uninterpreted`](Self::try_uninterpreted) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::Uninterpreted`].
    pub fn unwrap_uninterpreted(&self) -> &str {
        self.try_uninterpreted()
            .expect("expected Uninterpreted ModelValue")
    }

    /// Unwrap as an array SMT-LIB string, panicking if not ArraySmtlib.
    ///
    /// Prefer [`try_array_smtlib`](Self::try_array_smtlib) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::ArraySmtlib`].
    pub fn unwrap_array_smtlib(&self) -> &str {
        self.try_array_smtlib()
            .expect("expected ArraySmtlib ModelValue")
    }

    /// Extract floating-point fields with a checked `u64` significand.
    ///
    /// Prefer [`try_fp`](Self::try_fp) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` has no field-based floating-point value or its stored
    /// significand cannot be narrowed exactly to `u64`.
    pub fn unwrap_fp(&self) -> (bool, u64, u64, u32, u32) {
        self.try_fp().expect("expected FloatingPoint ModelValue")
    }

    /// Unwrap as a floating-point special value, panicking if not FloatingPointSpecial.
    ///
    /// Prefer [`try_fp_special`](Self::try_fp_special) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::FloatingPointSpecial`].
    pub fn unwrap_fp_special(&self) -> (&FpSpecialKind, u32, u32) {
        self.try_fp_special()
            .expect("expected FloatingPointSpecial ModelValue")
    }

    /// Unwrap as a datatype value, panicking if not Datatype.
    ///
    /// Prefer [`try_datatype`](Self::try_datatype) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::Datatype`].
    pub fn unwrap_datatype(&self) -> (&str, &[Self]) {
        self.try_datatype().expect("expected Datatype ModelValue")
    }

    /// Unwrap as a structured array, panicking if not Array.
    ///
    /// Prefer [`try_array`](Self::try_array) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::Array`].
    pub fn unwrap_array(&self) -> (&Self, &[(Self, Self)]) {
        self.try_array().expect("expected Array ModelValue")
    }

    /// Unwrap as a sequence, panicking if not Seq.
    ///
    /// Prefer [`try_seq`](Self::try_seq) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::Seq`].
    pub fn unwrap_seq(&self) -> &[Self] {
        self.try_seq().expect("expected Seq ModelValue")
    }
}

#[cfg(test)]
mod wide_tests;
