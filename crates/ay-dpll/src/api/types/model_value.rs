// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model value types and extraction methods.

use num_bigint::BigInt;
use num_rational::BigRational;

use super::SolverError;

/// A value from the solver's model, obtained via `get_value`.
///
/// This enum represents values from term-based model evaluation, supporting
/// more sorts than the legacy [`Model`](super::Model) struct.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ModelValue {
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
    /// Returns true if this is an Unknown value.
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Returns the variant name as a static string (for error messages).
    pub fn variant_name(&self) -> &'static str {
        match self {
            Self::Bool(_) => "Bool",
            Self::Int(_) => "Int",
            Self::Real(_) => "Real",
            Self::BitVec { .. } => "BitVec",
            Self::String(_) => "String",
            Self::Uninterpreted(_) => "Uninterpreted",
            Self::ArraySmtlib(_) => "ArraySmtlib",
            Self::Array { .. } => "Array",
            Self::FloatingPoint { .. } => "FloatingPoint",
            Self::FloatingPointSpecial { .. } => "FloatingPointSpecial",
            Self::Datatype { .. } => "Datatype",
            Self::Seq(_) => "Seq",
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

    /// Try to extract a floating-point value. Returns `None` if not `FloatingPoint`.
    pub fn as_fp(&self) -> Option<(bool, u64, u64, u32, u32)> {
        match self {
            Self::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => Some((*sign, *exponent, *significand, *eb, *sb)),
            _ => None,
        }
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

    /// Fallible extraction as floating-point value. Returns `Err` if not `FloatingPoint`.
    ///
    /// Returns `(sign, exponent, significand, eb, sb)`.
    pub fn try_fp(&self) -> Result<(bool, u64, u64, u32, u32), SolverError> {
        self.as_fp().ok_or_else(|| SolverError::ModelValueMismatch {
            expected: "FloatingPoint",
            actual: self.variant_name().to_string(),
        })
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

    /// Unwrap as a floating-point value, panicking if not FloatingPoint.
    ///
    /// Prefer [`try_fp`](Self::try_fp) for fallible extraction.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not [`ModelValue::FloatingPoint`].
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
