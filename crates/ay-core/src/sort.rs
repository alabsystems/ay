// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort system for AY
//!
//! Sorts are the types of terms in SMT-LIB.

use serde::{Deserialize, Serialize};
use std::fmt;

// ============================================================================
// Wrapper types for rich datatype representation
// ============================================================================

/// Bitvector sort with fixed width.
///
/// This wrapper type provides explicit documentation and helper methods.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BitVecSort {
    /// Bitvector width in bits
    pub width: u32,
}

impl BitVecSort {
    /// Create a new bitvector sort with the given width.
    #[must_use]
    pub fn new(width: u32) -> Self {
        Self { width }
    }
}

/// SMT Array sort wrapper.
///
/// This wrapper type provides explicit documentation and helper methods.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ArraySort {
    /// Index (domain) sort
    pub index_sort: Sort,
    /// Element (codomain) sort
    pub element_sort: Sort,
}

impl ArraySort {
    /// Create a new array sort.
    #[must_use]
    pub fn new(index_sort: Sort, element_sort: Sort) -> Self {
        Self {
            index_sort,
            element_sort,
        }
    }
}

/// A field in a datatype constructor (selector).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DatatypeField {
    /// Field (selector) name
    pub name: String,
    /// Field sort
    pub sort: Sort,
}

impl DatatypeField {
    /// Create a new datatype field.
    #[must_use]
    pub fn new(name: impl Into<String>, sort: Sort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }
}

/// A constructor in a datatype definition.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DatatypeConstructor {
    /// Constructor name
    pub name: String,
    /// Constructor fields (selectors)
    pub fields: Vec<DatatypeField>,
}

impl DatatypeConstructor {
    /// Create a new datatype constructor.
    #[must_use]
    pub fn new(name: impl Into<String>, fields: Vec<DatatypeField>) -> Self {
        Self {
            name: name.into(),
            fields,
        }
    }

    /// Create a constructor with no fields (nullary constructor).
    #[must_use]
    pub fn unit(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            fields: Vec::new(),
        }
    }
}

/// Algebraic datatype sort.
///
/// This type holds the full datatype definition including constructors and fields.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DatatypeSort {
    /// Datatype name
    pub name: String,
    /// Constructors (variants)
    pub constructors: Vec<DatatypeConstructor>,
}

impl DatatypeSort {
    /// Create a new datatype sort.
    #[must_use]
    pub fn new(name: impl Into<String>, constructors: Vec<DatatypeConstructor>) -> Self {
        Self {
            name: name.into(),
            constructors,
        }
    }
}

// ============================================================================
// Sort enum
// ============================================================================

/// A sort (type) in the SMT-LIB language.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Sort {
    /// Boolean sort
    Bool,
    /// Integer sort
    Int,
    /// Real sort
    Real,
    /// Bitvector sort with fixed width
    BitVec(BitVecSort),
    /// Array sort with index and element sorts
    Array(Box<ArraySort>),
    /// String sort
    String,
    /// Regular-language sort (SMT-LIB regex)
    RegLan,
    /// Floating-point sort with exponent and significand bits
    FloatingPoint(u32, u32),
    /// Uninterpreted sort
    Uninterpreted(String),
    /// Datatype sort (full constructor/field definition)
    Datatype(DatatypeSort),
    /// Parametric sequence sort: `(Seq T)` where `T` is the element sort.
    Seq(Box<Self>),
    /// Unicode character sort.
    ///
    /// SMT-LIB / Z3 model a character as a code point over the fixed alphabet
    /// `[0, 196607]` (`= 0x2FFFF = Z3's max_char`). AY lowers a `Char` to a
    /// single bounded `Int` code point ([`Self::as_term_sort`] maps `Char → Int`),
    /// carrying the standing invariant `0 <= x <= 196607` as a background axiom
    /// on every `Char`-sorted term (wired at the FFI layer). It differs from a
    /// plain `Int` only in sort-kind reporting (`Z3_CHAR_SORT`) and that bound.
    Char,
    /// Named finite-domain sort of the given cardinality (Z3's
    /// `Z3_mk_finite_domain_sort`): the carrier is `{0, 1, ..., size-1}`.
    ///
    /// Follows the exact `Char` pattern: a finite-domain value lowers to a
    /// single bounded `Int` ([`Self::as_term_sort`] maps `FiniteDomain → Int`),
    /// carrying the standing invariant `0 <= x < size` as a background axiom on
    /// every finite-domain-sorted term (wired at the FFI layer). The `size`
    /// must be `>= 1` (Z3 rejects a 0-cardinality domain; SMT sorts are
    /// non-empty). It differs from a plain `Int` only in sort-kind/name
    /// reporting (`Z3_FINITE_DOMAIN_SORT`) and that bound.
    FiniteDomain(String, u64),
    /// Type variable (Z3's `Z3_mk_type_variable`): a named polymorphic type
    /// parameter, reported as `Z3_TYPE_VAR`.
    ///
    /// AY carries the variable faithfully for introspection round-trips and
    /// MONOMORPHIC use in declaration signatures (where it behaves exactly like
    /// the uninterpreted sort of the same name — [`Self::as_term_sort`] maps
    /// `TypeVar(a) → Uninterpreted(a)`). Polymorphic INSTANTIATION (applying a
    /// decl whose signature mentions the variable to differently-sorted
    /// arguments) is NOT supported and fails with an honest sort error — it is
    /// never silently mis-solved.
    TypeVar(String),
}

// ============================================================================
// Sort helper methods
// ============================================================================

impl Sort {
    /// Create a bitvector sort with the given width.
    pub fn bitvec(width: u32) -> Self {
        Self::BitVec(BitVecSort { width })
    }

    /// Create a sequence sort with the given element sort.
    pub fn seq(element: Self) -> Self {
        Self::Seq(Box::new(element))
    }

    /// Get the element sort if this is a sequence sort.
    pub fn seq_element(&self) -> Option<&Self> {
        match self {
            Self::Seq(elem) => Some(elem),
            _ => None,
        }
    }

    /// Check if this is a sequence sort.
    pub fn is_seq(&self) -> bool {
        matches!(self, Self::Seq(_))
    }

    /// Create an array sort with the given index and element sorts.
    pub fn array(index_sort: Self, element_sort: Self) -> Self {
        Self::Array(Box::new(ArraySort {
            index_sort,
            element_sort,
        }))
    }

    /// Create a struct-like datatype sort with a single constructor.
    pub fn struct_type(
        name: impl Into<String>,
        fields: impl IntoIterator<Item = (impl Into<String>, Self)>,
    ) -> Self {
        let name: String = name.into();
        let fields: Vec<DatatypeField> = fields
            .into_iter()
            .map(|(field_name, sort)| DatatypeField {
                name: field_name.into(),
                sort,
            })
            .collect();

        Self::Datatype(DatatypeSort {
            name: name.clone(),
            constructors: vec![DatatypeConstructor {
                // Ensure uniqueness across multiple struct types in the same SMT file (#948).
                name: format!("{name}_mk"),
                fields,
            }],
        })
    }

    /// Create an enum-like datatype sort with nullary constructors.
    pub fn enum_type(
        name: impl Into<String>,
        variants: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self::Datatype(DatatypeSort {
            name: name.into(),
            constructors: variants
                .into_iter()
                .map(DatatypeConstructor::unit)
                .collect(),
        })
    }

    /// Get the bitvector width if this is a bitvector sort.
    #[must_use = "bitvec_width() result should be inspected"]
    pub fn bitvec_width(&self) -> Option<u32> {
        match self {
            Self::BitVec(bv) => Some(bv.width),
            _ => None,
        }
    }

    /// Get the array index sort if this is an array sort.
    #[must_use = "array_index() result should be inspected"]
    pub fn array_index(&self) -> Option<&Self> {
        match self {
            Self::Array(arr) => Some(&arr.index_sort),
            _ => None,
        }
    }

    /// Get the array element sort if this is an array sort.
    #[must_use = "array_element() result should be inspected"]
    pub fn array_element(&self) -> Option<&Self> {
        match self {
            Self::Array(arr) => Some(&arr.element_sort),
            _ => None,
        }
    }

    /// Returns true if this is a Bool sort.
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    /// Returns true if this is an Int sort.
    pub fn is_int(&self) -> bool {
        matches!(self, Self::Int)
    }

    /// Returns true if this is a Real sort.
    pub fn is_real(&self) -> bool {
        matches!(self, Self::Real)
    }

    /// Returns true if this is a bitvector sort.
    pub fn is_bitvec(&self) -> bool {
        matches!(self, Self::BitVec(_))
    }

    /// Returns true if this is an array sort.
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array(_))
    }

    /// Returns true if this is a regular-language sort.
    pub fn is_reglan(&self) -> bool {
        matches!(self, Self::RegLan)
    }

    /// Returns true if this is a datatype sort.
    pub fn is_datatype(&self) -> bool {
        matches!(self, Self::Datatype(_))
    }

    /// Returns true if this is a String sort.
    pub fn is_string(&self) -> bool {
        matches!(self, Self::String)
    }

    /// Returns true if this is a floating-point sort.
    pub fn is_fp(&self) -> bool {
        matches!(self, Self::FloatingPoint(_, _))
    }

    /// Get the exponent and significand bit widths if this is a floating-point sort.
    #[must_use = "fp_ebits_sbits() result should be inspected"]
    pub fn fp_ebits_sbits(&self) -> Option<(u32, u32)> {
        match self {
            Self::FloatingPoint(eb, sb) => Some((*eb, *sb)),
            _ => None,
        }
    }

    /// Returns true if this is an uninterpreted sort.
    pub fn is_uninterpreted(&self) -> bool {
        matches!(self, Self::Uninterpreted(_))
    }

    /// Returns true if this is the character sort.
    pub fn is_char(&self) -> bool {
        matches!(self, Self::Char)
    }

    /// Returns true if this is a finite-domain sort.
    pub fn is_finite_domain(&self) -> bool {
        matches!(self, Self::FiniteDomain(_, _))
    }

    /// Get the cardinality if this is a finite-domain sort.
    #[must_use = "finite_domain_size() result should be inspected"]
    pub fn finite_domain_size(&self) -> Option<u64> {
        match self {
            Self::FiniteDomain(_, size) => Some(*size),
            _ => None,
        }
    }

    /// Returns true if this is a type variable.
    pub fn is_type_var(&self) -> bool {
        matches!(self, Self::TypeVar(_))
    }

    /// Convert to the internal term-store representation.
    ///
    /// For UF-only datatypes, this maps `Sort::Datatype(dt)` to
    /// `Sort::Uninterpreted(dt.name)` to match the SMT-LIB elaborator behavior
    /// (datatypes are registered as uninterpreted sorts with UF symbols for
    /// constructors/selectors/testers).
    pub fn as_term_sort(&self) -> Self {
        match self {
            Self::Datatype(dt) => Self::Uninterpreted(dt.name.clone()),
            Self::Array(arr) => Self::array(
                arr.index_sort.as_term_sort(),
                arr.element_sort.as_term_sort(),
            ),
            // A `Char` is a bounded `Int` code point in the term store; the
            // `[0, 196607]` invariant is attached separately (FFI background
            // axiom). Lowering to `Int` here keeps every downstream theory /
            // hash-cons / model path `Char`-free (they only ever see `Int`).
            Self::Char => Self::Int,
            // A finite-domain value is a bounded `Int` in the term store; the
            // `0 <= x < size` invariant is attached separately (FFI background
            // axiom), exactly like `Char`.
            Self::FiniteDomain(_, _) => Self::Int,
            // A type variable behaves like the uninterpreted sort of the same
            // name for (monomorphic) solving; the `TypeVar` identity is kept
            // only at the API/FFI layer for introspection.
            Self::TypeVar(name) => Self::Uninterpreted(name.clone()),
            _ => self.clone(),
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::Int => write!(f, "Int"),
            Self::Real => write!(f, "Real"),
            Self::BitVec(bv) => write!(f, "(_ BitVec {})", bv.width),
            Self::Array(arr) => write!(f, "(Array {} {})", arr.index_sort, arr.element_sort),
            Self::String => write!(f, "String"),
            Self::RegLan => write!(f, "RegLan"),
            Self::FloatingPoint(eb, sb) => write!(f, "(_ FloatingPoint {eb} {sb})"),
            Self::Uninterpreted(name) => write!(f, "{name}"),
            Self::Datatype(dt) => write!(f, "{}", dt.name),
            Self::Seq(elem) => write!(f, "(Seq {elem})"),
            Self::Char => write!(f, "Char"),
            // Z3 renders a finite-domain sort / type variable by its bare name.
            Self::FiniteDomain(name, _) | Self::TypeVar(name) => write!(f, "{name}"),
        }
    }
}

#[cfg(test)]
#[path = "sort_tests.rs"]
mod tests;

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// REQUIRES: w1 != w2 (distinct bitvector widths)
    /// ENSURES: BitVec(w1) != BitVec(w2) (different widths are distinct sorts)
    #[kani::proof]
    fn proof_bitvec_width_distinguishes() {
        let w1: u32 = kani::any();
        let w2: u32 = kani::any();
        kani::assume(w1 != w2);

        let bv1 = Sort::bitvec(w1);
        let bv2 = Sort::bitvec(w2);

        assert!(
            bv1 != bv2,
            "Different bitvector widths must be distinct sorts"
        );
    }
}
