// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! AY Sort definitions.
//!
//! Sorts are the SMT equivalent of types. This module defines the sorts
//! supported by AY for verification of Rust programs.
//!
//! ## Sort Hierarchy
//!
//! ```text
//! Sort
//! ├── Bool           - Boolean values
//! ├── BitVec(width)  - Fixed-width bitvectors (integers, pointers)
//! ├── Int            - Mathematical integers (unbounded)
//! ├── Real           - Mathematical reals
//! ├── Array(idx,elem)- SMT arrays (memory model)
//! └── Datatype       - Algebraic datatypes (structs, enums)
//! ```
//!
//! ## Rust Type Mapping
//!
//! | Rust Type | AY Sort |
//! |-----------|---------|
//! | bool | Bool |
//! | i8/u8 | BitVec(8) |
//! | i32/u32 | BitVec(32) |
//! | i64/u64 | BitVec(64) |
//! | usize | BitVec(64) |
//! | *const T | BitVec(64) |
//! | &T | BitVec(64) |
//! | [T; N] | Array(BitVec(idx_bits), T_sort) |
//! | struct | Datatype |
//! | enum | Datatype |

use crate::format_symbol;
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

/// AY Sort - the SMT equivalent of types.
///
/// Each AY expression has a sort that determines valid operations.
///
/// # Memory Efficiency (#1006)
///
/// Sort is Arc-wrapped for O(1) cloning. The inner sort data is shared
/// across all clones, reducing memory overhead when sorts are frequently
/// cloned (e.g., 178+ clones in statement/mod.rs alone).
///
/// ## Before (O(n) clone):
/// ```text
/// sort.clone() → deep copy of DatatypeSort → O(fields × constructors)
/// ```
///
/// ## After (O(1) clone):
/// ```text
/// sort.clone() → Arc refcount increment → O(1)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort(Arc<SortInner>);

/// Inner sort representation.
///
/// This enum contains the actual sort data. It's wrapped in Arc by Sort
/// for efficient cloning.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SortInner {
    /// Boolean sort (true/false).
    Bool,

    /// Fixed-width bitvector.
    ///
    /// Used for integers, pointers, and memory addresses.
    /// Width must be > 0.
    BitVec(BitVecSort),

    /// Unbounded mathematical integer.
    ///
    /// Used for integer arithmetic that may exceed machine width.
    Int,

    /// Mathematical real numbers.
    ///
    /// Used for floating-point approximations and real arithmetic.
    Real,

    /// SMT Array sort.
    ///
    /// Maps index sort to element sort. Used for memory modeling.
    /// Note: No Box needed - already behind Arc in Sort.
    Array(ArraySort),

    /// Algebraic datatype (struct, enum, tuple).
    Datatype(DatatypeSort),

    /// String sort.
    String,

    /// IEEE 754 floating-point sort with exponent and significand bit widths.
    FloatingPoint(u32, u32),

    /// Uninterpreted sort (user-defined opaque type).
    Uninterpreted(String),

    /// Regular language sort (for string constraints).
    RegLan,

    /// Parametric sequence sort: `(Seq T)` where `T` is the element sort.
    Seq(Box<Sort>),
}

/// Bitvector sort with fixed width.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitVecSort {
    /// Width in bits. Must be > 0.
    pub width: u32,
}

/// SMT Array sort.
///
/// An array maps indices of `index_sort` to values of `element_sort`.
/// In SMT-LIB2: `(Array index_sort element_sort)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArraySort {
    /// Sort of array indices (typically BitVec for addresses).
    pub index_sort: Sort,
    /// Sort of array elements.
    pub element_sort: Sort,
}

/// Algebraic datatype sort.
///
/// Used for structs, enums, and tuples in Rust.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DatatypeSort {
    /// Name of the datatype.
    pub name: String,
    /// Constructors (variants for enums, single for structs).
    pub constructors: Vec<DatatypeConstructor>,
}

/// A constructor for an algebraic datatype.
///
/// For structs: single constructor with fields.
/// For enums: one constructor per variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DatatypeConstructor {
    /// Constructor name.
    pub name: String,
    /// Fields (selectors) with their sorts.
    pub fields: Vec<DatatypeField>,
}

/// A field in a datatype constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DatatypeField {
    /// Field name (selector name in SMT-LIB2).
    pub name: String,
    /// Sort of the field.
    pub sort: Sort,
}

impl Sort {
    /// Access the inner sort representation.
    ///
    /// Use this for pattern matching when you need to inspect the sort variant.
    #[inline]
    #[must_use]
    pub fn inner(&self) -> &SortInner {
        &self.0
    }

    /// Create a Sort from a SortInner.
    ///
    /// This wraps the inner sort in an Arc for efficient cloning.
    #[inline]
    pub(crate) fn from_inner(inner: SortInner) -> Self {
        Self(Arc::new(inner))
    }

    // Constructor methods (bool, bitvec, int, real, array, etc.)
    // are in sort_constructors.rs.

    /// Check if this is a boolean sort.
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self.inner(), SortInner::Bool)
    }

    /// Check if this is a bitvector sort.
    #[must_use]
    pub fn is_bitvec(&self) -> bool {
        matches!(self.inner(), SortInner::BitVec(_))
    }

    /// Check if this is an integer sort.
    #[must_use]
    pub fn is_int(&self) -> bool {
        matches!(self.inner(), SortInner::Int)
    }

    /// Check if this is a real sort.
    #[must_use]
    pub fn is_real(&self) -> bool {
        matches!(self.inner(), SortInner::Real)
    }

    /// Check if this is an array sort.
    #[must_use]
    pub fn is_array(&self) -> bool {
        matches!(self.inner(), SortInner::Array(_))
    }

    /// Check if this is a floating-point sort.
    #[must_use]
    pub fn is_floating_point(&self) -> bool {
        matches!(self.inner(), SortInner::FloatingPoint(_, _))
    }

    /// Get the exponent bit width, if this is a floating-point sort.
    #[must_use]
    pub fn fp_exponent_bits(&self) -> Option<u32> {
        match self.inner() {
            SortInner::FloatingPoint(eb, _) => Some(*eb),
            _ => None,
        }
    }

    /// Get the significand bit width, if this is a floating-point sort.
    #[must_use]
    pub fn fp_significand_bits(&self) -> Option<u32> {
        match self.inner() {
            SortInner::FloatingPoint(_, sb) => Some(*sb),
            _ => None,
        }
    }

    /// Check if this is a datatype sort.
    #[must_use]
    pub fn is_datatype(&self) -> bool {
        matches!(self.inner(), SortInner::Datatype(_))
    }

    /// Get the datatype name, if this is a datatype sort.
    #[must_use]
    pub fn datatype_name(&self) -> Option<&str> {
        match self.inner() {
            SortInner::Datatype(dt) => Some(&dt.name),
            _ => None,
        }
    }

    /// Check whether this datatype has a constructor with the given name.
    #[must_use]
    pub fn datatype_has_constructor(&self, constructor_name: &str) -> bool {
        match self.inner() {
            SortInner::Datatype(dt) => dt
                .constructors
                .iter()
                .any(|constructor| constructor.name == constructor_name),
            _ => false,
        }
    }

    /// Check whether this datatype has a field (selector) with the given name.
    #[must_use]
    pub fn datatype_has_field(&self, field_name: &str) -> bool {
        match self.inner() {
            SortInner::Datatype(dt) => dt.constructors.iter().any(|constructor| {
                constructor
                    .fields
                    .iter()
                    .any(|field| field.name == field_name)
            }),
            _ => false,
        }
    }

    /// Get the default (first) constructor name for a datatype sort.
    ///
    /// For struct types created with `struct_type`, this returns the unique
    /// constructor name (e.g., "Point_mk" for struct "Point").
    /// For enum types, this returns the first variant's constructor name.
    ///
    /// Returns None if not a datatype or if the datatype has no constructors.
    #[must_use]
    pub fn datatype_default_constructor(&self) -> Option<&str> {
        match self.inner() {
            SortInner::Datatype(dt) => dt.constructors.first().map(|c| c.name.as_str()),
            _ => None,
        }
    }

    /// Get the bitvector width, if this is a bitvector sort.
    #[must_use]
    pub fn bitvec_width(&self) -> Option<u32> {
        match self.inner() {
            SortInner::BitVec(bv) => Some(bv.width),
            _ => None,
        }
    }

    /// Get the bitvector sort details if this is a bitvector sort.
    ///
    /// Returns the [`BitVecSort`] containing width information.
    /// For API consistency with [`Self::array_sort()`] and [`Self::datatype_sort()`].
    #[must_use]
    pub fn bitvec_sort(&self) -> Option<&BitVecSort> {
        match self.inner() {
            SortInner::BitVec(bv) => Some(bv),
            _ => None,
        }
    }

    /// Check if this is a string sort.
    #[must_use]
    pub fn is_string(&self) -> bool {
        matches!(self.inner(), SortInner::String)
    }

    /// Check if this is a sequence sort.
    #[must_use]
    pub fn is_seq(&self) -> bool {
        matches!(self.inner(), SortInner::Seq(_))
    }

    /// Get the element sort of a sequence sort.
    #[must_use]
    pub fn seq_element(&self) -> Option<&Self> {
        match self.inner() {
            SortInner::Seq(elem) => Some(elem),
            _ => None,
        }
    }

    /// Check if this is a regular language sort.
    #[must_use]
    pub fn is_reglan(&self) -> bool {
        matches!(self.inner(), SortInner::RegLan)
    }

    /// Check if this is a numeric sort (BitVec, Int, or Real).
    #[must_use]
    pub fn is_numeric(&self) -> bool {
        matches!(
            self.inner(),
            SortInner::BitVec(_) | SortInner::Int | SortInner::Real
        )
    }

    /// Get the array sort details if this is an array sort.
    #[must_use]
    pub fn array_sort(&self) -> Option<&ArraySort> {
        match self.inner() {
            SortInner::Array(arr) => Some(arr),
            _ => None,
        }
    }

    /// Get the datatype sort details if this is a datatype sort.
    #[must_use]
    pub fn datatype_sort(&self) -> Option<&DatatypeSort> {
        match self.inner() {
            SortInner::Datatype(dt) => Some(dt),
            _ => None,
        }
    }
}

// ay-core term-store integration (requires "direct" feature)
#[cfg(feature = "direct")]
impl Sort {
    /// Convert to a term-store compatible sort.
    ///
    /// For datatypes, this maps to an uninterpreted sort with the datatype's name,
    /// matching ay-core's SMT-LIB elaborator behavior where datatypes are registered
    /// as uninterpreted sorts with UF symbols for constructors/selectors/testers.
    ///
    /// For arrays, this recursively converts index and element sorts.
    /// Other sorts are returned unchanged.
    ///
    /// Returns a `ay_core::Sort` since the result may be an uninterpreted sort,
    /// which ay-bindings doesn't support.
    #[cfg_attr(not(test), allow(dead_code))]
    #[must_use]
    pub(crate) fn as_term_sort(&self) -> ay_core::Sort {
        ay_core::Sort::from(self).as_term_sort()
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.inner() {
            SortInner::Bool => write!(f, "Bool"),
            SortInner::BitVec(bv) => write!(f, "(_ BitVec {})", bv.width),
            SortInner::Int => write!(f, "Int"),
            SortInner::Real => write!(f, "Real"),
            SortInner::Array(arr) => {
                write!(f, "(Array {} {})", arr.index_sort, arr.element_sort)
            }
            SortInner::Datatype(dt) => write!(f, "{}", format_symbol(&dt.name)),
            SortInner::String => write!(f, "String"),
            SortInner::FloatingPoint(eb, sb) => {
                write!(f, "(_ FloatingPoint {eb} {sb})")
            }
            SortInner::Uninterpreted(name) => write!(f, "{}", format_symbol(name)),
            SortInner::RegLan => write!(f, "RegLan"),
            SortInner::Seq(elem) => write!(f, "(Seq {elem})"),
        }
    }
}

impl Display for BitVecSort {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(_ BitVec {})", self.width)
    }
}

impl Display for ArraySort {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(Array {} {})", self.index_sort, self.element_sort)
    }
}

// ============================================================================
// ay-core Sort conversions (requires "direct" feature)
// ============================================================================

#[cfg(feature = "direct")]
mod core_conversions;

// Note: The From impls in core_conversions are automatically available as trait impls.
// No re-export needed.

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "sort_tests.rs"]
mod tests;

#[allow(clippy::panic)]
#[cfg(all(test, feature = "direct"))]
#[path = "sort_core_conversion_tests.rs"]
mod core_conversion_tests;
