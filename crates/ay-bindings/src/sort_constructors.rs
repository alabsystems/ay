// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Sort constructor methods.
//!
//! Factory methods for creating Bool, BitVec, Int, Real, Array,
//! Datatype, String, FloatingPoint, Uninterpreted, RegLan, and Seq sorts.
//! Predicate/accessor methods are in `sort.rs`.

use super::sort::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort, SortInner,
};

impl Sort {
    /// Create a boolean sort.
    /// ENSURES: result.is_bool() is true.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_bool()))]
    pub fn bool() -> Self {
        Self::from_inner(SortInner::Bool)
    }

    /// Create a bitvector sort with the given width.
    /// REQUIRES: width > 0.
    /// ENSURES: result.is_bitvec() is true with the provided width.
    ///
    /// # Panics
    /// Panics if width is 0.
    #[must_use]
    #[cfg_attr(kani, kani::requires(width > 0))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_bitvec()))]
    pub fn bitvec(width: u32) -> Self {
        assert!(width > 0, "BitVec width must be > 0");
        Self::from_inner(SortInner::BitVec(BitVecSort { width }))
    }

    /// Create an 8-bit bitvector sort.
    /// ENSURES: result.bitvec_width() == Some(8).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_bitvec()))]
    pub fn bv8() -> Self {
        Self::bitvec(8)
    }

    /// Create a 16-bit bitvector sort.
    /// ENSURES: result.bitvec_width() == Some(16).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_bitvec()))]
    pub fn bv16() -> Self {
        Self::bitvec(16)
    }

    /// Create a 32-bit bitvector sort.
    /// ENSURES: result.bitvec_width() == Some(32).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_bitvec()))]
    pub fn bv32() -> Self {
        Self::bitvec(32)
    }

    /// Create a 64-bit bitvector sort.
    /// ENSURES: result.bitvec_width() == Some(64).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_bitvec()))]
    pub fn bv64() -> Self {
        Self::bitvec(64)
    }

    /// Create a 128-bit bitvector sort.
    /// ENSURES: result.bitvec_width() == Some(128).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_bitvec()))]
    pub fn bv128() -> Self {
        Self::bitvec(128)
    }

    /// Create an unbounded integer sort.
    /// ENSURES: result.is_int() is true.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_int()))]
    pub fn int() -> Self {
        Self::from_inner(SortInner::Int)
    }

    /// Create a real number sort.
    /// ENSURES: result.is_real() is true.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_real()))]
    pub fn real() -> Self {
        Self::from_inner(SortInner::Real)
    }

    /// Create an array sort.
    /// ENSURES: result.is_array() is true with provided index/element sorts.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_array()))]
    pub fn array(index_sort: Self, element_sort: Self) -> Self {
        Self::from_inner(SortInner::Array(ArraySort {
            index_sort,
            element_sort,
        }))
    }

    /// Create a memory array sort (64-bit addresses to bytes).
    /// ENSURES: result.is_array() with index BitVec(64) and element BitVec(8).
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_array()))]
    pub fn memory() -> Self {
        Self::array(Self::bv64(), Self::bv8())
    }

    /// Create a simple struct datatype sort.
    /// REQUIRES: `fields` are the constructor field sorts in order.
    /// ENSURES: returns Datatype with one constructor named "<datatype_name>_mk".
    ///
    /// NOTE: Constructor names include the datatype name prefix to ensure uniqueness
    /// across multiple struct types in the same SMT file. This fixes #948 where
    /// multiple structs with the generic "mk" constructor caused sort conflicts.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_datatype()))]
    pub fn struct_type(
        name: impl Into<String>,
        fields: impl IntoIterator<Item = (impl Into<String>, Self)>,
    ) -> Self {
        let name_str: String = name.into();
        let constructor_fields = fields
            .into_iter()
            .map(|(field_name, sort)| DatatypeField {
                name: field_name.into(),
                sort,
            })
            .collect();

        Self::from_inner(SortInner::Datatype(DatatypeSort {
            name: name_str.clone(),
            constructors: vec![DatatypeConstructor {
                name: format!("{name_str}_mk"),
                fields: constructor_fields,
            }],
        }))
    }

    /// Create an enum datatype sort.
    /// REQUIRES: `variants` supply constructor names and field sorts.
    /// ENSURES: returns Datatype with one constructor per variant.
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_datatype()))]
    pub fn enum_type<VariantName, Variants, FieldName, VariantFields>(
        name: impl Into<String>,
        variants: Variants,
    ) -> Self
    where
        VariantName: Into<String>,
        Variants: IntoIterator<Item = (VariantName, VariantFields)>,
        FieldName: Into<String>,
        VariantFields: IntoIterator<Item = (FieldName, Self)>,
    {
        let constructors = variants
            .into_iter()
            .map(|(variant_name, fields)| {
                let constructor_fields = fields
                    .into_iter()
                    .map(|(field_name, sort)| DatatypeField {
                        name: field_name.into(),
                        sort,
                    })
                    .collect();
                DatatypeConstructor {
                    name: variant_name.into(),
                    fields: constructor_fields,
                }
            })
            .collect();

        Self::from_inner(SortInner::Datatype(DatatypeSort {
            name: name.into(),
            constructors,
        }))
    }

    /// Create a simple enum datatype sort with nullary constructors.
    ///
    /// This is a convenience method for enum types where all variants are
    /// nullary (no fields). Matches ay-core's `Sort::enum_type()` signature.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::Sort;
    ///
    /// // Simple enum with no fields
    /// let color = Sort::simple_enum_type("Color", ["Red", "Green", "Blue"]);
    /// assert!(color.is_datatype());
    /// ```
    #[must_use]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_datatype()))]
    pub fn simple_enum_type(
        name: impl Into<String>,
        variants: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        let constructors: Vec<(String, Vec<(String, Self)>)> =
            variants.into_iter().map(|v| (v.into(), vec![])).collect();
        Self::enum_type(name, constructors)
    }

    /// Create a tuple datatype sort with auto-generated field names.
    ///
    /// This is a convenience method that creates a datatype with fields named
    /// `_0`, `_1`, `_2`, etc. - matching Rust's tuple field access syntax.
    ///
    /// REQUIRES: `sorts` is non-empty.
    /// ENSURES: returns Datatype with fields named `_0`, `_1`, etc.
    ///
    /// # Panics
    /// Panics if `sorts` is empty.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::Sort;
    ///
    /// // Create (Int, Bool) tuple type
    /// let pair = Sort::tuple(vec![Sort::int(), Sort::bool()]);
    /// assert!(pair.is_datatype());
    /// assert!(pair.datatype_has_field("_0"));
    /// assert!(pair.datatype_has_field("_1"));
    /// ```
    #[must_use]
    #[cfg_attr(kani, kani::requires(!sorts.is_empty()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.is_datatype()))]
    pub fn tuple(sorts: Vec<Self>) -> Self {
        assert!(!sorts.is_empty(), "Tuple must have at least one element");

        let fields: Vec<(String, Self)> = sorts
            .into_iter()
            .enumerate()
            .map(|(i, sort)| (format!("_{i}"), sort))
            .collect();

        // Use a unique name based on field count to avoid collisions
        let name = format!("Tuple{}", fields.len());
        Self::struct_type(name, fields)
    }

    /// Create a string sort.
    #[must_use]
    pub fn string() -> Self {
        Self::from_inner(SortInner::String)
    }

    /// Create a floating-point sort with given exponent and significand widths.
    #[must_use]
    pub fn floating_point(exponent_bits: u32, significand_bits: u32) -> Self {
        Self::from_inner(SortInner::FloatingPoint(exponent_bits, significand_bits))
    }

    /// Shorthand for `floating_point`.
    #[must_use]
    pub fn fp(exponent_bits: u32, significand_bits: u32) -> Self {
        Self::floating_point(exponent_bits, significand_bits)
    }

    /// IEEE 754 half-precision (Float16): 5-bit exponent, 11-bit significand.
    #[must_use]
    pub fn fp16() -> Self {
        Self::floating_point(5, 11)
    }

    /// IEEE 754 single-precision (Float32): 8-bit exponent, 24-bit significand.
    #[must_use]
    pub fn fp32() -> Self {
        Self::floating_point(8, 24)
    }

    /// IEEE 754 double-precision (Float64): 11-bit exponent, 53-bit significand.
    #[must_use]
    pub fn fp64() -> Self {
        Self::floating_point(11, 53)
    }

    /// Create an uninterpreted sort with the given name.
    #[must_use]
    pub fn uninterpreted(name: impl Into<String>) -> Self {
        Self::from_inner(SortInner::Uninterpreted(name.into()))
    }

    /// Create a regular language sort.
    #[must_use]
    pub fn reglan() -> Self {
        Self::from_inner(SortInner::RegLan)
    }

    /// Create a sequence sort with the given element sort.
    #[must_use]
    pub fn seq(element: Self) -> Self {
        Self::from_inner(SortInner::Seq(Box::new(element)))
    }
}
