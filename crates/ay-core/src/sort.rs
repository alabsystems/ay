// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort system for AY
//!
//! Sorts are the types of terms in SMT-LIB.

use std::fmt;

// ============================================================================
// Wrapper types for rich datatype representation
// ============================================================================

/// Bitvector sort with fixed width.
///
/// This wrapper type provides explicit documentation and helper methods.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

// Hand-written serde impls for the sort types.
//
// These reproduce byte-for-byte what `#[derive(Serialize, Deserialize)]`
// generated for these types (structs with `#[serde(deny_unknown_fields)]`:
// same field order, indices, and names, unknown fields rejected; `Sort`:
// externally tagged, same variant order, indices, and names), written as
// plain matches with no operation that can panic. The derive expansions
// carried Trust L0 panic-freedom obligations the verifier could not
// discharge; this form discharges them by construction.
mod sort_serde {
    use super::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use serde::de::{
        Deserialize, Deserializer, EnumAccess, Error as DeError, MapAccess, SeqAccess, Unexpected,
        VariantAccess, Visitor,
    };
    use serde::ser::{Serialize, SerializeStruct, SerializeTupleVariant, Serializer};
    use std::fmt;

    // ------------------------------------------------------------------
    // BitVecSort
    // ------------------------------------------------------------------

    const BIT_VEC_SORT_FIELDS: &[&str] = &["width"];

    impl Serialize for BitVecSort {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut state = serializer.serialize_struct("BitVecSort", 1)?;
            state.serialize_field("width", &self.width)?;
            state.end()
        }
    }

    enum BitVecSortField {
        Width,
    }

    impl<'de> Deserialize<'de> for BitVecSortField {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_identifier(BitVecSortFieldVisitor)
        }
    }

    struct BitVecSortFieldVisitor;

    impl Visitor<'_> for BitVecSortFieldVisitor {
        type Value = BitVecSortField;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("field identifier")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                0 => Ok(BitVecSortField::Width),
                _ => Err(DeError::invalid_value(
                    Unexpected::Unsigned(value),
                    &"field index 0 <= i < 1",
                )),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                "width" => Ok(BitVecSortField::Width),
                _ => Err(DeError::unknown_field(value, BIT_VEC_SORT_FIELDS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                b"width" => Ok(BitVecSortField::Width),
                _ => Err(DeError::unknown_field(
                    &String::from_utf8_lossy(value),
                    BIT_VEC_SORT_FIELDS,
                )),
            }
        }
    }

    struct BitVecSortVisitor;

    impl<'de> Visitor<'de> for BitVecSortVisitor {
        type Value = BitVecSort;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("struct BitVecSort")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let width = match seq.next_element::<u32>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        0,
                        &"struct BitVecSort with 1 element",
                    ));
                }
            };
            Ok(BitVecSort { width })
        }

        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut width: Option<u32> = None;
            while let Some(key) = map.next_key::<BitVecSortField>()? {
                match key {
                    BitVecSortField::Width => {
                        if width.is_some() {
                            return Err(DeError::duplicate_field("width"));
                        }
                        width = Some(map.next_value()?);
                    }
                }
            }
            let Some(width) = width else {
                return Err(DeError::missing_field("width"));
            };
            Ok(BitVecSort { width })
        }
    }

    impl<'de> Deserialize<'de> for BitVecSort {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_struct("BitVecSort", BIT_VEC_SORT_FIELDS, BitVecSortVisitor)
        }
    }

    // ------------------------------------------------------------------
    // ArraySort
    // ------------------------------------------------------------------

    const ARRAY_SORT_FIELDS: &[&str] = &["index_sort", "element_sort"];

    impl Serialize for ArraySort {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut state = serializer.serialize_struct("ArraySort", 2)?;
            state.serialize_field("index_sort", &self.index_sort)?;
            state.serialize_field("element_sort", &self.element_sort)?;
            state.end()
        }
    }

    enum ArraySortField {
        IndexSort,
        ElementSort,
    }

    impl<'de> Deserialize<'de> for ArraySortField {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_identifier(ArraySortFieldVisitor)
        }
    }

    struct ArraySortFieldVisitor;

    impl Visitor<'_> for ArraySortFieldVisitor {
        type Value = ArraySortField;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("field identifier")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                0 => Ok(ArraySortField::IndexSort),
                1 => Ok(ArraySortField::ElementSort),
                _ => Err(DeError::invalid_value(
                    Unexpected::Unsigned(value),
                    &"field index 0 <= i < 2",
                )),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                "index_sort" => Ok(ArraySortField::IndexSort),
                "element_sort" => Ok(ArraySortField::ElementSort),
                _ => Err(DeError::unknown_field(value, ARRAY_SORT_FIELDS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                b"index_sort" => Ok(ArraySortField::IndexSort),
                b"element_sort" => Ok(ArraySortField::ElementSort),
                _ => Err(DeError::unknown_field(
                    &String::from_utf8_lossy(value),
                    ARRAY_SORT_FIELDS,
                )),
            }
        }
    }

    struct ArraySortVisitor;

    impl<'de> Visitor<'de> for ArraySortVisitor {
        type Value = ArraySort;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("struct ArraySort")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let index_sort = match seq.next_element::<Sort>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        0,
                        &"struct ArraySort with 2 elements",
                    ));
                }
            };
            let element_sort = match seq.next_element::<Sort>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        1,
                        &"struct ArraySort with 2 elements",
                    ));
                }
            };
            Ok(ArraySort {
                index_sort,
                element_sort,
            })
        }

        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut index_sort: Option<Sort> = None;
            let mut element_sort: Option<Sort> = None;
            while let Some(key) = map.next_key::<ArraySortField>()? {
                match key {
                    ArraySortField::IndexSort => {
                        if index_sort.is_some() {
                            return Err(DeError::duplicate_field("index_sort"));
                        }
                        index_sort = Some(map.next_value()?);
                    }
                    ArraySortField::ElementSort => {
                        if element_sort.is_some() {
                            return Err(DeError::duplicate_field("element_sort"));
                        }
                        element_sort = Some(map.next_value()?);
                    }
                }
            }
            let Some(index_sort) = index_sort else {
                return Err(DeError::missing_field("index_sort"));
            };
            let Some(element_sort) = element_sort else {
                return Err(DeError::missing_field("element_sort"));
            };
            Ok(ArraySort {
                index_sort,
                element_sort,
            })
        }
    }

    impl<'de> Deserialize<'de> for ArraySort {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_struct("ArraySort", ARRAY_SORT_FIELDS, ArraySortVisitor)
        }
    }

    // ------------------------------------------------------------------
    // DatatypeField
    // ------------------------------------------------------------------

    const DATATYPE_FIELD_FIELDS: &[&str] = &["name", "sort"];

    impl Serialize for DatatypeField {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut state = serializer.serialize_struct("DatatypeField", 2)?;
            state.serialize_field("name", &self.name)?;
            state.serialize_field("sort", &self.sort)?;
            state.end()
        }
    }

    enum DatatypeFieldField {
        Name,
        Sort,
    }

    impl<'de> Deserialize<'de> for DatatypeFieldField {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_identifier(DatatypeFieldFieldVisitor)
        }
    }

    struct DatatypeFieldFieldVisitor;

    impl Visitor<'_> for DatatypeFieldFieldVisitor {
        type Value = DatatypeFieldField;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("field identifier")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                0 => Ok(DatatypeFieldField::Name),
                1 => Ok(DatatypeFieldField::Sort),
                _ => Err(DeError::invalid_value(
                    Unexpected::Unsigned(value),
                    &"field index 0 <= i < 2",
                )),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                "name" => Ok(DatatypeFieldField::Name),
                "sort" => Ok(DatatypeFieldField::Sort),
                _ => Err(DeError::unknown_field(value, DATATYPE_FIELD_FIELDS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                b"name" => Ok(DatatypeFieldField::Name),
                b"sort" => Ok(DatatypeFieldField::Sort),
                _ => Err(DeError::unknown_field(
                    &String::from_utf8_lossy(value),
                    DATATYPE_FIELD_FIELDS,
                )),
            }
        }
    }

    struct DatatypeFieldVisitor;

    impl<'de> Visitor<'de> for DatatypeFieldVisitor {
        type Value = DatatypeField;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("struct DatatypeField")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let name = match seq.next_element::<String>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        0,
                        &"struct DatatypeField with 2 elements",
                    ));
                }
            };
            let sort = match seq.next_element::<Sort>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        1,
                        &"struct DatatypeField with 2 elements",
                    ));
                }
            };
            Ok(DatatypeField { name, sort })
        }

        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut name: Option<String> = None;
            let mut sort: Option<Sort> = None;
            while let Some(key) = map.next_key::<DatatypeFieldField>()? {
                match key {
                    DatatypeFieldField::Name => {
                        if name.is_some() {
                            return Err(DeError::duplicate_field("name"));
                        }
                        name = Some(map.next_value()?);
                    }
                    DatatypeFieldField::Sort => {
                        if sort.is_some() {
                            return Err(DeError::duplicate_field("sort"));
                        }
                        sort = Some(map.next_value()?);
                    }
                }
            }
            let Some(name) = name else {
                return Err(DeError::missing_field("name"));
            };
            let Some(sort) = sort else {
                return Err(DeError::missing_field("sort"));
            };
            Ok(DatatypeField { name, sort })
        }
    }

    impl<'de> Deserialize<'de> for DatatypeField {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_struct(
                "DatatypeField",
                DATATYPE_FIELD_FIELDS,
                DatatypeFieldVisitor,
            )
        }
    }

    // ------------------------------------------------------------------
    // DatatypeConstructor
    // ------------------------------------------------------------------

    const DATATYPE_CONSTRUCTOR_FIELDS: &[&str] = &["name", "fields"];

    impl Serialize for DatatypeConstructor {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut state = serializer.serialize_struct("DatatypeConstructor", 2)?;
            state.serialize_field("name", &self.name)?;
            state.serialize_field("fields", &self.fields)?;
            state.end()
        }
    }

    enum DatatypeConstructorField {
        Name,
        Fields,
    }

    impl<'de> Deserialize<'de> for DatatypeConstructorField {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_identifier(DatatypeConstructorFieldVisitor)
        }
    }

    struct DatatypeConstructorFieldVisitor;

    impl Visitor<'_> for DatatypeConstructorFieldVisitor {
        type Value = DatatypeConstructorField;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("field identifier")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                0 => Ok(DatatypeConstructorField::Name),
                1 => Ok(DatatypeConstructorField::Fields),
                _ => Err(DeError::invalid_value(
                    Unexpected::Unsigned(value),
                    &"field index 0 <= i < 2",
                )),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                "name" => Ok(DatatypeConstructorField::Name),
                "fields" => Ok(DatatypeConstructorField::Fields),
                _ => Err(DeError::unknown_field(value, DATATYPE_CONSTRUCTOR_FIELDS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                b"name" => Ok(DatatypeConstructorField::Name),
                b"fields" => Ok(DatatypeConstructorField::Fields),
                _ => Err(DeError::unknown_field(
                    &String::from_utf8_lossy(value),
                    DATATYPE_CONSTRUCTOR_FIELDS,
                )),
            }
        }
    }

    struct DatatypeConstructorVisitor;

    impl<'de> Visitor<'de> for DatatypeConstructorVisitor {
        type Value = DatatypeConstructor;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("struct DatatypeConstructor")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let name = match seq.next_element::<String>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        0,
                        &"struct DatatypeConstructor with 2 elements",
                    ));
                }
            };
            let fields = match seq.next_element::<Vec<DatatypeField>>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        1,
                        &"struct DatatypeConstructor with 2 elements",
                    ));
                }
            };
            Ok(DatatypeConstructor { name, fields })
        }

        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut name: Option<String> = None;
            let mut fields: Option<Vec<DatatypeField>> = None;
            while let Some(key) = map.next_key::<DatatypeConstructorField>()? {
                match key {
                    DatatypeConstructorField::Name => {
                        if name.is_some() {
                            return Err(DeError::duplicate_field("name"));
                        }
                        name = Some(map.next_value()?);
                    }
                    DatatypeConstructorField::Fields => {
                        if fields.is_some() {
                            return Err(DeError::duplicate_field("fields"));
                        }
                        fields = Some(map.next_value()?);
                    }
                }
            }
            let Some(name) = name else {
                return Err(DeError::missing_field("name"));
            };
            let Some(fields) = fields else {
                return Err(DeError::missing_field("fields"));
            };
            Ok(DatatypeConstructor { name, fields })
        }
    }

    impl<'de> Deserialize<'de> for DatatypeConstructor {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_struct(
                "DatatypeConstructor",
                DATATYPE_CONSTRUCTOR_FIELDS,
                DatatypeConstructorVisitor,
            )
        }
    }

    // ------------------------------------------------------------------
    // DatatypeSort
    // ------------------------------------------------------------------

    const DATATYPE_SORT_FIELDS: &[&str] = &["name", "constructors"];

    impl Serialize for DatatypeSort {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut state = serializer.serialize_struct("DatatypeSort", 2)?;
            state.serialize_field("name", &self.name)?;
            state.serialize_field("constructors", &self.constructors)?;
            state.end()
        }
    }

    enum DatatypeSortField {
        Name,
        Constructors,
    }

    impl<'de> Deserialize<'de> for DatatypeSortField {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_identifier(DatatypeSortFieldVisitor)
        }
    }

    struct DatatypeSortFieldVisitor;

    impl Visitor<'_> for DatatypeSortFieldVisitor {
        type Value = DatatypeSortField;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("field identifier")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                0 => Ok(DatatypeSortField::Name),
                1 => Ok(DatatypeSortField::Constructors),
                _ => Err(DeError::invalid_value(
                    Unexpected::Unsigned(value),
                    &"field index 0 <= i < 2",
                )),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                "name" => Ok(DatatypeSortField::Name),
                "constructors" => Ok(DatatypeSortField::Constructors),
                _ => Err(DeError::unknown_field(value, DATATYPE_SORT_FIELDS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                b"name" => Ok(DatatypeSortField::Name),
                b"constructors" => Ok(DatatypeSortField::Constructors),
                _ => Err(DeError::unknown_field(
                    &String::from_utf8_lossy(value),
                    DATATYPE_SORT_FIELDS,
                )),
            }
        }
    }

    struct DatatypeSortVisitor;

    impl<'de> Visitor<'de> for DatatypeSortVisitor {
        type Value = DatatypeSort;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("struct DatatypeSort")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let name = match seq.next_element::<String>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        0,
                        &"struct DatatypeSort with 2 elements",
                    ));
                }
            };
            let constructors = match seq.next_element::<Vec<DatatypeConstructor>>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        1,
                        &"struct DatatypeSort with 2 elements",
                    ));
                }
            };
            Ok(DatatypeSort { name, constructors })
        }

        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut name: Option<String> = None;
            let mut constructors: Option<Vec<DatatypeConstructor>> = None;
            while let Some(key) = map.next_key::<DatatypeSortField>()? {
                match key {
                    DatatypeSortField::Name => {
                        if name.is_some() {
                            return Err(DeError::duplicate_field("name"));
                        }
                        name = Some(map.next_value()?);
                    }
                    DatatypeSortField::Constructors => {
                        if constructors.is_some() {
                            return Err(DeError::duplicate_field("constructors"));
                        }
                        constructors = Some(map.next_value()?);
                    }
                }
            }
            let Some(name) = name else {
                return Err(DeError::missing_field("name"));
            };
            let Some(constructors) = constructors else {
                return Err(DeError::missing_field("constructors"));
            };
            Ok(DatatypeSort { name, constructors })
        }
    }

    impl<'de> Deserialize<'de> for DatatypeSort {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_struct(
                "DatatypeSort",
                DATATYPE_SORT_FIELDS,
                DatatypeSortVisitor,
            )
        }
    }

    // ------------------------------------------------------------------
    // Sort
    // ------------------------------------------------------------------

    const SORT_VARIANTS: &[&str] = &[
        "Bool",
        "Int",
        "Real",
        "BitVec",
        "Array",
        "String",
        "RegLan",
        "FloatingPoint",
        "Uninterpreted",
        "Datatype",
        "Seq",
        "Char",
        "FiniteDomain",
        "TypeVar",
    ];

    impl Serialize for Sort {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            match *self {
                Sort::Bool => serializer.serialize_unit_variant("Sort", 0, "Bool"),
                Sort::Int => serializer.serialize_unit_variant("Sort", 1, "Int"),
                Sort::Real => serializer.serialize_unit_variant("Sort", 2, "Real"),
                Sort::BitVec(ref bv) => {
                    serializer.serialize_newtype_variant("Sort", 3, "BitVec", bv)
                }
                Sort::Array(ref arr) => {
                    serializer.serialize_newtype_variant("Sort", 4, "Array", arr)
                }
                Sort::String => serializer.serialize_unit_variant("Sort", 5, "String"),
                Sort::RegLan => serializer.serialize_unit_variant("Sort", 6, "RegLan"),
                Sort::FloatingPoint(ref eb, ref sb) => {
                    let mut tv =
                        serializer.serialize_tuple_variant("Sort", 7, "FloatingPoint", 2)?;
                    tv.serialize_field(eb)?;
                    tv.serialize_field(sb)?;
                    tv.end()
                }
                Sort::Uninterpreted(ref name) => {
                    serializer.serialize_newtype_variant("Sort", 8, "Uninterpreted", name)
                }
                Sort::Datatype(ref dt) => {
                    serializer.serialize_newtype_variant("Sort", 9, "Datatype", dt)
                }
                Sort::Seq(ref elem) => {
                    serializer.serialize_newtype_variant("Sort", 10, "Seq", elem)
                }
                Sort::Char => serializer.serialize_unit_variant("Sort", 11, "Char"),
                Sort::FiniteDomain(ref name, ref size) => {
                    let mut tv =
                        serializer.serialize_tuple_variant("Sort", 12, "FiniteDomain", 2)?;
                    tv.serialize_field(name)?;
                    tv.serialize_field(size)?;
                    tv.end()
                }
                Sort::TypeVar(ref name) => {
                    serializer.serialize_newtype_variant("Sort", 13, "TypeVar", name)
                }
            }
        }
    }

    enum SortVariant {
        Bool,
        Int,
        Real,
        BitVec,
        Array,
        String,
        RegLan,
        FloatingPoint,
        Uninterpreted,
        Datatype,
        Seq,
        Char,
        FiniteDomain,
        TypeVar,
    }

    impl<'de> Deserialize<'de> for SortVariant {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_identifier(SortVariantVisitor)
        }
    }

    struct SortVariantVisitor;

    impl Visitor<'_> for SortVariantVisitor {
        type Value = SortVariant;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("variant identifier")
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                0 => Ok(SortVariant::Bool),
                1 => Ok(SortVariant::Int),
                2 => Ok(SortVariant::Real),
                3 => Ok(SortVariant::BitVec),
                4 => Ok(SortVariant::Array),
                5 => Ok(SortVariant::String),
                6 => Ok(SortVariant::RegLan),
                7 => Ok(SortVariant::FloatingPoint),
                8 => Ok(SortVariant::Uninterpreted),
                9 => Ok(SortVariant::Datatype),
                10 => Ok(SortVariant::Seq),
                11 => Ok(SortVariant::Char),
                12 => Ok(SortVariant::FiniteDomain),
                13 => Ok(SortVariant::TypeVar),
                _ => Err(DeError::invalid_value(
                    Unexpected::Unsigned(value),
                    &"variant index 0 <= i < 14",
                )),
            }
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                "Bool" => Ok(SortVariant::Bool),
                "Int" => Ok(SortVariant::Int),
                "Real" => Ok(SortVariant::Real),
                "BitVec" => Ok(SortVariant::BitVec),
                "Array" => Ok(SortVariant::Array),
                "String" => Ok(SortVariant::String),
                "RegLan" => Ok(SortVariant::RegLan),
                "FloatingPoint" => Ok(SortVariant::FloatingPoint),
                "Uninterpreted" => Ok(SortVariant::Uninterpreted),
                "Datatype" => Ok(SortVariant::Datatype),
                "Seq" => Ok(SortVariant::Seq),
                "Char" => Ok(SortVariant::Char),
                "FiniteDomain" => Ok(SortVariant::FiniteDomain),
                "TypeVar" => Ok(SortVariant::TypeVar),
                _ => Err(DeError::unknown_variant(value, SORT_VARIANTS)),
            }
        }

        fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
        where
            E: DeError,
        {
            match value {
                b"Bool" => Ok(SortVariant::Bool),
                b"Int" => Ok(SortVariant::Int),
                b"Real" => Ok(SortVariant::Real),
                b"BitVec" => Ok(SortVariant::BitVec),
                b"Array" => Ok(SortVariant::Array),
                b"String" => Ok(SortVariant::String),
                b"RegLan" => Ok(SortVariant::RegLan),
                b"FloatingPoint" => Ok(SortVariant::FloatingPoint),
                b"Uninterpreted" => Ok(SortVariant::Uninterpreted),
                b"Datatype" => Ok(SortVariant::Datatype),
                b"Seq" => Ok(SortVariant::Seq),
                b"Char" => Ok(SortVariant::Char),
                b"FiniteDomain" => Ok(SortVariant::FiniteDomain),
                b"TypeVar" => Ok(SortVariant::TypeVar),
                _ => Err(DeError::unknown_variant(
                    &String::from_utf8_lossy(value),
                    SORT_VARIANTS,
                )),
            }
        }
    }

    struct SortFloatingPointVisitor;

    impl<'de> Visitor<'de> for SortFloatingPointVisitor {
        type Value = Sort;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("tuple variant Sort::FloatingPoint")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let ebits = match seq.next_element::<u32>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        0,
                        &"tuple variant Sort::FloatingPoint with 2 elements",
                    ));
                }
            };
            let sbits = match seq.next_element::<u32>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        1,
                        &"tuple variant Sort::FloatingPoint with 2 elements",
                    ));
                }
            };
            Ok(Sort::FloatingPoint(ebits, sbits))
        }
    }

    struct SortFiniteDomainVisitor;

    impl<'de> Visitor<'de> for SortFiniteDomainVisitor {
        type Value = Sort;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("tuple variant Sort::FiniteDomain")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let name = match seq.next_element::<String>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        0,
                        &"tuple variant Sort::FiniteDomain with 2 elements",
                    ));
                }
            };
            let size = match seq.next_element::<u64>()? {
                Some(value) => value,
                None => {
                    return Err(DeError::invalid_length(
                        1,
                        &"tuple variant Sort::FiniteDomain with 2 elements",
                    ));
                }
            };
            Ok(Sort::FiniteDomain(name, size))
        }
    }

    struct SortVisitor;

    impl<'de> Visitor<'de> for SortVisitor {
        type Value = Sort;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("enum Sort")
        }

        fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
        where
            A: EnumAccess<'de>,
        {
            match data.variant()? {
                (SortVariant::Bool, variant) => {
                    variant.unit_variant()?;
                    Ok(Sort::Bool)
                }
                (SortVariant::Int, variant) => {
                    variant.unit_variant()?;
                    Ok(Sort::Int)
                }
                (SortVariant::Real, variant) => {
                    variant.unit_variant()?;
                    Ok(Sort::Real)
                }
                (SortVariant::BitVec, variant) => {
                    variant.newtype_variant::<BitVecSort>().map(Sort::BitVec)
                }
                (SortVariant::Array, variant) => {
                    variant.newtype_variant::<Box<ArraySort>>().map(Sort::Array)
                }
                (SortVariant::String, variant) => {
                    variant.unit_variant()?;
                    Ok(Sort::String)
                }
                (SortVariant::RegLan, variant) => {
                    variant.unit_variant()?;
                    Ok(Sort::RegLan)
                }
                (SortVariant::FloatingPoint, variant) => {
                    variant.tuple_variant(2, SortFloatingPointVisitor)
                }
                (SortVariant::Uninterpreted, variant) => {
                    variant.newtype_variant::<String>().map(Sort::Uninterpreted)
                }
                (SortVariant::Datatype, variant) => variant
                    .newtype_variant::<DatatypeSort>()
                    .map(Sort::Datatype),
                (SortVariant::Seq, variant) => {
                    variant.newtype_variant::<Box<Sort>>().map(Sort::Seq)
                }
                (SortVariant::Char, variant) => {
                    variant.unit_variant()?;
                    Ok(Sort::Char)
                }
                (SortVariant::FiniteDomain, variant) => {
                    variant.tuple_variant(2, SortFiniteDomainVisitor)
                }
                (SortVariant::TypeVar, variant) => {
                    variant.newtype_variant::<String>().map(Sort::TypeVar)
                }
            }
        }
    }

    impl<'de> Deserialize<'de> for Sort {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_enum("Sort", SORT_VARIANTS, SortVisitor)
        }
    }
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
        // Explicit push loop (not `collect`): each push is a locally bounded
        // growth step, where a bulk collect from an opaque iterator is an
        // allocation the verifier cannot bound.
        let mut collected: Vec<DatatypeField> = Vec::new();
        for (field_name, sort) in fields {
            collected.push(DatatypeField {
                name: field_name.into(),
                sort,
            });
        }
        let fields = collected;

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
        // Explicit push loop (not `collect`): see `struct_type`.
        let mut constructors: Vec<DatatypeConstructor> = Vec::new();
        for variant in variants {
            constructors.push(DatatypeConstructor::unit(variant));
        }
        Self::Datatype(DatatypeSort {
            name: name.into(),
            constructors,
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
