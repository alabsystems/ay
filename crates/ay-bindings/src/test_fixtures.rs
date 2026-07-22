// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Test fixtures for common Sort patterns.
//!
//! This module provides helper functions for constructing common Sort types
//! used across test suites. Reduces duplication and ensures consistency.
//!
//! # Usage
//!
//! ```rust
//! use ay_bindings::test_fixtures::{point_sort, option_i32_sort};
//!
//! let point = point_sort();
//! let opt = option_i32_sort();
//! ```

use crate::sort::Sort;

/// Creates a Point struct sort with x, y fields (both i32/bv32).
///
/// SMT: `(declare-datatype Point ((Point_mk (x (_ BitVec 32)) (y (_ BitVec 32)))))`
pub fn point_sort() -> Sort {
    Sort::struct_type("Point", [("x", Sort::bv32()), ("y", Sort::bv32())])
}

/// Creates an Option<T> enum sort with None and Some(value: T) variants.
///
/// SMT: `(declare-datatype Option ((None) (Some (value T))))`
pub fn option_sort(value_sort: Sort) -> Sort {
    Sort::enum_type(
        "Option",
        vec![("None", vec![]), ("Some", vec![("value", value_sort)])],
    )
}

/// Creates an Option<i32> enum sort - common case.
pub fn option_i32_sort() -> Sort {
    option_sort(Sort::bv32())
}

/// Creates an OptionLike struct sort with is_some (bool) and value (T) fields.
///
/// This models optional values as structs rather than enums, useful for
/// testing struct field access patterns.
///
/// SMT: `(declare-datatype OptionLike ((OptionLike_mk (is_some Bool) (value T))))`
pub fn option_like_sort(value_sort: Sort) -> Sort {
    Sort::struct_type(
        "OptionLike",
        [("is_some", Sort::bool()), ("value", value_sort)],
    )
}

/// Creates an OptionLike<i32> struct sort - common case.
pub fn option_like_i32_sort() -> Sort {
    option_like_sort(Sort::bv32())
}

/// Creates a Tuple2 struct sort with fld_0 and fld_1 fields.
pub fn tuple2_sort(fld0_sort: Sort, fld1_sort: Sort) -> Sort {
    let name = format!(
        "Tuple_{}_{}",
        sort_suffix(&fld0_sort),
        sort_suffix(&fld1_sort)
    );
    Sort::struct_type(&name, [("fld_0", fld0_sort), ("fld_1", fld1_sort)])
}

/// Returns a short suffix for sort names.
fn sort_suffix(sort: &Sort) -> String {
    if let Some(w) = sort.bitvec_width() {
        format!("bv{w}")
    } else if sort.is_bool() {
        "bool".into()
    } else if sort.is_int() {
        "int".into()
    } else if sort.is_real() {
        "real".into()
    } else if sort.is_array() {
        "arr".into()
    } else if sort.is_datatype() {
        sort.datatype_name().unwrap_or("dt").to_string()
    } else {
        "unknown".into()
    }
}

#[cfg(test)]
#[path = "test_fixtures_tests.rs"]
mod tests;
