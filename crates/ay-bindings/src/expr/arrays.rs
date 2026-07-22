// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Array operations for AY expressions.

use crate::memory::POINTER_WIDTH;
use crate::sort::{ArraySort, Sort};
use std::sync::Arc;

use super::{Expr, ExprValue};

fn datatype_field_sort(sort: &Sort, field_name: &str) -> Option<Sort> {
    let dt = sort.datatype_sort()?;
    dt.constructors.iter().find_map(|constructor| {
        constructor
            .fields
            .iter()
            .find(|field| field.name == field_name)
            .map(|field| field.sort.clone())
    })
}

fn zero_expr_for_sort(sort: &Sort) -> Option<Expr> {
    if sort.is_bitvec() {
        Some(Expr::bitvec_const(0, sort.bitvec_width()?))
    } else if sort.is_int() {
        Some(Expr::int_const(0))
    } else {
        None
    }
}

/// Coerce a value to match an array's element sort (Part of #1341, #1459).
///
/// Handles: BitVec <-> Vec/String datatype, Int <-> BitVec mismatches.
/// Returns the value unchanged if no coercion applies.
fn coerce_store_value(value: Expr, arr_sort: &ArraySort) -> Expr {
    let value_dt_name = value.sort.datatype_name().map(str::to_string);
    let elem_dt_name = arr_sort.element_sort.datatype_name();
    let should_coerce_bv_to_dt = elem_dt_name.is_some_and(|dt| dt == "Vec" || dt == "String")
        && value.sort.is_bitvec()
        && value.sort.bitvec_width() == Some(POINTER_WIDTH);

    let mut coerced = if should_coerce_bv_to_dt {
        let dt_name = elem_dt_name.expect("checked above");
        let ptr_sort = datatype_field_sort(&arr_sort.element_sort, "fld_ptr");
        let len_sort = datatype_field_sort(&arr_sort.element_sort, "fld_len");
        let cap_sort = datatype_field_sort(&arr_sort.element_sort, "fld_cap");
        if ptr_sort.as_ref() == Some(&value.sort) {
            if let (Some(len_sort), Some(cap_sort)) = (len_sort, cap_sort) {
                if let (Some(len), Some(cap)) =
                    (zero_expr_for_sort(&len_sort), zero_expr_for_sort(&cap_sort))
                {
                    let cons_name = format!("{dt_name}_mk");
                    Expr::datatype_constructor(
                        dt_name,
                        cons_name,
                        vec![value, len, cap],
                        arr_sort.element_sort.clone(),
                    )
                } else {
                    value
                }
            } else {
                value
            }
        } else {
            value
        }
    } else {
        let should_coerce_dt_to_bv = arr_sort.element_sort.is_bitvec()
            && arr_sort.element_sort.bitvec_width() == Some(POINTER_WIDTH)
            && value_dt_name
                .as_deref()
                .is_some_and(|dt| dt == "Vec" || dt == "String");
        if should_coerce_dt_to_bv {
            let dt_name = value_dt_name.as_deref().expect("checked above");
            let ptr_sort = datatype_field_sort(&value.sort, "fld_ptr");
            if ptr_sort.as_ref() == Some(&arr_sort.element_sort) {
                value.field_select(dt_name, "fld_ptr", arr_sort.element_sort.clone())
            } else {
                value
            }
        } else {
            value
        }
    };

    // Defense-in-depth: Coerce Int/BitVec mismatches (Part of #1459)
    if arr_sort.element_sort.is_int() && coerced.sort.is_bitvec() {
        coerced = coerced.bv2int();
    } else if arr_sort.element_sort.is_bitvec() && coerced.sort.is_int() {
        if let Some(width) = arr_sort.element_sort.bitvec_width() {
            coerced = coerced.int2bv(width);
        }
    }
    coerced
}

impl Expr {
    // ===== Array Operations =====

    /// Array select (read).
    ///
    /// # REQUIRES
    /// - `self` is Array sort
    /// - `index` sort matches array index sort
    ///
    /// # ENSURES
    /// - Result sort matches array element sort
    #[cfg_attr(kani, kani::requires(self.sort.is_array()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn select(self, index: Self) -> Self {
        self.try_select(index)
            .expect("select requires Array sort with matching index sort")
    }

    /// Array store (write).
    ///
    /// # REQUIRES
    /// - `self` is Array sort
    /// - `index` sort matches array index sort
    /// - `value` sort matches array element sort
    ///
    /// # ENSURES
    /// - Result sort matches `self` array sort
    #[cfg_attr(kani, kani::requires(self.sort.is_array()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_array()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn store(self, index: Self, value: Self) -> Self {
        self.try_store(index, value)
            .expect("store requires Array sort with matching index and element sorts")
    }

    /// Create a constant array.
    ///
    /// # REQUIRES
    /// - None (value can be any sort)
    ///
    /// # ENSURES
    /// - Result sort is Array(index_sort, value.sort())
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_array()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn const_array(index_sort: Sort, value: Self) -> Self {
        Self::try_const_array(index_sort, value).expect("const_array sort check failed")
    }

    // ===== Fallible Array Operations =====

    /// Fallible version of [`Expr::const_array`].
    ///
    /// `const_array` cannot currently fail on sort constraints (any index sort
    /// and value sort are accepted), but this method exists for API
    /// consistency with `try_select` / `try_store`.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_const_array(index_sort: Sort, value: Self) -> Result<Self, crate::SortError> {
        let element_sort = value.sort.clone();
        let array_sort = Sort::array(index_sort.clone(), element_sort);
        Ok(Self {
            sort: array_sort,
            value: Arc::new(ExprValue::ConstArray { index_sort, value }),
        })
    }

    /// Fallible version of [`Expr::select`].
    ///
    /// Returns `SortError` if `self` is not an Array sort or if the index
    /// sort does not match the array's index sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_select(self, index: Self) -> Result<Self, crate::SortError> {
        let arr_sort = self
            .sort
            .array_sort()
            .ok_or_else(|| crate::SortError::unary("select", "Array", &self.sort))?;
        if index.sort != arr_sort.index_sort {
            return Err(crate::SortError::binary(
                "select",
                "matching index sort",
                &index.sort,
                &arr_sort.index_sort,
            ));
        }
        let elem_sort = arr_sort.element_sort.clone();
        Ok(Self {
            sort: elem_sort,
            value: Arc::new(ExprValue::Select { array: self, index }),
        })
    }

    /// Fallible version of [`Expr::store`].
    ///
    /// Returns `SortError` if `self` is not an Array sort, if the index sort
    /// does not match, or if the value sort does not match the array's element
    /// sort (after auto-coercion).
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_store(self, index: Self, value: Self) -> Result<Self, crate::SortError> {
        let arr_sort = self
            .sort
            .array_sort()
            .ok_or_else(|| crate::SortError::unary("store", "Array", &self.sort))?;
        if index.sort != arr_sort.index_sort {
            return Err(crate::SortError::binary(
                "store",
                "matching index sort",
                &index.sort,
                &arr_sort.index_sort,
            ));
        }
        let coerced_value = coerce_store_value(value, arr_sort);
        if coerced_value.sort != arr_sort.element_sort {
            return Err(crate::SortError::binary(
                "store",
                "matching element sort",
                &coerced_value.sort,
                &arr_sort.element_sort,
            ));
        }
        let result_sort = self.sort.clone();
        Ok(Self {
            sort: result_sort,
            value: Arc::new(ExprValue::Store {
                array: self,
                index,
                value: coerced_value,
            }),
        })
    }
}
