// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed legacy Sort decoding under the existing transport control.
//!
//! Matches ay-core's sort_serde JSON representation, including positional
//! helper structs and externally tagged unit objects. This is transport only:
//! zero widths, empty names and duplicate datatype members are not validated
//! here. The complete snapshot preflight owns those semantic checks.
//!
//! Strings and vectors use fallible capacity-checked admission. Recursive
//! boxes use pre-admitted fixed-size Box::new calls: stable safe Rust provides
//! no fallible constructor for these current public owner types. These leaves
//! remain infallible allocator calls with pre/post polling, not recoverable
//! process OOM or allocator-exact RSS guarantees. No unsafe or toolchain feature
//! is introduced. The caller admits input/depth and settles returned owners.

use super::owned_values::{
    self, null, owned_string, structure, tagged, tuple, u32_value, u64_value, RawSlice,
    UnknownFields,
};
use super::{lexical, Control, TransportError};
use ay_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use std::mem::size_of;

const VARIANTS: &[&str] = &[
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
    "Complex",
    "FiniteField",
];

pub(super) fn read(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<Sort, TransportError> {
    read_at(raw, 0, control)
}

fn read_at(
    raw: RawSlice<'_>,
    depth: usize,
    control: &mut Control<'_>,
) -> Result<Sort, TransportError> {
    control.charge(1, 0)?;
    // The already-admitted complete input has the stricter total JSON-depth
    // cap. Also bound this decoder's recursion if used independently.
    control.cap("owning sort depth", depth, lexical::OUTER_DEPTH)?;
    let tag = tagged(raw, VARIANTS, control)?;
    let unit = match tag.index {
        0 => Some(Sort::Bool),
        1 => Some(Sort::Int),
        2 => Some(Sort::Real),
        5 => Some(Sort::String),
        6 => Some(Sort::RegLan),
        11 => Some(Sort::Char),
        14 => Some(Sort::Complex),
        _ => None,
    };
    let result = match unit {
        Some(unit) => {
            if let Some(payload) = tag.payload {
                null(payload, control)?;
            }
            unit
        }
        None => payload(tag.index, required(tag.payload, control)?, depth, control)?,
    };
    control.charge(0, 0)?;
    Ok(result)
}

fn payload(
    index: usize,
    raw: RawSlice<'_>,
    depth: usize,
    control: &mut Control<'_>,
) -> Result<Sort, TransportError> {
    match index {
        15 => {
            let p = u32_value(raw, control)?;
            match ay_core::FiniteFieldSort::new(p) {
                Some(f) => Ok(Sort::FiniteField(f)),
                None => control.fail(TransportError::InvalidShape(
                    "unsupported finite-field modulus",
                )),
            }
        }
        3 => {
            let [width] = structure(raw, &["width"], UnknownFields::Reject, control)?.values;
            Ok(Sort::BitVec(BitVecSort {
                width: u32_value(required(width, control)?, control)?,
            }))
        }
        4 => array(raw, depth, control),
        7 => {
            let [exponent, significand] = tuple(raw, control)?;
            Ok(Sort::FloatingPoint(
                u32_value(required(exponent, control)?, control)?,
                u32_value(required(significand, control)?, control)?,
            ))
        }
        8 => owned_string(raw, control).map(Sort::Uninterpreted),
        9 => datatype(raw, depth, control).map(Sort::Datatype),
        10 => {
            let next_depth = control.add(depth, 1)?;
            let element = read_at(raw, next_depth, control)?;
            boxed(element, control).map(Sort::Seq)
        }
        12 => {
            let [name, cardinality] = tuple(raw, control)?;
            Ok(Sort::FiniteDomain(
                owned_string(required(name, control)?, control)?,
                u64_value(required(cardinality, control)?, control)?,
            ))
        }
        13 => owned_string(raw, control).map(Sort::TypeVar),
        _ => control.fail(TransportError::InvalidShape("unsupported Sort variant")),
    }
}

fn array(
    raw: RawSlice<'_>,
    depth: usize,
    control: &mut Control<'_>,
) -> Result<Sort, TransportError> {
    let [index, element] = structure(
        raw,
        &["index_sort", "element_sort"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    let next_depth = control.add(depth, 1)?;
    let index_sort = read_at(required(index, control)?, next_depth, control)?;
    let element_sort = read_at(required(element, control)?, next_depth, control)?;
    boxed(
        ArraySort {
            index_sort,
            element_sort,
        },
        control,
    )
    .map(Sort::Array)
}

fn datatype(
    raw: RawSlice<'_>,
    depth: usize,
    control: &mut Control<'_>,
) -> Result<DatatypeSort, TransportError> {
    let [name, constructors] = structure(
        raw,
        &["name", "constructors"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    let name = owned_string(required(name, control)?, control)?;
    let constructors = required(constructors, control)?;
    // The admitted JSON length bounds element count; the vector helper still
    // counts every element and admits actual slot capacity before decoding it.
    let constructors = owned_values::vector(
        constructors,
        constructors.as_str().len(),
        control,
        |raw, control| constructor(raw, depth, control),
    )?;
    Ok(DatatypeSort { name, constructors })
}

fn constructor(
    raw: RawSlice<'_>,
    depth: usize,
    control: &mut Control<'_>,
) -> Result<DatatypeConstructor, TransportError> {
    let [name, fields] =
        structure(raw, &["name", "fields"], UnknownFields::Reject, control)?.values;
    let name = owned_string(required(name, control)?, control)?;
    let fields = required(fields, control)?;
    let fields = owned_values::vector(fields, fields.as_str().len(), control, |raw, control| {
        field(raw, depth, control)
    })?;
    Ok(DatatypeConstructor { name, fields })
}

fn field(
    raw: RawSlice<'_>,
    depth: usize,
    control: &mut Control<'_>,
) -> Result<DatatypeField, TransportError> {
    let [name, sort] = structure(raw, &["name", "sort"], UnknownFields::Reject, control)?.values;
    let name = owned_string(required(name, control)?, control)?;
    let next_depth = control.add(depth, 1)?;
    let sort = read_at(required(sort, control)?, next_depth, control)?;
    Ok(DatatypeField { name, sort })
}

fn required<'a>(
    field: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    field
        .ok_or(TransportError::InvalidShape("missing required Sort field"))
        .or_else(|error| control.fail(error))
}

fn boxed<T>(value: T, control: &mut Control<'_>) -> Result<Box<T>, TransportError> {
    control.charge(1, size_of::<T>())?;
    let value = Box::new(value);
    control.charge(0, 0)?;
    Ok(value)
}

#[cfg(test)]
mod tests;
