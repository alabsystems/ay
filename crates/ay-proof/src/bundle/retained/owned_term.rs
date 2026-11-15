// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed legacy term owners assembled without generic owning serde decoding.
//!
//! These functions decode representation only: IDs may be forward/outside the
//! eventual table, widths may be zero, and quantifier bindings are not checked
//! here. Snapshot preflight must still authenticate the complete term table.
//! Input admission and final owner settlement belong to the enclosing reader.
//! Every leaf shares its original control, including the explicitly prepaid
//! but infallible Box/Arc/bigint leaves documented in the sibling decoders.

use super::owned_values::{
    bool_value, owned_string, structure, tagged, tuple, u32_value, vector, RawSlice, UnknownFields,
};
use super::{owned_bignum, owned_sort, owned_symbol, Control, TransportError};
use ay_core::{Constant, RationalWrapper, Sort, TermData, TermId};

const TERMS: &[&str] = &[
    "Const", "Var", "App", "Let", "Not", "Ite", "Forall", "Exists",
];
const CONSTANTS: &[&str] = &["Bool", "Int", "Rational", "BitVec", "String", "FiniteField"];

pub(super) fn read(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<TermData, TransportError> {
    control.charge(1, 0)?;
    let tag = tagged(raw, TERMS, control)?;
    let raw = required(tag.payload, control)?;
    let term = match tag.index {
        0 => TermData::Const(constant(raw, control)?),
        1 => {
            let [name, id] = tuple(raw, control)?;
            TermData::Var(
                owned_string(required(name, control)?, control)?,
                u32_value(required(id, control)?, control)?,
            )
        }
        2 => {
            let [symbol, arguments] = tuple(raw, control)?;
            TermData::App(
                owned_symbol::read(required(symbol, control)?, control)?,
                ids(required(arguments, control)?, control)?,
            )
        }
        3 => {
            let [bindings, body] = tuple(raw, control)?;
            let bindings = required(bindings, control)?;
            let bindings = vector(bindings, bindings.as_str().len(), control, let_binding)?;
            TermData::Let(bindings, term_id(required(body, control)?, control)?)
        }
        4 => TermData::Not(term_id(raw, control)?),
        5 => {
            let [condition, yes, no] = tuple(raw, control)?;
            TermData::Ite(
                term_id(required(condition, control)?, control)?,
                term_id(required(yes, control)?, control)?,
                term_id(required(no, control)?, control)?,
            )
        }
        6 | 7 => quantified(tag.index, raw, control)?,
        _ => return control.fail(TransportError::InvalidShape("unsupported TermData variant")),
    };
    control.charge(0, 0)?;
    Ok(term)
}

pub(super) fn constant(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<Constant, TransportError> {
    control.charge(1, 0)?;
    let tag = tagged(raw, CONSTANTS, control)?;
    let raw = required(tag.payload, control)?;
    let value = match tag.index {
        0 => Constant::Bool(bool_value(raw, control)?),
        1 => Constant::Int(owned_bignum::bigint(raw, control)?),
        2 => Constant::Rational(RationalWrapper(owned_bignum::big_rational(raw, control)?)),
        3 => {
            let [value, width] =
                structure(raw, &["value", "width"], UnknownFields::Reject, control)?.values;
            Constant::BitVec {
                value: owned_bignum::bigint(required(value, control)?, control)?,
                width: u32_value(required(width, control)?, control)?,
            }
        }
        4 => Constant::String(owned_string(raw, control)?),
        5 => {
            let [value, field] =
                structure(raw, &["value", "field"], UnknownFields::Reject, control)?.values;
            let value = u32_value(required(value, control)?, control)?;
            let p = u32_value(required(field, control)?, control)?;
            let Some(field) = ay_core::FiniteFieldSort::new(p) else {
                return control.fail(TransportError::InvalidShape(
                    "unsupported finite-field modulus",
                ));
            };
            Constant::FiniteField { value, field }
        }
        _ => return control.fail(TransportError::InvalidShape("unsupported Constant variant")),
    };
    control.charge(0, 0)?;
    Ok(value)
}

pub(super) fn term_id(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<TermId, TransportError> {
    u32_value(raw, control).map(TermId)
}

pub(super) fn ids(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<Vec<TermId>, TransportError> {
    vector(raw, raw.as_str().len(), control, term_id)
}

fn let_binding(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<(String, TermId), TransportError> {
    let [name, term] = tuple(raw, control)?;
    Ok((
        owned_string(required(name, control)?, control)?,
        term_id(required(term, control)?, control)?,
    ))
}

pub(super) fn binder(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<(String, Sort), TransportError> {
    let [name, sort] = tuple(raw, control)?;
    Ok((
        owned_string(required(name, control)?, control)?,
        owned_sort::read(required(sort, control)?, control)?,
    ))
}

fn quantified(
    variant: usize,
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<TermData, TransportError> {
    let [binders, body, triggers] = tuple(raw, control)?;
    let binders = required(binders, control)?;
    let binders = vector(binders, binders.as_str().len(), control, binder)?;
    let body = term_id(required(body, control)?, control)?;
    let triggers = required(triggers, control)?;
    let triggers = vector(triggers, triggers.as_str().len(), control, ids)?;
    match variant {
        6 => Ok(TermData::Forall(binders, body, triggers)),
        7 => Ok(TermData::Exists(binders, body, triggers)),
        _ => control.fail(TransportError::InvalidShape(
            "unsupported quantifier variant",
        )),
    }
}

fn required<'a>(
    field: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    field
        .ok_or(TransportError::InvalidShape(
            "missing required term payload",
        ))
        .or_else(|error| control.fail(error))
}

#[cfg(test)]
mod tests;
