// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed rule payloads plus a closed, allocation-controlled unit-enum bridge.
//!
//! Only payload-bearing tags are listed here. The unit bridge uses each
//! existing serde implementation's static registry and refuses nonunit
//! requests, so a newly added owning variant cannot allocate behind our back.
//! All scans, temporary tag strings and payload owners share the caller's
//! original control. Transport decoding does not authorize any proof rule.

use super::owned_values::{
    bool_value, owned_string, structure, tagged, u32_value, vector, RawSlice, Tag, UnknownFields,
};
use super::{owned_units, Control, TransportError};
use ay_core::{AletheRule, TheoryLemmaKind};

const ALETHE_PAYLOADS: &[&str; 3] = &["AndPos", "OrPos", "Custom"];
const THEORY_PAYLOADS: &[&str; 6] = &[
    "BvBitBlastGate",
    "ArraySelectStore",
    "FpToBv",
    "FpClassification",
    "FiniteFieldLinear",
    "FiniteFieldLinearWide",
];

pub(super) fn alethe(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<AletheRule, TransportError> {
    let Some(tag) = payload_tag(raw, ALETHE_PAYLOADS, control)? else {
        return owned_units::alethe_unit(raw, control);
    };
    let payload = required(tag.payload, control)?;
    let rule = match tag.index {
        0 => AletheRule::AndPos(u32_value(payload, control)?),
        1 => AletheRule::OrPos(u32_value(payload, control)?),
        2 => AletheRule::Custom(owned_string(payload, control)?),
        _ => return control.fail(TransportError::InvalidShape("unsupported rule payload")),
    };
    control.charge(0, 0)?;
    Ok(rule)
}

pub(super) fn theory(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<TheoryLemmaKind, TransportError> {
    let Some(tag) = payload_tag(raw, THEORY_PAYLOADS, control)? else {
        return owned_units::theory_unit(raw, control);
    };
    let payload = required(tag.payload, control)?;
    let kind = match tag.index {
        0 => {
            let [gate, width] = structure(
                payload,
                &["gate_type", "width"],
                UnknownFields::Reject,
                control,
            )?
            .values;
            TheoryLemmaKind::BvBitBlastGate {
                gate_type: owned_units::bv_gate(required(gate, control)?, control)?,
                width: u32_value(required(width, control)?, control)?,
            }
        }
        1 => {
            let [index_eq] =
                structure(payload, &["index_eq"], UnknownFields::Reject, control)?.values;
            TheoryLemmaKind::ArraySelectStore {
                index_eq: bool_value(required(index_eq, control)?, control)?,
            }
        }
        2 | 3 => {
            let [operation] =
                structure(payload, &["operation"], UnknownFields::Reject, control)?.values;
            let operation = owned_units::fp_operation(required(operation, control)?, control)?;
            if tag.index == 2 {
                TheoryLemmaKind::FpToBv { operation }
            } else {
                TheoryLemmaKind::FpClassification { operation }
            }
        }
        4 => {
            let entries = vector(
                payload,
                TheoryLemmaKind::MAX_FINITE_FIELD_LINEAR_ROWS,
                control,
                |entry, control| {
                    u8::try_from(u32_value(entry, control)?)
                        .map_err(|_| TransportError::InvalidShape("expected field multiplier byte"))
                },
            )?;
            let Ok(entries) = entries.try_into() else {
                return control.fail(TransportError::InvalidShape(
                    "expected eight field multipliers",
                ));
            };
            TheoryLemmaKind::FiniteFieldLinear(entries)
        }
        5 => {
            let entries = vector(
                payload,
                TheoryLemmaKind::MAX_FINITE_FIELD_LINEAR_ROWS,
                control,
                u32_value,
            )?;
            let Ok(entries) = entries.try_into() else {
                return control.fail(TransportError::InvalidShape(
                    "expected eight full-width field multipliers",
                ));
            };
            TheoryLemmaKind::FiniteFieldLinearWide(entries)
        }
        _ => return control.fail(TransportError::InvalidShape("unsupported theory payload")),
    };
    control.charge(0, 0)?;
    Ok(kind)
}

/// Classify before invoking a decoder; never catch a poisoned unit decode and
/// retry a payload route. Ignore is ONLY a classification mode: the selected
/// tagged decoder subsequently enforces a single known entry. Unknown keys,
/// duplicate/multiple entries and nonnull unit payloads cannot be accepted by
/// this prepass. Repeated scans/temporary names are charged without refunds.
fn payload_tag<'a, const N: usize>(
    raw: RawSlice<'a>,
    names: &[&str; N],
    control: &mut Control<'_>,
) -> Result<Option<Tag<'a>>, TransportError> {
    control.charge(1, 0)?;
    if !raw.as_str().starts_with('{') {
        return Ok(None);
    }
    let fields = structure(raw, names, UnknownFields::Ignore, control)?;
    control.charge(N, 0)?;
    if fields.values.iter().any(Option::is_some) {
        tagged(raw, names, control).map(Some)
    } else {
        Ok(None)
    }
}

fn required<'a>(
    value: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    value
        .ok_or(TransportError::InvalidShape("missing rule payload"))
        .or_else(|error| control.fail(error))
}

#[cfg(test)]
mod tests;
