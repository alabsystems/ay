// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed arithmetic annotation ownership under the caller's existing control.
//!
//! This preserves legacy accepted values and re-encoded bytes, not streaming
//! fault order or diagnostic wording. Shape scans precede typed field decoding.
//! Coefficients remain raw Rational64 pairs; no reduction, sign correction or
//! arithmetic is performed. Negative coefficients and nonpositive divisors
//! remain untrusted transport values until the proof checker validates them.
//! Input admission and returned-owner settlement belong to the caller.

use super::owned_values::{i64_value, null, structure, tagged, vector, RawSlice, UnknownFields};
use super::{owned_bignum, Control, TransportError};
use ay_core::{CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation};

pub(super) fn farkas(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<FarkasAnnotation, TransportError> {
    control.charge(1, 0)?;
    let [coefficients] = structure(raw, &["coefficients"], UnknownFields::Reject, control)?.values;
    let coefficients = required(coefficients, control)?;
    let coefficients = vector(
        coefficients,
        coefficients.as_str().len(),
        control,
        owned_bignum::rational64,
    )?;
    control.charge(0, 0)?;
    Ok(FarkasAnnotation { coefficients })
}

pub(super) fn cutting_plane(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<CuttingPlaneAnnotation, TransportError> {
    control.charge(1, 0)?;
    let [combination, divisor] =
        structure(raw, &["farkas", "divisor"], UnknownFields::Reject, control)?.values;
    let farkas = farkas(required(combination, control)?, control)?;
    let divisor = i64_value(required(divisor, control)?, control)?;
    control.charge(0, 0)?;
    Ok(CuttingPlaneAnnotation { farkas, divisor })
}

pub(super) fn lia(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<LiaAnnotation, TransportError> {
    control.charge(1, 0)?;
    let tag = tagged(
        raw,
        &[
            "BoundsGap",
            "Divisibility",
            "CuttingPlane",
            "LinearIdentity",
        ],
        control,
    )?;
    let value = match tag.index {
        0 | 1 | 3 => {
            if let Some(payload) = tag.payload {
                null(payload, control)?;
            }
            match tag.index {
                0 => LiaAnnotation::BoundsGap,
                1 => LiaAnnotation::Divisibility,
                _ => LiaAnnotation::LinearIdentity,
            }
        }
        2 => LiaAnnotation::CuttingPlane(cutting_plane(required(tag.payload, control)?, control)?),
        _ => return control.fail(TransportError::InvalidShape("unsupported LIA annotation")),
    };
    control.charge(0, 0)?;
    Ok(value)
}

fn required<'a>(
    value: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    value
        .ok_or(TransportError::InvalidShape(
            "missing arithmetic annotation field",
        ))
        .or_else(|error| control.fail(error))
}

#[cfg(test)]
mod tests;
