// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SOS wire bounds and canonical integers, not theorem or shape validation.
//!
//! The caller admits the raw input and settles returned owners. Every pass
//! uses its original control. Canonical integer admission deliberately parses
//! at most 32 limbs into temporary scratch, drops that scratch, then reuses
//! the audited bigint constructor with a second charged parse. No reservation
//! is refunded. This avoids widening the ordinary bigint decoder or duplicating
//! its pinned, infallible allocation boundary. All certificate semantics stay
//! in the existing preflight/checker: e.g. negative/zero denominators, empty or
//! rectangular matrices and out-of-clause positions are still transport data.

use super::owned_values::{
    i8_value, structure, tagged, tuple, u32_value, vector, RawSlice, UnknownFields,
};
use super::{owned_bignum, Control, TransportError};
use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, TermId};
use num_bigint::BigInt;

pub(super) fn clause(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<Vec<TermId>, TransportError> {
    vector(raw, NraSosCertificate::MAX_CLAUSE_SLOTS, control, term_id)
}

pub(super) fn certificate(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<NraSosCertificate, TransportError> {
    let [basis_raw, gram_raw, terms_raw, rhs] = structure(
        raw,
        &["basis", "gram", "terms", "rhs"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    let basis = basis(required(basis_raw, control)?, control)?;
    let gram = gram(required(gram_raw, control)?, control)?;
    let terms = terms(required(terms_raw, control)?, control)?;
    let rhs = rational(required(rhs, control)?, control)?;
    control.charge(0, 0)?;
    Ok(NraSosCertificate {
        basis,
        gram,
        terms,
        rhs,
    })
}

fn term_id(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<TermId, TransportError> {
    u32_value(raw, control).map(TermId)
}

fn basis(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<Vec<Vec<TermId>>, TransportError> {
    vector(
        raw,
        NraSosCertificate::MAX_BASIS,
        control,
        |row, control| vector(row, 2, control, term_id),
    )
}

fn gram(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<Vec<Vec<NraSosRational>>, TransportError> {
    vector(
        raw,
        NraSosCertificate::MAX_BASIS,
        control,
        |row, control| vector(row, NraSosCertificate::MAX_BASIS, control, rational),
    )
}

fn terms(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<Vec<NraSosTerm>, TransportError> {
    vector(raw, NraSosCertificate::MAX_TERMS, control, term)
}

fn term(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<NraSosTerm, TransportError> {
    let [origin_raw, multiplier] = structure(
        raw,
        &["origin", "multiplier"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    let origin = origin(required(origin_raw, control)?, control)?;
    let multiplier = rational(required(multiplier, control)?, control)?;
    control.charge(0, 0)?;
    Ok(NraSosTerm { origin, multiplier })
}

fn origin(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<NraSosOrigin, TransportError> {
    let tag = tagged(raw, &["ClauseLiteral", "Product"], control)?;
    let payload = required(tag.payload, control)?;
    let value = match tag.index {
        0 => {
            let [position] =
                structure(payload, &["position"], UnknownFields::Reject, control)?.values;
            NraSosOrigin::ClauseLiteral {
                position: u32_value(required(position, control)?, control)?,
            }
        }
        1 => {
            let [left, right] =
                structure(payload, &["left", "right"], UnknownFields::Reject, control)?.values;
            NraSosOrigin::Product {
                left: u32_value(required(left, control)?, control)?,
                right: u32_value(required(right, control)?, control)?,
            }
        }
        _ => return control.fail(TransportError::InvalidShape("unsupported SOS origin")),
    };
    control.charge(0, 0)?;
    Ok(value)
}

fn rational(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<NraSosRational, TransportError> {
    let [numerator, denominator] = structure(
        raw,
        &["numerator", "denominator"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    let numerator = integer(required(numerator, control)?, control)?;
    let denominator = integer(required(denominator, control)?, control)?;
    // Unlike BigRational's wire codec, this struct permits a zero denominator.
    // Its positive-sign and normalization obligations belong to the checker.
    control.charge(0, 0)?;
    Ok(NraSosRational {
        numerator,
        denominator,
    })
}

fn integer(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<BigInt, TransportError> {
    let [sign, limbs] = tuple::<2>(raw, control)?;
    let sign = i8_value(required(sign, control)?, control)?;
    let limbs = vector(required(limbs, control)?, 32, control, u32_value)?;
    control.charge(1, 0)?;
    // core::proof::nra_sos::wire::integer first parses its bounded tuple,
    // then enforces exactly these sign and canonical-limb conditions.
    if !matches!(sign, -1..=1) {
        return control.fail(TransportError::InvalidShape("invalid SOS integer sign"));
    }
    if limbs.last() == Some(&0) || ((sign == 0) != limbs.is_empty()) {
        return control.fail(TransportError::InvalidShape(
            "noncanonical SOS integer limbs",
        ));
    }
    drop(limbs);
    control.charge(0, 0)?;
    // At most 32 words, reparsed and re-admitted on the SAME control. The
    // earlier scratch reservation is consumed even though it was just dropped.
    owned_bignum::bigint(raw, control)
}

fn required<'a>(
    field: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    field
        .ok_or(TransportError::InvalidShape("missing SOS field"))
        .or_else(|error| control.fail(error))
}

#[cfg(test)]
mod tests;
