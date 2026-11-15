// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owning v6 transport, not proof or external-problem authentication.
//!
//! The caller supplies the original minimum deadline and a whole-operation
//! constrained Control, and owns its final post-cleanup finish. Envelope/schema
//! admission precedes every typed owner; v5 never falls back to another reader.
//! Typed leaves preserve legacy values without generic owning deserialization.
//! Retained payloads remain untrusted raw bytes for the mandatory inner reader.
//!
//! Inventory-local ceilings additionally constrain its nested operation; every
//! accepted inner charge is forwarded to the SAME outer ledger. A refused
//! local reservation is terminal, not refundable credit. Inner returned-owner
//! bytes describe only inventory ownership and are deliberately not copied to
//! the outer usage. Whole-owner settlement belongs to the enclosing operation.
//! Prepriced opaque Box/Arc/bigint construction, parser scratch and destruction
//! retain their documented limitations: no allocator-exact RSS or hard latency.

use super::outer_view::{NullableTerm, RawFields};
use super::owned_values::{null, owned_string, u32_value, vector, RawSlice};
use super::{
    control, decode, outer_view, owned_snapshot, owned_term, BorrowedField, BundleEncoding,
    BundleLimits, Control, PresenceError, RawValue, RetainedBundle, RetainedField, TransportError,
    WireLimits,
};
use crate::bundle::SerializableProofBundle;
use ay_core::{time::Instant, TermId};

pub(super) fn read(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<RetainedBundle, TransportError> {
    assemble(bytes, limits, wire, deadline, control).or_else(|error| control.fail(error))
}

fn assemble(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<RetainedBundle, TransportError> {
    let view = outer_view::read(bytes, limits.max_json_bytes, control)?;
    if view.encoding != BundleEncoding::RetainedV6 {
        return control.fail(TransportError::Presence(PresenceError::UnsupportedSchema));
    }
    let snapshot = snapshot(&view.fields, control)?;
    let BorrowedField::Present(bytes) = view.fields.retained else {
        return control.fail(TransportError::Presence(
            PresenceError::MissingRetainedField,
        ));
    };
    let retained = inventory(bytes, wire, deadline, control)?;
    let bundle = RetainedBundle::from_parts(snapshot, retained)
        .map_err(TransportError::from)
        .or_else(|error| control.fail(error))?;
    control.charge(0, 0)?;
    Ok(bundle)
}

fn snapshot(
    fields: &RawFields<'_>,
    control: &mut Control<'_>,
) -> Result<SerializableProofBundle, TransportError> {
    Ok(SerializableProofBundle {
        schema: owned_string(RawSlice::from_raw(fields.schema), control)?,
        steps: entries(fields.steps, control, owned_snapshot::step)?,
        term_entries: entries(fields.term_entries, control, owned_snapshot::term_entry)?,
        true_term: optional_term(fields.true_term, control)?,
        false_term: optional_term(fields.false_term, control)?,
        var_counter: u32_value(RawSlice::from_raw(fields.var_counter), control)?,
        obligation_assertions: owned_term::ids(
            RawSlice::from_raw(fields.obligation_assertions),
            control,
        )?,
        datatype_declarations: entries(
            fields.datatype_declarations,
            control,
            owned_snapshot::named_members,
        )?,
        constructor_selectors: entries(
            fields.constructor_selectors,
            control,
            owned_snapshot::named_members,
        )?,
        datatype_member_signatures: entries(
            fields.datatype_member_signatures,
            control,
            owned_snapshot::signature,
        )?,
        declared_function_identities: entries(
            fields.declared_function_identities,
            control,
            owned_string,
        )?,
    })
}

fn entries<'a, T>(
    raw: &'a RawValue,
    control: &mut Control<'_>,
    decode: impl FnMut(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> Result<Vec<T>, TransportError> {
    // Input length is already admitted. Actual element count is censused and
    // its exact slots charged before invoking any explicit typed owner decoder.
    vector(RawSlice::from_raw(raw), raw.get().len(), control, decode)
}

fn optional_term(
    field: NullableTerm<'_>,
    control: &mut Control<'_>,
) -> Result<Option<TermId>, TransportError> {
    control.charge(1, 0)?;
    match field {
        NullableTerm::Absent => Ok(None),
        NullableTerm::Present(raw) if raw.get() == "null" => {
            null(RawSlice::from_raw(raw), control).map(|()| None)
        }
        NullableTerm::Present(raw) => {
            owned_term::term_id(RawSlice::from_raw(raw), control).map(Some)
        }
    }
}

fn inventory(
    bytes: &[u8],
    wire: &WireLimits,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<RetainedField, TransportError> {
    let outcome = control::run(
        deadline,
        &mut |work, bytes| control.charge(work, bytes).is_ok(),
        |inner| {
            inner.constrain(wire.max_work, wire.max_storage_bytes)?;
            decode::read(bytes, wire, inner)
        },
    );
    outcome.result.or_else(|error| control.fail(error))
}

#[cfg(test)]
mod tests;
