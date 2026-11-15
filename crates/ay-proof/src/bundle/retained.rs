// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private controlled retained transport and whole-document wire framing.
//!
//! Payloads are nested raw JSON, owned as bytes, never quoted outer Strings.
//! There is deliberately no unconstrained serde implementation for the owning
//! inventory. `borrow_bundle` admits a complete borrowed envelope; it does NOT
//! decode legacy owners. `decode_bundle` admits typed owners and preserves the
//! actual v6 schema with its mandatory inventory. `encode_bundle` emits the
//! complete document through the same cumulative control, without an unchecked
//! field clone or an unpriced string-escaping scan.
//! Transport alone authenticates no proof. `replay_bundle` additionally runs
//! independent strict snapshot/retained checking, including source-bound
//! conditional prerequisite frames; external problem binding remains separate.
//! `replay_exact_bundle` also checks the complete, nonempty first-use assumption
//! inventory before dropping the document; that is not external query authority.
//!
//! Only the transport's new owners and bounded parser scratch are accounted.
//! Borrowed input and already-owned source buffers must be admitted by the caller.
//! Uncontrolled public legacy serde remains outside these entries. Logical
//! reservations, actual capacity checks and opaque serde intervals are not an
//! allocator-exact RSS or hard cancellation-latency guarantee.
//!
//! WireLimits supplies payload JSON/storage ceilings, an additional per-call
//! work ceiling, and its original deadline. The ceiling grants no aggregate
//! allowance: outer framing/copy and inner codec work are distinct costs that
//! the caller must cumulatively admit. Row/literal/hint limits remain for the
//! required inner codec and source-bound checker, not transport authority.
//! Duplicate claimed step IDs are preserved raw; later binding must reject them.

use crate::bv_blast_solver::retained::wire::WireLimits;
use crate::checker::bv_bitblast::MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF;
use ay_core::time::Instant;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use serde_json::value::RawValue;
use std::{fmt, mem::size_of};

mod control;
mod decode;
mod encode;
#[cfg(test)]
mod exact_inventory;
mod lexical;
mod outer_decode;
mod outer_encode;
mod outer_view;
mod owned_annotation;
mod owned_bignum;
mod owned_rule;
mod owned_snapshot;
mod owned_sort;
mod owned_sos;
mod owned_symbol;
mod owned_term;
mod owned_units;
mod owned_values;
mod owning;
mod serialization;
mod versioned;
mod view;

use crate::checker::bv_bitblast::retained_session::RetainedStepPayload;
use control::Control;
#[cfg(test)]
pub(super) use exact_inventory::ExactInventoryError;
#[cfg(test)]
pub(super) use outer_view::OuterView;
pub(super) use owning::{decode_bundle, decode_bundle_observed};
#[cfg(test)]
pub(super) use owning::{
    replay_bundle, replay_exact_bundle, OwningOutcome, OwningUsage, ReadError,
};
pub(super) use versioned::RetainedBundle;
pub(super) use view::BorrowedField;
type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

pub(super) const SNAPSHOT_SCHEMA: &str = "ay.proofbundle/v5";
pub(super) const RETAINED_SCHEMA: &str = "ay.proofbundle/v6";

/// Private whole-document ceilings, in addition to the retained payload caps.
/// These constrain one transport attempt, not a renewed caller allowance.
pub(super) struct BundleLimits {
    pub(super) max_json_bytes: usize,
    pub(super) max_storage_bytes: usize,
    pub(super) max_work: u64,
    pub(super) deadline: Instant,
}

/// Omission is different from an explicitly supplied empty inventory.
///
/// A future outer DTO borrows `BorrowedField`; controlled ownership conversion
/// preserves omission separately from a present empty inventory. Null refuses.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) enum RetainedField {
    #[default]
    Absent,
    Present(Vec<RetainedStepPayload>),
}

impl RetainedField {
    #[cfg(test)]
    pub(super) fn is_absent(&self) -> bool {
        matches!(self, Self::Absent)
    }
}

/// Only a wire-schema branch selection, never an authenticated proof token.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BundleEncoding {
    SnapshotV5,
    RetainedV6,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(super) enum PresenceError {
    #[error("unsupported proof bundle schema")]
    UnsupportedSchema,
    #[error("legacy v5 bundle must omit the retained field")]
    UnexpectedRetainedField,
    #[error("retained v6 bundle requires the retained field")]
    MissingRetainedField,
}

/// Validate only the exact schema/presence pairing. An empty v6 inventory is
/// well-shaped here, not necessarily sufficient for the enclosing proof.
#[cfg(test)]
pub(super) fn schema_presence(
    schema: &str,
    field: &RetainedField,
) -> Result<BundleEncoding, PresenceError> {
    presence(schema, !field.is_absent())
}

fn presence(schema: &str, present: bool) -> Result<BundleEncoding, PresenceError> {
    match (schema, present) {
        (SNAPSHOT_SCHEMA, false) => Ok(BundleEncoding::SnapshotV5),
        (SNAPSHOT_SCHEMA, true) => Err(PresenceError::UnexpectedRetainedField),
        (RETAINED_SCHEMA, true) => Ok(BundleEncoding::RetainedV6),
        (RETAINED_SCHEMA, false) => Err(PresenceError::MissingRetainedField),
        _ => Err(PresenceError::UnsupportedSchema),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(super) enum TransportError {
    #[error("retained transport progress refused")]
    Refused,
    #[error("retained transport deadline expired")]
    Deadline,
    #[error("retained transport size overflow")]
    Overflow,
    #[error("retained transport allocation refused")]
    Allocation,
    #[error("invalid retained transport JSON")]
    InvalidJson,
    #[error("invalid retained transport: {0}")]
    InvalidShape(&'static str),
    #[error("retained transport {resource} limit {limit} exceeded by {actual}")]
    Limit {
        resource: &'static str,
        limit: usize,
        actual: usize,
    },
    #[error(transparent)]
    Presence(#[from] PresenceError),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
/// Success records exact accepted transport charges. On refusal, work/bytes
/// include attempted reservations: a local ceiling may have rejected them
/// before calling progress. They are NOT consumed-work evidence or refundable
/// credit, and must never be subtracted to manufacture a reusable remainder.
pub(super) struct TransportUsage {
    pub(super) charged_work: usize,
    pub(super) charged_bytes: usize,
    pub(super) returned_owned_bytes: usize,
}

/// Production callers consume the result; the usage report is for tests.
#[derive(Debug)]
pub(super) struct TransportOutcome<T> {
    pub(super) result: Result<T, TransportError>,
    #[cfg(test)]
    pub(super) usage: TransportUsage,
}

/// Required before borrowing raw fields from a complete outer JSON document.
/// This prices a depth-only scan and bounds RawValue's nesting scratch; it does
/// not price legacy fields subsequently parsed by the outer DTO.
#[cfg(test)]
pub(super) fn admit_outer_json(
    bytes: &[u8],
    deadline: Instant,
    progress: Progress<'_>,
) -> TransportOutcome<()> {
    control::run(deadline, progress, |control| lexical::outer(bytes, control))
}

/// Decode new owners through the original deadline and cumulative progress.
#[cfg(test)]
pub(super) fn decode(
    schema: &str,
    field: BorrowedField<'_>,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> TransportOutcome<RetainedField> {
    control::run(deadline.min(wire.deadline), progress, |control| {
        control.constrain(wire.max_work, wire.max_storage_bytes)?;
        presence(schema, !field.is_absent())?;
        match field {
            BorrowedField::Absent => Ok(RetainedField::Absent),
            BorrowedField::Present(bytes) => decode::read(bytes, wire, control),
        }
    })
}

/// Emit a raw inventory array, or None for an omitted v5 field. The future outer
/// writer must additionally admit its complete output allocation.
#[cfg(test)]
pub(super) fn encode(
    schema: &str,
    field: &RetainedField,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> TransportOutcome<Option<Vec<u8>>> {
    control::run(deadline.min(wire.deadline), progress, |control| {
        control.constrain(wire.max_work, wire.max_storage_bytes)?;
        schema_presence(schema, field)?;
        match field {
            RetainedField::Absent => Ok(None),
            RetainedField::Present(entries) => encode::write(entries, wire, control).map(Some),
        }
    })
}

/// Encode a borrowed v5 snapshot and its explicit retained-field state.
/// Present evidence selects v6, including a present empty inventory. The
/// source snapshot must itself be v5; a v6 document cannot shed its evidence
/// by passing through this function. Nothing here authenticates a proof.
///
/// The caller admits borrowed source ownership separately. Parser scratch and
/// the output owner are cumulatively charged, without refunds; inventory views
/// borrow their payloads rather than copying a second encoded buffer. String lengths
/// are admitted before serde's opaque escaping scan; this is not a hard
/// cancellation-latency or allocator-exact RSS guarantee.
/// Wire work/storage ceilings constrain inventory preparation here; complete
/// framing and emission use `BundleLimits` and the same cumulative callback.
/// This differs from the inventory-only `encode` operation's local scope.
#[cfg(test)]
pub(super) fn encode_bundle(
    bundle: &super::SerializableProofBundle,
    field: &RetainedField,
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> TransportOutcome<Vec<u8>> {
    let deadline = deadline.min(limits.deadline).min(wire.deadline);
    control::run(deadline, progress, |control| {
        control.constrain(limits.max_work, limits.max_storage_bytes)?;
        outer_encode::write(bundle, field, limits, wire, deadline, control)
    })
}

/// Re-encode an owning v6 envelope, retaining its actual schema and mandatory
/// inventory. Source owners stay borrowed and must already be admitted by the
/// caller. No cloning, legacy normalization or proof acceptance occurs here.
/// The same controlled two-pass writer, ceilings and original minimum deadline
/// apply as for `encode_bundle`; the cumulative caller allowance is not renewed.
pub(super) fn encode_versioned_bundle(
    envelope: &RetainedBundle,
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> TransportOutcome<Vec<u8>> {
    let deadline = deadline.min(limits.deadline).min(wire.deadline);
    control::run(deadline, progress, |control| {
        control.constrain(limits.max_work, limits.max_storage_bytes)?;
        outer_encode::write_versioned(envelope, limits, wire, deadline, control)
    })
}

/// Admit and borrow the complete versioned envelope, without decoding any
/// legacy owner or authenticating nested proof data. The input owner remains
/// the caller's responsibility. The returned view preserves the actual wire
/// schema and inventory together; it is not a normalized legacy snapshot.
#[cfg(test)]
pub(super) fn borrow_bundle<'a>(
    bytes: &'a [u8],
    limits: &BundleLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> TransportOutcome<OuterView<'a>> {
    control::run(deadline.min(limits.deadline), progress, |control| {
        control.constrain(limits.max_work, limits.max_storage_bytes)?;
        outer_view::read(bytes, limits.max_json_bytes, control)
    })
}

#[cfg(test)]
mod tests;
