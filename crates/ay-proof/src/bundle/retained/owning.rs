// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private owning-v6 transport and its strict replay-only composition.
//!
//! Input ownership belongs to the caller. New typed owners and all reported
//! replay debits share one cumulative control and one original minimum absolute
//! deadline. Opaque allocator, arithmetic, clone/hash and destructor intervals
//! in the admitted leaves/checker are not made allocator-exact or hard-latency
//! bounded by this composition. No external problem identity is authenticated.

use super::{
    control, outer_decode, BundleLimits, Control, Instant, Progress, RetainedBundle,
    TransportError, WireLimits,
};
#[cfg(test)]
use super::{exact_inventory, ExactInventoryError};
#[cfg(test)]
use crate::bundle::{retained_reader, BundleReCheck};
#[cfg(test)]
use crate::ProofCheckError;

/// Nonrefundable admission history, NOT an allocator/live-owner/RSS census.
/// Observed only by tests: production callers consume the result alone.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(in crate::bundle) struct OwningUsage {
    /// Charges attempted in the outer ledger, including a refused outer debit.
    /// A wire-local refusal before forwarding a debit is not an outer charge.
    pub(in crate::bundle) charged_work: usize,
    pub(in crate::bundle) charged_bytes: usize,
    /// Some only after complete ownership decoding. This conservative reserve
    /// includes parser scratch, temporary names/limbs and pinned private-owner
    /// allocation requests, even after their buffers are dropped. It excludes
    /// replay and is never added to charged_bytes a second time or refunded.
    /// It may remain Some on late refusal or a failed proof. In replay_bundle,
    /// the decoded envelope is dropped and is NOT part of the returned value.
    pub(in crate::bundle) decoded_owner_reservation_bytes: Option<usize>,
}

#[derive(Debug)]
pub(in crate::bundle) struct OwningOutcome<T, E> {
    pub(in crate::bundle) result: Result<T, E>,
    #[cfg(test)]
    pub(in crate::bundle) usage: OwningUsage,
}

#[cfg(test)]
#[derive(Debug, thiserror::Error)]
pub(in crate::bundle) enum ReadError {
    #[error(transparent)]
    Transport(#[from] TransportError),
    #[error(transparent)]
    Proof(#[from] ProofCheckError),
    #[error(transparent)]
    Inventory(#[from] ExactInventoryError),
}

#[cfg(test)]
enum ReplayKind {
    General,
    ExactInventory,
}

/// Own the actual v6 document and mandatory inventory. This only establishes
/// transport validity, never proof acceptance, and cannot choose legacy v5.
pub(in crate::bundle) fn decode_bundle(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> OwningOutcome<RetainedBundle, TransportError> {
    with_decoded(bytes, limits, wire, deadline, progress, |envelope, _, _| {
        Ok(envelope)
    })
}

/// Same exact decoder with its pre-terminal failure retained as fixed data.
pub(in crate::bundle) fn decode_bundle_observed(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
    first: &mut Option<TransportError>,
) -> OwningOutcome<RetainedBundle, TransportError> {
    with_decoded_observed(
        bytes,
        limits,
        wire,
        deadline,
        progress,
        first,
        |envelope, _, _| Ok(envelope),
    )
}

/// Decode and independently recheck a complete retained document without any
/// replacement-evidence producer or legacy fallback. Transport stop/deadline
/// takes precedence over a success OR a semantic proof error. All decoded
/// owners are dropped before final publication; uncaught panics unwind and
/// publish no outcome. The caller must still bind the intended external query.
#[cfg(test)]
pub(in crate::bundle) fn replay_bundle(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> OwningOutcome<BundleReCheck, ReadError> {
    replay_with(bytes, limits, wire, deadline, progress, ReplayKind::General)
}

/// Additionally require a complete proof with a nonempty, exact inventory of
/// assumptions in first-use order. The comparison runs before the owned
/// envelope is dropped, on the SAME cumulative control and original deadline.
/// This is internal inventory equality, NOT external query/declaration binding
/// or authority to publish a CHC certificate. No fallback selects general replay.
#[cfg(test)]
pub(in crate::bundle) fn replay_exact_bundle(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
) -> OwningOutcome<BundleReCheck, ReadError> {
    replay_with(
        bytes,
        limits,
        wire,
        deadline,
        progress,
        ReplayKind::ExactInventory,
    )
}

#[cfg(test)]
fn replay_with(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
    kind: ReplayKind,
) -> OwningOutcome<BundleReCheck, ReadError> {
    let outcome = with_decoded(
        bytes,
        limits,
        wire,
        deadline,
        progress,
        |envelope, deadline, control| {
            // Preserve semantic errors inside the outer result so transport
            // cleanup and its final stop/deadline checks cannot be bypassed.
            let checked = retained_reader::replay_versioned_with_wire_limits(
                &envelope,
                Some(*wire),
                deadline,
                &mut |work, bytes| control.charge(work, bytes).is_ok(),
            )
            .map_err(ReadError::Proof)
            .and_then(|checked| {
                if let ReplayKind::ExactInventory = kind {
                    exact_inventory::check(
                        &checked,
                        &envelope.parts().0.obligation_assertions,
                        control,
                    )?;
                }
                Ok(checked)
            });
            drop(envelope);
            control.charge(0, 0)?;
            Ok(checked)
        },
    );
    OwningOutcome {
        result: match outcome.result {
            Ok(checked) => checked,
            Err(error) => Err(ReadError::Transport(error)),
        },
        usage: outcome.usage,
    }
}

fn with_decoded<T>(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
    operation: impl FnOnce(RetainedBundle, Instant, &mut Control<'_>) -> Result<T, TransportError>,
) -> OwningOutcome<T, TransportError> {
    with_decoded_observed(
        bytes, limits, wire, deadline, progress, &mut None, operation,
    )
}

fn with_decoded_observed<T>(
    bytes: &[u8],
    limits: &BundleLimits,
    wire: &WireLimits,
    deadline: Instant,
    progress: Progress<'_>,
    first: &mut Option<TransportError>,
    operation: impl FnOnce(RetainedBundle, Instant, &mut Control<'_>) -> Result<T, TransportError>,
) -> OwningOutcome<T, TransportError> {
    let deadline = deadline.min(limits.deadline).min(wire.deadline);
    #[cfg(test)]
    let mut decoded_owner_reservation_bytes = None;
    let outcome = control::run_observed(deadline, progress, first, |control| {
        control.constrain(limits.max_work, limits.max_storage_bytes)?;
        #[cfg(test)]
        let start = control.usage.charged_bytes;
        let envelope = outer_decode::read(bytes, limits, wire, deadline, control)?;
        // Measured for the tests' usage report only; charged bytes never fall.
        #[cfg(test)]
        {
            let reserved = control
                .usage
                .charged_bytes
                .checked_sub(start)
                .ok_or(TransportError::Overflow)
                .or_else(|error| control.fail(error))?;
            decoded_owner_reservation_bytes = Some(reserved);
        }
        operation(envelope, deadline, control)
    });
    // The existing codec's returned_owned_bytes retains its narrower meaning.
    // It is neither copied nor relabeled as complete-document ownership here.
    OwningOutcome {
        result: outcome.result,
        #[cfg(test)]
        usage: OwningUsage {
            charged_work: outcome.usage.charged_work,
            charged_bytes: outcome.usage.charged_bytes,
            decoded_owner_reservation_bytes,
        },
    }
}
