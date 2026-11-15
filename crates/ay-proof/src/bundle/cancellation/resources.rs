// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Caller-owned resource control of the tracked independent bundle reader.

use super::*;

/// Independently re-check a bundle through one sticky resource callback.
///
/// The callback receives the existing incremental work/byte charges through
/// structural preflight, complete positional term/proof copying, datatype and
/// Skolem authentication, strict checking, and result allocation. Snapshot
/// copies include unused entries and nested owning payloads; they never use a
/// producer's or checker-only store's incomplete memory ledger as their price.
/// The caller must retain its cumulative allowance between phases and, when
/// desired, across earlier construction and subsequent replay calls.
///
/// Returning false is terminal for this invocation. Refusal is latched before
/// entering the callback, including if it panics and a lower-level guard catches
/// that panic; a latched refusal fails the invocation and no cancelled partial
/// checker result is returned. The callback is not consulted after the strict
/// checker's final step, so a completed re-check is never refused afterwards.
///
/// This exposes the tracked reader's accounting, not a complete allocator/RSS
/// bound or hard latency guarantee. Some strict-checker scratch/container prices
/// are coarse; individual arithmetic, allocation and destruction intervals stay
/// opaque. JSON decoding and source-side bundle construction are outside this
/// call. Proof/context validity still does not authenticate the intended external
/// query: the consumer must retain the full binding contract of
/// [`re_check_bundle_strict`].
pub fn re_check_bundle_strict_with_resource_control(
    bundle: &SerializableProofBundle,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<BundleReCheck, ProofCheckError> {
    ResourceControl {
        progress,
        refused: false,
    }
    .run(|progress| reconstruct_and_check(bundle, progress))
}

struct ResourceControl<'a> {
    progress: Progress<'a>,
    refused: bool,
}

impl ResourceControl<'_> {
    fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.refused = true;
        if (self.progress)(work, bytes) {
            self.refused = false;
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    fn run<T>(
        &mut self,
        operation: impl FnOnce(Progress<'_>) -> Result<T, ProofCheckError>,
    ) -> Result<T, ProofCheckError> {
        self.charge(0, 0)?;
        let result = operation(&mut |work, bytes| self.charge(work, bytes).is_ok());
        // #completed-check-accepted: the latch, not a fresh callback (see
        // `Cancellation::run`).
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        result
    }
}

#[cfg(test)]
mod tests;
