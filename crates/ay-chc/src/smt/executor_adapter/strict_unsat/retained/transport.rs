// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{BoundRetainedProof, BoundRetainedProofBytes, RetainedReplayProgress};
use std::panic::AssertUnwindSafe;

impl BoundRetainedProof {
    /// Consume the live-source capability into paired actual-v4 bytes, under
    /// the SAME original request ledger. There is no raw-v3 fallback.
    pub(crate) fn encode(
        self,
        progress: &mut RetainedReplayProgress<'_>,
    ) -> Result<BoundRetainedProofBytes, String> {
        #[cfg(test)]
        let _census = progress.census_stage("transport-encode");
        let callback_owner = &mut *progress;
        let proposed = ay_core::catch_ay_panics(
            AssertUnwindSafe(move || {
                let progress = callback_owner;
                progress.admits(&self.request)?;
                let limits = progress.transport_limits();
                let bundle = self
                    .bundle
                    .encode_with_resource_control(
                        limits,
                        progress.deadline(),
                        &mut |work, bytes| progress.charge(work, bytes),
                    )
                    .map_err(|error| format!("bound retained encoding failed: {error}"))?;
                let BoundRetainedProof {
                    query,
                    request,
                    strict_verdict,
                    bundle: owner,
                    settlement,
                } = self;
                // The original proof/context owner is destroyed before terminal
                // byte-capability admission. Work is never refunded.
                drop(owner);
                let settled = settlement.settles();
                // Only now, with the proof owner gone, its transient bytes
                // return; the exact surviving buffers are debited again.
                drop(settlement);
                if settled {
                    let survivors = query
                        .capacity()
                        .checked_add(bundle.capacity())
                        .ok_or_else(|| progress.refuse("bound retained survivor size overflow"))?;
                    if !progress.charge(0, survivors) {
                        return Err(progress.refuse("bound retained survivor admission refusal"));
                    }
                }
                Ok::<_, String>(BoundRetainedProofBytes {
                    query,
                    bundle,
                    request,
                    strict_verdict,
                })
            }),
            |reason| Err(format!("bound retained encoding panicked: {reason}")),
        );
        finish(proposed, progress)
    }
}

fn finish(
    proposed: Result<BoundRetainedProofBytes, String>,
    progress: &mut RetainedReplayProgress<'_>,
) -> Result<BoundRetainedProofBytes, String> {
    match proposed {
        Err(error) => Err(progress.refuse(&error)),
        Ok(bytes) => {
            if let Err(error) = progress.check() {
                drop(bytes);
                let _ = progress.check();
                return Err(error);
            }
            Ok(bytes)
        }
    }
}

impl BoundRetainedProofBytes {
    pub(crate) fn query_bytes(&self) -> &[u8] {
        &self.query
    }
    pub(crate) fn bundle_bytes(&self) -> &[u8] {
        &self.bundle
    }
    pub(crate) fn strict_verdict(&self) -> &ay_dpll::api::StrictProofVerdict {
        &self.strict_verdict
    }

    pub(crate) fn admit(&self, progress: &mut RetainedReplayProgress<'_>) -> Result<(), String> {
        progress.admits(&self.request)
    }

    /// Used by the private sealed-row constructor, never a raw-byte mint.
    /// The caller must check the shared owner after temporary-owner cleanup.
    pub(crate) fn into_parts(self) -> (Vec<u8>, Vec<u8>) {
        (self.query, self.bundle)
    }
}
