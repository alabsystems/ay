// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Continue the original compact witness owner through portable publication.
//! No tree-value conversion, callback-free retry or fresh producer allowance.

use super::*;
use crate::{ChcError, ChcPdrProofRun, ChcResult, Counterexample, VerifiedChcResult};

impl Counterexample {
    /// Export complete shared values only after fresh original-clause replay.
    /// The witness retains its original solve controls and cumulative allowance.
    pub fn compact_ground_derivation_artifact(
        &self,
        problem: &ChcProblem,
    ) -> Result<ChcProofRunArtifact> {
        self.compact_ground_derivation_artifact_with_progress(problem, &mut || true)
    }

    /// Export compact evidence with a sticky borrowed continuation callback.
    ///
    /// Every controlled producer, transport and independent replay operation
    /// observes this callback and the witness's original owner. This does not
    /// make opaque arithmetic, serde or allocator intervals interruptible.
    pub fn compact_ground_derivation_artifact_with_progress(
        &self,
        problem: &ChcProblem,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<ChcProofRunArtifact> {
        let evidence = self.compact_evidence().ok_or_else(|| {
            error(
                Reason::MissingGroundDerivation,
                "no compact ground derivation",
            )
        })?;
        let mut original = evidence.owner();
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // Capture only an additional admission boundary; all work/storage
            // still debit the ORIGINAL owner, never this boundary's counters.
            let mut caller = Owner::capture().map_err(native_error)?;
            let mut continuation = || caller.poll().is_ok() && progress();
            let mut owner = original.with_progress(&mut continuation);
            encode_with_owner(problem, evidence.derivation(), &mut owner)
        }));
        match outcome {
            Err(_) => original.refuse(CompactError::Stopped).map_err(native_error),
            Ok(Err(failure)) if failure.reason == Reason::Interrupted => {
                original.refuse(CompactError::Stopped).map_err(native_error)
            }
            Ok(Err(failure)) if failure.reason == Reason::SourceWorkLimitExceeded => original
                .refuse(CompactError::Resource)
                .map_err(native_error),
            Ok(result) => result,
        }
    }
}

impl ChcPdrProofRun {
    /// Export a verified Unsafe run's complete compact witness, when present.
    /// Missing compact evidence returns `None`, never an empty proof.
    pub fn unsafe_compact_ground_derivation_artifact_bytes(&self) -> ChcResult<Option<Vec<u8>>> {
        self.unsafe_compact_ground_derivation_artifact_bytes_with_progress(&mut || true)
            .map_err(|error| ChcError::Verification(format!("compact witness export: {error}")))
    }

    /// Continue a compact witness through checked export without renewing its
    /// original allowance. Interruption is an error, not a format fallback.
    pub fn unsafe_compact_ground_derivation_artifact_bytes_with_progress(
        &self,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<Option<Vec<u8>>> {
        if let VerifiedChcResult::Unsafe(verified) = self.result() {
            let counterexample = verified.counterexample();
            if counterexample.compact_evidence().is_some() {
                // The first callback offer belongs to the retained witness,
                // too. No transient refusal may leave that owner reusable.
                return counterexample
                    .compact_ground_derivation_artifact_with_progress(self.problem(), progress)
                    .map(|artifact| Some(artifact.into_bytes()));
            }
        }
        if !progress() {
            return Err(native_error(CompactError::Stopped));
        }
        Ok(None)
    }
}
