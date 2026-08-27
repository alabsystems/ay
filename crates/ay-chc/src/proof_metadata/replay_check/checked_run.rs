// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only views over an atomically bound checked-replay result.

use super::ChcCheckedReplayRun;
use crate::{ChcCheckedReplaySummary, ChcPdrProofRun, ChcProofEvidenceManifest};

/// Immutable checked-replay run access.
///
/// The run, manifest, summary, and bytes form one validated bundle. Callers
/// cannot substitute any constituent after checked replay succeeds:
///
/// ```compile_fail
/// use ay_chc::{ChcCheckedReplayRun, ChcPdrProofRun};
///
/// fn replace_run(checked: &mut ChcCheckedReplayRun, run: ChcPdrProofRun) {
///     checked.proof_run = run;
/// }
/// ```
impl ChcCheckedReplayRun {
    /// Return the upgraded problem-bound proof run.
    pub fn proof_run(&self) -> &ChcPdrProofRun {
        &self.proof_run
    }

    /// Return the admitted evidence manifest.
    pub fn manifest(&self) -> &ChcProofEvidenceManifest {
        &self.manifest
    }

    /// Return the validated checked replay summary.
    pub fn summary(&self) -> &ChcCheckedReplaySummary {
        &self.summary
    }

    /// Return normalized problem artifact bytes.
    pub fn problem_bytes(&self) -> &[u8] {
        &self.problem_bytes
    }

    /// Return certificate artifact bytes.
    pub fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }

    /// Return solver transcript bytes produced by this pass, when present.
    pub fn run_log_bytes(&self) -> Option<&[u8]> {
        self.run_log_bytes.as_deref()
    }

    /// Return the replay-log artifact bytes.
    pub fn replay_log_bytes(&self) -> &[u8] {
        &self.replay_log_bytes
    }

    /// Return the checked-report artifact bytes.
    pub fn checked_report_bytes(&self) -> &[u8] {
        &self.checked_report_bytes
    }

    pub(crate) fn into_proof_run(self) -> ChcPdrProofRun {
        self.proof_run
    }
}
