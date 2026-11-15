// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One sticky caller allowance across ground export, fallback and fresh replay.
//!
//! Polling is cooperative: metadata, SMT, arithmetic, serde internals and
//! allocation/destruction still contain opaque intervals. No latency bound is
//! asserted. Interruption is classified before diagnostics erase its type.

use super::{verification_error, CheckedReplayPlan};
use crate::proof_metadata::ChcReplayPayloadFormat as Format;
use crate::smt::executor_adapter::{ReplayLimit, RetainedReplayProgress};
use crate::{
    ChcGroundDerivationArtifactError as ArtifactError,
    ChcGroundDerivationArtifactErrorReason as Reason, ChcProblem, ChcResult,
    ChcValidatedGroundDerivation,
};

#[cfg(test)]
pub(super) fn within_budget(start: &super::Instant, budget: super::Duration) -> bool {
    budget
        .checked_sub(start.elapsed())
        .is_some_and(|remaining| !remaining.is_zero())
}

pub(super) struct ReplayProgress<'a> {
    allowance: ReplayAllowance<'a>,
    stopped: bool,
    compact_owner: Option<crate::ground_derivation::compact::Owner<'static>>,
}

enum ReplayAllowance<'a> {
    Callback(&'a mut dyn FnMut() -> bool),
    Retained(RetainedReplayProgress<'a>),
}

impl<'a> ReplayProgress<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            allowance: ReplayAllowance::Callback(progress),
            stopped: false,
            compact_owner: None,
        }
    }

    pub(super) fn new_retained_for_rows(
        limit: ReplayLimit<'a>,
        callback: &'a mut dyn FnMut() -> bool,
        rows: usize,
    ) -> ChcResult<Self> {
        let allowance = RetainedReplayProgress::new_for_retained_rows(limit, callback, rows)
            .map_err(|reason| {
                verification_error(format!(
                "checked replay budget exhausted or interrupted; staying metadata-only: {reason}"
            ))
            })?;
        Ok(Self {
            allowance: ReplayAllowance::Retained(allowance),
            stopped: false,
            compact_owner: None,
        })
    }

    pub(super) fn poll(&mut self) -> bool {
        if self.stopped {
            return false;
        }
        // A nested validator may catch a callback panic. Leave refusal latched
        // while invoking user code so recovery cannot resume or try a fallback.
        self.stopped = true;
        if self
            .compact_owner
            .as_mut()
            .is_some_and(|owner| owner.poll().is_err())
        {
            return false;
        }
        let allowed = match &mut self.allowance {
            ReplayAllowance::Callback(progress) => progress(),
            ReplayAllowance::Retained(progress) => progress.charge(0, 0),
        };
        if allowed {
            self.stopped = false;
            true
        } else {
            false
        }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> bool {
        if self.stopped {
            return false;
        }
        self.stopped = true;
        if self
            .compact_owner
            .as_mut()
            .is_some_and(|owner| owner.admit(work, bytes).is_err())
        {
            return false;
        }
        let allowed = match &mut self.allowance {
            ReplayAllowance::Callback(progress) => progress(),
            ReplayAllowance::Retained(progress) => progress.charge(work, bytes),
        };
        self.stopped = !allowed;
        allowed
    }

    pub(super) fn retain_compact_owner(
        &mut self,
        owner: crate::ground_derivation::compact::Owner<'static>,
    ) -> ChcResult<()> {
        if self.compact_owner.is_some() {
            self.stopped = true;
            return Err(verification_error(
                "compact replay owner cannot be replaced",
            ));
        }
        self.compact_owner = Some(owner);
        self.check()
    }

    pub(super) fn retained_mut(&mut self) -> ChcResult<&mut RetainedReplayProgress<'a>> {
        self.check()?;
        match &mut self.allowance {
            ReplayAllowance::Retained(progress) => Ok(progress),
            ReplayAllowance::Callback(_) => Err(verification_error(
                "checked replay has no request-wide retained resource owner",
            )),
        }
    }

    pub(super) fn check(&mut self) -> ChcResult<()> {
        if self.poll() {
            Ok(())
        } else {
            Err(verification_error(
                "checked replay budget exhausted or interrupted; staying metadata-only",
            ))
        }
    }

    fn accept<T>(&mut self, result: Result<T, ArtifactError>) -> Result<T, ExportFailure> {
        if matches!(&result, Err(error) if error.reason == Reason::Interrupted) {
            self.stopped = true;
            return Err(ExportFailure::Interrupted);
        }
        if !self.poll() {
            return Err(ExportFailure::Interrupted);
        }
        result.map_err(ExportFailure::Rejected)
    }

    /// The verdict of a completed CHECK (not an export, whose publication
    /// [`Self::accept`] still admits). #completed-check-accepted: consult the
    /// LATCH, not the caller. A refusal the check observed stays final even if
    /// a nested validator swallowed it; a stop that arrives after its last
    /// poll neither discards an accepted derivation nor masks a rejection.
    /// The next phase's own admission poll is where that stop is honoured.
    fn settle_check<T>(&mut self, result: Result<T, ArtifactError>) -> Result<T, ExportFailure> {
        if self.stopped || matches!(&result, Err(error) if error.reason == Reason::Interrupted) {
            self.stopped = true;
            return Err(ExportFailure::Interrupted);
        }
        result.map_err(ExportFailure::Rejected)
    }
}

#[derive(Debug, thiserror::Error)]
enum ExportFailure {
    #[error("ground-derivation export interrupted")]
    Interrupted,
    #[error("{0}")]
    Rejected(ArtifactError),
    #[error("ground-derivation v1 export failed ({v1}); v2 export failed ({v2})")]
    Both {
        v1: ArtifactError,
        v2: ArtifactError,
    },
}

type GroundBytes = Option<(Format, Vec<u8>)>;

fn export_one(
    format: Format,
    export: &mut impl FnMut(Format, &mut dyn FnMut() -> bool) -> Result<Option<Vec<u8>>, ArtifactError>,
    progress: &mut ReplayProgress<'_>,
) -> Result<GroundBytes, ExportFailure> {
    if !progress.poll() {
        return Err(ExportFailure::Interrupted);
    }
    let result = export(format, &mut || progress.poll());
    progress
        .accept(result)
        .map(|bytes| bytes.map(|bytes| (format, bytes)))
}

fn select_export(
    preferred: Option<Format>,
    export: &mut impl FnMut(Format, &mut dyn FnMut() -> bool) -> Result<Option<Vec<u8>>, ArtifactError>,
    progress: &mut ReplayProgress<'_>,
) -> Result<GroundBytes, ExportFailure> {
    match preferred {
        None => Ok(None),
        Some(format @ (Format::GroundDerivationV1 | Format::GroundDerivationV2)) => {
            export_one(format, export, progress)
        }
        Some(Format::CompactGroundDerivationV1) => {
            // Compact replay is selected separately with its retained owner.
            Err(ExportFailure::Rejected(ArtifactError {
                reason: Reason::SchemaMismatch,
                reason_code: "schema_mismatch",
                detail: "compact ground replay requires its dedicated owner-bound route".into(),
            }))
        }
        Some(Format::SmtlibV1) => {
            // Default export preserves v1; only a non-interrupted rejection
            // permits the source-authenticated finite-UF representation.
            match export_one(Format::GroundDerivationV1, export, progress) {
                Err(ExportFailure::Rejected(v1)) => {
                    match export_one(Format::GroundDerivationV2, export, progress) {
                        Ok(None) => Err(ExportFailure::Rejected(v1)),
                        Err(ExportFailure::Rejected(v2)) => Err(ExportFailure::Both { v1, v2 }),
                        other => other,
                    }
                }
                other => other,
            }
        }
    }
}

pub(super) fn select_plan(
    preferred: Option<Format>,
    mut export: impl FnMut(Format, &mut dyn FnMut() -> bool) -> Result<Option<Vec<u8>>, ArtifactError>,
    fallback: impl FnOnce() -> ChcResult<Vec<super::ChcReplayObligation>>,
    progress: &mut ReplayProgress<'_>,
) -> ChcResult<CheckedReplayPlan> {
    progress.check()?;
    if preferred == Some(Format::CompactGroundDerivationV1) {
        return Err(verification_error(
            "compact replay requires its original owner; no legacy or SMT fallback",
        ));
    }
    let selected = select_export(preferred, &mut export, progress);
    // Check before either fallback branch, including after opaque failed work.
    progress.check()?;
    let ground_error = match selected {
        Ok(Some((format, artifact_bytes))) => {
            return Ok(CheckedReplayPlan::GroundDerivation {
                format,
                artifact_bytes,
            });
        }
        Err(ExportFailure::Interrupted) => {
            return Err(verification_error(
                "checked replay ground-derivation export interrupted; staying metadata-only",
            ));
        }
        Ok(None) => None,
        Err(error) => Some(error),
    };
    let replay = fallback();
    progress.check()?;
    match (ground_error, replay) {
        (_, Ok(obligations)) => Ok(CheckedReplayPlan::Smt(obligations)),
        (None, Err(error)) => Err(error),
        (Some(ground_error), Err(trace_error)) => Err(verification_error(format!(
            "checked replay could not produce Unsafe evidence: ground derivation: {ground_error}; SMT trace fallback: {trace_error}"
        ))),
    }
}

pub(super) fn validate_ground(
    problem: &ChcProblem,
    format: Format,
    bytes: &[u8],
    progress: &mut ReplayProgress<'_>,
) -> ChcResult<ChcValidatedGroundDerivation> {
    progress.check()?;
    let result = match format {
        Format::GroundDerivationV1 => crate::validate_chc_ground_derivation_artifact_with_progress(
            problem,
            bytes,
            &mut || progress.poll(),
        ),
        Format::GroundDerivationV2 => {
            crate::validate_chc_ground_derivation_artifact_v2_with_progress(
                problem,
                bytes,
                &mut || progress.poll(),
            )
        }
        Format::SmtlibV1 | Format::CompactGroundDerivationV1 => {
            return Err(verification_error(
                "ground replay plan labels evidence as SMT-LIB",
            ))
        }
    };
    progress.settle_check(result).map_err(|error| {
        verification_error(format!(
            "checked replay {} validation: {error}",
            format.as_str()
        ))
    })
}

#[cfg(test)]
mod tests;
