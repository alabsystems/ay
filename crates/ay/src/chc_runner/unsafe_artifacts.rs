// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Preserve deciding original-clause evidence through CLI publication.

use super::*;
use ay::chc::{
    ChcGroundDerivationArtifactErrorReason, ChcProofRunArtifact, ChcReplayObligationKind,
    ChcReplayPayloadFormat, CHC_GROUND_DERIVATION_ARTIFACT_ROLE,
    CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA, CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
    CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA,
};

pub(super) enum ChcReplayPayload {
    Smt(ChcReplayObligation),
    Ground(ChcProofRunArtifact),
}

pub(super) struct ReplayFile {
    pub(super) kind: ChcReplayObligationKind,
    pub(super) file_name: String,
    pub(super) role: &'static str,
    pub(super) format: ChcReplayPayloadFormat,
    pub(super) bytes: Vec<u8>,
}

impl ChcReplayPayload {
    pub(super) fn into_file(self) -> io::Result<ReplayFile> {
        match self {
            Self::Smt(obligation) => Ok(ReplayFile {
                kind: obligation.kind,
                file_name: format!(
                    "{:03}-{}.smt2",
                    obligation.clause_index,
                    obligation.kind.as_str()
                ),
                role: "replay-obligation",
                format: ChcReplayPayloadFormat::SmtlibV1,
                bytes: obligation.smtlib.into_bytes(),
            }),
            Self::Ground(artifact) => {
                let format = match (artifact.schema(), artifact.role()) {
                    (
                        CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA,
                        CHC_GROUND_DERIVATION_ARTIFACT_ROLE,
                    ) => ChcReplayPayloadFormat::GroundDerivationV1,
                    (
                        CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA,
                        CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
                    ) => ChcReplayPayloadFormat::GroundDerivationV2,
                    _ => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "unsupported CHC ground artifact schema or role",
                        ));
                    }
                };
                Ok(ReplayFile {
                    kind: ChcReplayObligationKind::TraceValidity,
                    file_name: format!("trace-validity-{}.json", artifact.role()),
                    role: artifact.role(),
                    format,
                    bytes: artifact.into_bytes(),
                })
            }
        }
    }
}

pub(super) fn unsafe_replay_payloads(
    problem: &ChcProblem,
    counterexample: &Counterexample,
) -> ChcResult<Vec<ChcReplayPayload>> {
    let now = Instant::now();
    let timeout_ms = GLOBAL_TIMEOUT_MS.load(Ordering::Relaxed);
    let deadline = if timeout_ms == 0 {
        now.checked_add(Duration::from_secs(30))
    } else {
        START_TIME
            .get()
            .and_then(|start| start.checked_add(Duration::from_millis(timeout_ms)))
    };
    let mut stopped = false;
    unsafe_replay_payloads_with_progress(problem, counterexample, &mut || {
        stopped |= deadline.is_none_or(|deadline| Instant::now() >= deadline);
        !stopped
    })
}

fn unsafe_replay_payloads_with_progress(
    problem: &ChcProblem,
    counterexample: &Counterexample,
    progress: &mut dyn FnMut() -> bool,
) -> ChcResult<Vec<ChcReplayPayload>> {
    if !progress() {
        return Err(ay::chc::ChcError::Verification(
            "CHC unsafe evidence export interrupted".to_string(),
        ));
    }
    if !counterexample.has_ground_derivation() {
        // Preserve the legacy transition-system exporter when no ground
        // derivation is carried. A rejected candidate is never absence.
        let obligations = counterexample.trace_validity_replay_obligations(problem)?;
        if !progress() {
            return Err(ay::chc::ChcError::Verification(
                "CHC unsafe evidence export interrupted".to_string(),
            ));
        }
        return Ok(obligations.into_iter().map(ChcReplayPayload::Smt).collect());
    }
    let v1 = counterexample.ground_derivation_artifact_with_progress(problem, progress);
    let artifact = match v1 {
        Ok(artifact) => artifact,
        Err(error) if error.reason == ChcGroundDerivationArtifactErrorReason::Interrupted => {
            return Err(ay::chc::ChcError::Verification(error.to_string()));
        }
        Err(v1_error) => {
            // Canonical v2 carries source-authenticated finite-UF values that
            // v1 cannot encode. Both producers validate against the original
            // source and independently decode/check their exact bytes. The
            // same caller progress grant spans both attempts.
            counterexample
                .ground_derivation_artifact_v2_with_progress(problem, progress)
                .map_err(|v2_error| {
                    ay::chc::ChcError::Verification(format!(
                        "CHC ground evidence export failed: v1: {v1_error}; v2: {v2_error}"
                    ))
                })?
        }
    };
    if !progress() {
        return Err(ay::chc::ChcError::Verification(
            "CHC unsafe evidence export interrupted".to_string(),
        ));
    }
    Ok(vec![ChcReplayPayload::Ground(artifact)])
}

#[cfg(test)]
mod tests;
