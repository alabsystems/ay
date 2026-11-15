// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{refused, R34RowStatus};
use ay_chc::engines::{
    validate_external_invariant_model_typed, ExternalInvariantValidation as Kind,
    ExternalInvariantValidationOwner,
};
use ay_chc::{
    CancellationToken, ChcCheckedReplayRun, ChcPdrProofRun, ChcProblem, ChcResult, PdrConfig,
    VerifiedChcResult,
};
use ay_core::time::Instant;
use ay_encode::invoke::{solve_with_proof_report_with_cancellation, EncodeConfig};

pub(super) fn run(
    problem: ChcProblem,
    config: &EncodeConfig,
    mut validation: PdrConfig,
    owner: &ExternalInvariantValidationOwner,
    cancellation: &CancellationToken,
) -> ChcResult<R34RowStatus> {
    if let Some(kind) = owner.check() {
        return Ok(refused(kind));
    }
    let source_identity = problem.normalized_input_sha256();
    let report = solve_with_proof_report_with_cancellation(problem.clone(), config, cancellation)
        .map_err(|error| ay_chc::ChcError::Internal(error.to_string()))?;
    if let Some(kind) = owner.check() {
        return Ok(refused(kind));
    }
    if report.proof_run().problem().normalized_input_sha256() != source_identity {
        return Err(ay_chc::ChcError::Verification(
            "R34 returned proof is bound to another problem".to_owned(),
        ));
    }
    let result = match report.proof_run().result() {
        VerifiedChcResult::Safe(_) => "Safe",
        VerifiedChcResult::Unsafe(_) => "Unsafe",
        VerifiedChcResult::Unknown(_) => "Unknown",
        _ => {
            return Err(ay_chc::ChcError::Verification(
                "R34 unsupported future verified result".to_owned(),
            ));
        }
    }
    .to_owned();
    let checked_model = if let VerifiedChcResult::Safe(invariant) = report.proof_run().result() {
        validation.solve_timeout = Some(owner.deadline().saturating_duration_since(Instant::now()));
        // The outer owner already holds this phase. Reentering with_resources
        // would (correctly) refuse; the typed validator inherits its active TLS
        // minima, and the same owner is polled before/after all opaque work.
        Some(validate_external_invariant_model_typed(
            &problem,
            invariant.model(),
            &validation,
        )?)
    } else {
        None
    };
    if let Some(kind) = owner.check() {
        return Ok(refused(kind));
    }
    if let Some(rejection) = checked_model.and_then(model_refusal) {
        return Ok(rejection);
    }
    // R34 requires replay, so a failed strict pass must retain its real error.
    // The best-effort report wrapper deliberately discards that diagnostic.
    let replayed = if report.checked_replay().is_none() && report.proof_run().accepted_as_proof() {
        Some(strict_replay(
            report.proof_run(),
            owner.deadline(),
            cancellation,
        )?)
    } else {
        None
    };
    if let Some(kind) = owner.check() {
        return Ok(refused(kind));
    }
    let checked_run = replayed.as_ref().or_else(|| report.checked_replay());
    let proof_run = checked_run.map_or(report.proof_run(), ChcCheckedReplayRun::proof_run);
    let checked = checked_run.is_some() && proof_run.metadata().trust_full_verifier_admissible();
    let status = R34RowStatus::Observed {
        result,
        original_model_validation: checked_model.map(|kind| format!("{kind:?}")),
        checked_original_replay: checked,
        metadata: proof_run.metadata().to_json_value(),
    };
    // No live solver/model/proof bundle crosses the owner's final cleanup fence.
    drop(replayed);
    drop(report);
    drop(problem);
    Ok(owner.check().map_or(status, refused))
}

// Keep the report wrapper's classified-panic policy, but propagate the original
// strict-replay Result. The outer owner still holds its original absolute wall,
// shared ticks and cancellation scope; no phase re-enters or renews that owner.
fn strict_replay(
    run: &ChcPdrProofRun,
    deadline: Instant,
    cancellation: &CancellationToken,
) -> ChcResult<ChcCheckedReplayRun> {
    ay_core::catch_ay_panics(
        std::panic::AssertUnwindSafe(|| {
            run.run_checked_replay_with_cancellation(
                deadline.saturating_duration_since(Instant::now()),
                cancellation,
            )
        }),
        |reason| Err(ay_chc::ChcError::Internal(reason)),
    )
}

#[cfg(test)]
mod replay_tests;

fn model_refusal(kind: Kind) -> Option<R34RowStatus> {
    match kind {
        Kind::Valid => None,
        Kind::Refuted | Kind::Rejected => Some(R34RowStatus::OriginalModelRejected {
            observed: format!("{kind:?}"),
        }),
        other => Some(refused(other)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_original_model_cannot_publish_safe_or_replay_evidence() {
        for kind in [Kind::Refuted, Kind::Rejected] {
            assert!(matches!(
                model_refusal(kind),
                Some(R34RowStatus::OriginalModelRejected { .. })
            ));
        }
        assert!(model_refusal(Kind::Valid).is_none());
    }

    #[test]
    fn every_typed_original_validation_refusal_remains_a_non_verdict() {
        for kind in [
            Kind::Timeout,
            Kind::Cancelled,
            Kind::Memory,
            Kind::WorkLimit,
            Kind::Inconclusive,
        ] {
            assert!(matches!(model_refusal(kind),
                Some(R34RowStatus::ResourceRefused { observed }) if observed == format!("{kind:?}")));
        }
    }
}
