// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compact replay is terminal once selected: no recursive export or SMT retry.

use super::ground_export::ReplayProgress;
use super::*;
use crate::ground_derivation::compact_artifact;
use crate::ChcReplayPayloadFormat as Format;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

#[cfg(test)]
mod tests;

/// Read the later caller BEFORE installing the retained witness observer.
/// A failed capture is terminal for that witness, not a retryable fresh call.
pub(super) fn capture_caller(
    original: Option<&mut crate::ground_derivation::compact::Owner<'static>>,
) -> ChcResult<Option<ay_core::resource::CheckStop>> {
    let Some(owner) = original else {
        return Ok(None);
    };
    match ay_core::resource::current_check_stop() {
        Ok(stop) => Ok(stop),
        Err(_) => owner
            .refuse(crate::ground_derivation::compact::Error::Stopped)
            .map_err(|error| verification_error(error.to_string())),
    }
}

fn control_open(
    control: &crate::smt::replay_control::ScopedReplayControl,
    interrupt: Option<&AtomicBool>,
) -> bool {
    control.open() && !interrupt.is_some_and(|flag| flag.load(Ordering::Acquire))
}

/// Observe captured caller limits before invoking a foreign callback.
pub(super) fn admit_control(
    original: Option<&mut crate::ground_derivation::compact::Owner<'static>>,
    control: &crate::smt::replay_control::ScopedReplayControl,
    interrupt: Option<&AtomicBool>,
) -> ChcResult<()> {
    if control_open(control, interrupt) {
        return Ok(());
    }
    if let Some(owner) = original {
        return owner
            .refuse(crate::ground_derivation::compact::Error::Stopped)
            .map_err(|error| verification_error(error.to_string()));
    }
    // Every other replay refusal is classified as exhaustion or interruption
    // (`ReplayProgress::check`); a captured caller limit keeps that class.
    Err(verification_error(
        "checked replay caller limit exhausted or interrupted; staying metadata-only",
    ))
}

/// Even the constructor's first callback belongs to the retained witness.
pub(super) fn continuation<'a>(
    original: Option<&crate::ground_derivation::compact::Owner<'static>>,
    progress: &'a mut dyn FnMut() -> bool,
    caller: Option<ay_core::resource::CheckStop>,
    control: &'a crate::smt::replay_control::ScopedReplayControl,
    interrupt: Option<Arc<AtomicBool>>,
) -> impl FnMut() -> bool + 'a {
    let retained = original.map(|owner| owner.retained());
    move || match &retained {
        Some(owner) => {
            // Invoke both observers INSIDE the original witness's borrowed
            // continuation. A one-shot stop or unwind is latched before it can
            // disappear with the caller's TLS scope or a later retry.
            let mut allowed = || {
                control_open(control, interrupt.as_deref())
                    && !caller.as_ref().is_some_and(|stop| stop())
                    && progress()
                    && !caller.as_ref().is_some_and(|stop| stop())
                    && control_open(control, interrupt.as_deref())
            };
            owner.with_progress(&mut allowed).poll().is_ok()
        }
        None => {
            control_open(control, interrupt.as_deref())
                && progress()
                && control_open(control, interrupt.as_deref())
        }
    }
}

pub(super) fn select_plan(
    run: &ChcPdrProofRun,
    preferred: Option<Format>,
    progress: &mut ReplayProgress<'_>,
) -> ChcResult<Option<CheckedReplayPlan>> {
    progress.check()?;
    let present = matches!(&run.result, VerifiedChcResult::Unsafe(cex)
        if cex.counterexample().compact_evidence().is_some());
    let selected = preferred == Some(Format::CompactGroundDerivationV1)
        || (present && preferred == Some(Format::SmtlibV1));
    if !selected {
        return Ok(None);
    }
    if !present {
        return Err(verification_error(
            "compact replay requires original compact evidence",
        ));
    }
    let result =
        run.unsafe_compact_ground_derivation_artifact_bytes_with_progress(&mut || progress.poll());
    progress.check()?;
    let artifact_bytes = result
        .map_err(|error| verification_error(error.to_string()))?
        .ok_or_else(|| verification_error("compact ground exporter returned no evidence"))?;
    Ok(Some(CheckedReplayPlan::GroundDerivation {
        format: Format::CompactGroundDerivationV1,
        artifact_bytes,
    }))
}

pub(super) fn check_row(
    run: &ChcPdrProofRun,
    artifact_bytes: Vec<u8>,
    progress: &mut ReplayProgress<'_>,
) -> ChcResult<(
    ChcCheckedReplayObligation,
    SealedReplayObligationPayload,
    serde_json::Value,
)> {
    progress.check()?;
    let VerifiedChcResult::Unsafe(cex) = &run.result else {
        return Err(verification_error("compact evidence cannot prove Safe"));
    };
    let evidence = cex
        .counterexample()
        .compact_evidence()
        .ok_or_else(|| verification_error("compact replay lost its original owner"))?;
    let retained = evidence.owner();
    let mut callback = || progress.poll();
    let mut owner = retained.with_progress(&mut callback);
    let validated =
        compact_artifact::validate_with_owner(run.problem(), &artifact_bytes, &mut owner)
            .map_err(|error| verification_error(error.to_string()))?;
    let work = artifact_bytes
        .len()
        .checked_mul(3)
        .ok_or_else(|| verification_error("compact row accounting overflow"))?;
    owner
        .admit(work, 4096)
        .map_err(|error| verification_error(error.to_string()))?;
    let name = super::super::replay_payload_role(Format::CompactGroundDerivationV1);
    let query = ChcProofArtifactDigest::from_bytes(name, &artifact_bytes);
    let checker_command = format!(
        "{CHC_IN_PROCESS_REPLAY_CHECKER_NAME} --validate-compact-ground-derivation-v1 {name}"
    );
    let record = serde_json::json!({
        "name": name, "kind": ChcReplayObligationKind::TraceValidity.as_str(),
        "payload_format": Format::CompactGroundDerivationV1.as_str(),
        "query_sha256": query.sha256, "expected": "valid", "verdict": "valid",
        "status": "pass", "step_count": validated.step_count(),
        "value_node_count": validated.node_count(),
        "strict_bundle": false, "strict_alethe": false, "strict_cert": null,
    });
    let mut row = ChcCheckedReplayObligation::new(
        name,
        ChcReplayObligationKind::TraceValidity,
        query,
        checker_command,
        ChcReplayCheckResult::pass(),
    );
    row.payload_format = Format::CompactGroundDerivationV1;
    let payload = SealedReplayObligationPayload::try_new_compact_ground_derivation(
        &row,
        &validated,
        artifact_bytes,
        &mut || owner.poll().is_ok(),
    )?;
    owner
        .poll()
        .map_err(|error| verification_error(error.to_string()))?;
    drop(validated);
    drop(owner);
    progress.check()?;
    Ok((row, payload, record))
}
