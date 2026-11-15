// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    ChcQueryPlayback, ChcQueryPlaybackControl as Control, ChcQueryPlaybackError as Error, Result,
};
use crate::ground_derivation::{
    GroundDerivation, GroundDerivationStep,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES as EDGES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS as STEPS,
};
use crate::{
    validate_chc_ground_derivation_artifact_v2_with_progress, ChcProofRunArtifact,
    ChcValidatedGroundDerivation, Counterexample,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

pub(super) fn lift(
    row: &ChcQueryPlayback<'_>,
    bytes: &[u8],
    control: &mut Control<'_>,
) -> Result<(ChcProofRunArtifact, ChcValidatedGroundDerivation)> {
    control.poll()?;
    let incoming =
        validate_chc_ground_derivation_artifact_v2_with_progress(&row.problem, bytes, &mut || {
            control.poll().is_ok()
        });
    control.poll()?;
    let incoming = incoming?;
    let candidate = project(row, incoming.derivation(), control)?;
    drop(incoming);
    control.poll()?;
    let candidate = Counterexample::new(Vec::new()).with_ground_derivation(candidate);
    let artifact = candidate
        .ground_derivation_artifact_v2_with_progress(row.original, &mut || control.poll().is_ok());
    drop(candidate);
    control.poll()?;
    let artifact = artifact?;
    let validated = validate_chc_ground_derivation_artifact_v2_with_progress(
        row.original,
        artifact.bytes(),
        &mut || control.poll().is_ok(),
    );
    control.poll()?;
    Ok((artifact, validated?))
}

fn project(
    row: &ChcQueryPlayback<'_>,
    incoming: &GroundDerivation,
    control: &mut Control<'_>,
) -> Result<GroundDerivation> {
    let mut roots = Vec::new();
    control.reserve(&mut roots, incoming.steps.len(), STEPS)?;
    let mut steps = Vec::new();
    let mut edge_count = 0usize;
    for step in &incoming.steps {
        control.poll()?;
        let origin = row
            .origins
            .get(step.clause_index)
            .ok_or(Error::InvalidSource)?;
        let added = origin
            .consumers
            .len()
            .checked_add(1)
            .ok_or(Error::LimitExceeded)?;
        if steps.len().checked_add(added).is_none_or(|n| n > STEPS) {
            return Err(Error::LimitExceeded);
        }
        edge_count = edge_count
            .checked_add(step.premises.len())
            .and_then(|n| n.checked_add(origin.consumers.len()))
            .filter(|n| *n <= EDGES)
            .ok_or(Error::LimitExceeded)?;
        let mut premises = Vec::new();
        control.reserve(&mut premises, step.premises.len(), EDGES)?;
        for &premise in &step.premises {
            control.poll()?;
            premises.push(*roots.get(premise).ok_or(Error::InvalidSource)?);
        }
        let mut env = FxHashMap::default();
        env.try_reserve(step.env.len())
            .map_err(|_| Error::AllocationFailed)?;
        for (name, value) in &step.env {
            control.poll()?;
            // Copy the entire already-validated typed environment, including
            // source-bound finite-UF evaluator observations. No completion,
            // filtering, textual parsing, type narrowing or defaulting.
            // Each individual clone remains an opaque interval bounded by the
            // V2 total-value/node/depth/token admission already performed.
            env.insert(name.clone(), value.clone());
        }
        control.push(
            &mut steps,
            GroundDerivationStep {
                clause_index: origin.first,
                env,
                premises,
            },
            STEPS,
        )?;
        for &clause_index in &origin.consumers {
            control.poll()?;
            let premise = steps.len().checked_sub(1).ok_or(Error::InvalidSource)?;
            let mut premises = Vec::new();
            control.push(&mut premises, premise, EDGES)?;
            control.push(
                &mut steps,
                GroundDerivationStep {
                    clause_index,
                    env: FxHashMap::default(),
                    premises,
                },
                STEPS,
            )?;
        }
        let root = steps.len().checked_sub(1).ok_or(Error::InvalidSource)?;
        control.push(&mut roots, root, STEPS)?;
    }
    let query_step = *roots.get(incoming.query_step).ok_or(Error::InvalidSource)?;
    drop(roots);
    control.poll()?;
    Ok(GroundDerivation { steps, query_step })
}
