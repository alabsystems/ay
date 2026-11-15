// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One accepted native assignment; snapshots are DATA, not replay permission.

use super::*;
use ay_dpll::api::CompleteModelValue;

pub(in crate::quantified::counterexample) fn extract(
    obligation: &str,
    names: &[&str],
    function_names: &[&str],
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<(Vec<CompleteModelValue>, Vec<ScalarFunctionModel>)> {
    if names.len() > 4096 || function_names.len() > 4096 {
        return None;
    }
    // The literal subset keeps the existing single bounded response/decoder.
    // Snapshot authentication has its native persistent ledger; subsequent
    // DATA topology/serialization is prepaid from this same SourceControl.
    control.bytes(24 * 1024 * 1024)?;
    if !function_names.is_empty() {
        control.bytes(24 * 1024 * 1024)?;
    }
    let result = attempt(
        obligation,
        deadline,
        memory,
        cancellation,
        control,
        |solver| {
            let values = solver.try_get_named_values_complete(names).ok()?;
            control.poll()?;
            (Instant::now() < deadline).then_some(())?;
            let functions = if function_names.is_empty() {
                Vec::new()
            } else {
                solver
                    .try_get_named_scalar_function_models(function_names)
                    .ok()?
            };
            // The solver/model was never mutated or replaced between these reads.
            Some((values, functions))
        },
    );
    control.poll()?;
    (Instant::now() < deadline).then_some(())?;
    result
}
