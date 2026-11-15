// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict, data-only wire types. No serde implementation on an evidence type.

use super::*;
use serde::{Deserialize, Serialize};

pub(super) const SCHEMA: &str = "ay.quantified-chc-trace-artifact/v1";

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Wire {
    pub(super) schema: String,
    pub(super) source: String,
    pub(super) steps: Vec<Step>,
    pub(super) functions: String,
    pub(super) pinned_sha256: String,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Step {
    pub(super) clause_index: usize,
    pub(super) premises: Vec<usize>,
    pub(super) bindings: Vec<Local>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Local {
    pub(super) name: String,
    pub(super) value: String,
}

pub(super) fn export(
    trace: &QuantifiedChcTrace,
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<Wire> {
    control.poll()?;
    let count = trace.clause_indices().len();
    if count == 0 || count != trace.premise_steps().len() || trace.bindings.len() > MAX_BINDINGS {
        return None;
    }
    control.bytes(count.checked_mul(std::mem::size_of::<Step>())?)?;
    let mut steps = Vec::new();
    steps.try_reserve_exact(count).ok()?;
    let mut cursor = 0;
    for (occurrence, (&index, premises)) in trace
        .clause_indices()
        .iter()
        .zip(trace.premise_steps())
        .enumerate()
    {
        control.charge(1)?;
        control.bytes(premises.len().checked_mul(std::mem::size_of::<usize>())?)?;
        let start = cursor;
        while trace
            .bindings
            .get(cursor)
            .is_some_and(|binding| binding.occurrence == occurrence)
        {
            cursor += 1;
        }
        let bindings = bindings::export(&trace.bindings[start..cursor], registry, control)?;
        steps.push(Step {
            clause_index: index,
            premises: premises.clone(),
            bindings,
        });
    }
    if cursor != trace.bindings.len() {
        return None;
    }
    let functions = functions::export(&trace.functions, problem, control)?;
    let pinned_sha256 = transport::digest(trace.replay_obligation().as_bytes(), control)?;
    control.bytes(problem.source_smtlib().len().checked_add(SCHEMA.len())?)?;
    let result = Wire {
        schema: SCHEMA.to_owned(),
        source: problem.source_smtlib().to_owned(),
        steps,
        functions,
        pinned_sha256,
    };
    control.poll()?;
    Some(result)
}

pub(super) fn topology(wire: &Wire, control: &SourceControl<'_>) -> Option<derivation::Derivation> {
    let count = wire.steps.len();
    if count == 0 {
        return None;
    }
    control.bytes(
        count.checked_mul(std::mem::size_of::<usize>() + std::mem::size_of::<Vec<usize>>())?,
    )?;
    let mut indices = Vec::new();
    let mut premises = Vec::new();
    indices.try_reserve_exact(count).ok()?;
    premises.try_reserve_exact(count).ok()?;
    let mut edges_left = count - 1;
    let mut bindings_left = MAX_BINDINGS;
    for step in &wire.steps {
        control.charge(1)?;
        edges_left = edges_left.checked_sub(step.premises.len())?;
        bindings_left = bindings_left.checked_sub(step.bindings.len())?;
        control.bytes(
            step.premises
                .len()
                .checked_mul(std::mem::size_of::<usize>())?,
        )?;
        indices.push(step.clause_index);
        premises.push(step.premises.clone());
    }
    if edges_left != 0 {
        return None;
    }
    control.poll()?;
    Some(derivation::Derivation {
        clause_indices: indices,
        premise_steps: premises,
    })
}
