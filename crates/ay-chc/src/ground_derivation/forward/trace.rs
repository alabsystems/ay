// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn materialize(
    nodes: &[Node],
    mut cursor: usize,
    query: GroundDerivationStep,
    cache: &mut GroundSourceSurfaceCache<'_>,
    control: &mut GroundValidationControl<'_>,
) -> Result<GroundDerivation, GroundDerivationError> {
    let mut path = Vec::new();
    loop {
        control.poll()?;
        let node = nodes
            .get(cursor)
            .ok_or(GroundDerivationError::RootOutOfRange)?;
        cache.charge(1).map_err(surface_error)?;
        path.try_reserve(1)
            .map_err(|_| GroundDerivationError::SourceWorkLimitExceeded)?;
        path.push(cursor);
        let Some(parent) = node.parent else { break };
        if parent >= cursor {
            return Err(GroundDerivationError::PremiseNotWellFounded {
                step: cursor,
                premise: parent,
            });
        }
        cursor = parent;
    }
    cache
        .charge(
            path.len()
                .checked_add(1)
                .ok_or(GroundDerivationError::SourceWorkLimitExceeded)?,
        )
        .map_err(surface_error)?;
    let mut steps = Vec::new();
    steps
        .try_reserve_exact(path.len() + 1)
        .map_err(|_| GroundDerivationError::SourceWorkLimitExceeded)?;
    for index in path.into_iter().rev() {
        control.poll()?;
        let node = &nodes[index];
        cache
            .charge_step_scalar_replay(node.step.clause_index, &node.step.env, &[])
            .map_err(surface_error)?;
        control.poll()?;
        let premises = if node.parent.is_some() {
            vec![steps.len() - 1]
        } else {
            Vec::new()
        };
        steps.push(GroundDerivationStep {
            clause_index: node.step.clause_index,
            env: node.step.env.clone(),
            premises,
        });
        control.poll()?;
    }
    let query_step = steps.len();
    steps.push(GroundDerivationStep {
        premises: vec![query_step - 1],
        ..query
    });
    Ok(GroundDerivation { steps, query_step })
}
