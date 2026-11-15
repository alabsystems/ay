// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Bind only exact direct source variables from the complete concrete body
/// tuple. A fact must be fully ground; an extra head/guard variable refuses.
pub(super) fn environment(
    clause_index: usize,
    body: Option<(&[ChcExpr], &[SmtValue])>,
    cache: &mut GroundSourceSurfaceCache<'_>,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<FxHashMap<String, SmtValue>>, GroundDerivationError> {
    cache
        .charge_step_reuse_with_control(clause_index, control)
        .map_err(surface_error)?;
    let mut env = FxHashMap::default();
    if let Some((arguments, values)) = body {
        if arguments.len() != values.len() {
            return Ok(None);
        }
        for (argument, value) in arguments.iter().zip(values) {
            control.poll()?;
            let ChcExpr::Var(variable) = argument else {
                return Ok(None);
            };
            // Existing finite profile precedes recursive sort checking/copy.
            cache
                .charge(
                    ground_value_storage_profile(value)
                        .map_err(surface_error)?
                        .0,
                )
                .map_err(surface_error)?;
            control.poll()?;
            if !canonical_ground_value_matches_sort(value, &variable.sort) {
                return Ok(None);
            }
            control.poll()?;
            if let Some(previous) = env.get(&variable.name) {
                // Representation equality is conservative for differently
                // represented extensional arrays; it can only lose a candidate.
                if previous != value {
                    return Ok(None);
                }
                control.poll()?;
            } else {
                cache
                    .charge(
                        variable
                            .name
                            .len()
                            .checked_add(1)
                            .ok_or(GroundDerivationError::SourceWorkLimitExceeded)?,
                    )
                    .map_err(surface_error)?;
                env.try_reserve(1)
                    .map_err(|_| GroundDerivationError::SourceWorkLimitExceeded)?;
                control.poll()?;
                env.insert(variable.name.clone(), value.clone());
                control.poll()?;
            }
        }
    }
    let surface = cache
        .surface_with_control(clause_index, control)
        .map_err(surface_error)?;
    if !surface.uf_applications.is_empty() || surface.variables.len() != env.len() {
        return Ok(None);
    }
    for variable in &surface.variables {
        control.poll()?;
        let Some(value) = env.get(&variable.name) else {
            return Ok(None);
        };
        if !canonical_ground_value_matches_sort(value, &variable.sort) {
            return Ok(None);
        }
        control.poll()?;
    }
    Ok(Some(env))
}

pub(super) fn enabled(
    clause_index: usize,
    clause: &HornClause,
    env: &FxHashMap<String, SmtValue>,
    cache: &mut GroundSourceSurfaceCache<'_>,
    control: &mut GroundValidationControl<'_>,
) -> Result<bool, GroundDerivationError> {
    control.poll()?;
    cache
        .charge_step_scalar_replay(clause_index, env, &[])
        .map_err(surface_error)?;
    control.poll()?;
    match &clause.body.constraint {
        None => Ok(true),
        Some(constraint) => Ok(matches!(
            eval_ground_with_control(constraint, env, control)?,
            Some(SmtValue::Bool(true))
        )),
    }
}

pub(super) fn head(
    problem: &ChcProblem,
    predicate: PredicateId,
    arguments: &[ChcExpr],
    env: &FxHashMap<String, SmtValue>,
    cache: &mut GroundSourceSurfaceCache<'_>,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<Vec<SmtValue>>, GroundDerivationError> {
    let Some(declaration) = problem.predicates().get(predicate.index()) else {
        return Ok(None);
    };
    if declaration.id != predicate || declaration.arg_sorts.len() != arguments.len() {
        return Ok(None);
    }
    cache.charge(arguments.len()).map_err(surface_error)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(arguments.len())
        .map_err(|_| GroundDerivationError::SourceWorkLimitExceeded)?;
    for (argument, sort) in arguments.iter().zip(&declaration.arg_sorts) {
        control.poll()?;
        let Some(value) = eval_ground_with_control(argument, env, control)? else {
            return Ok(None);
        };
        cache
            .charge(
                ground_value_storage_profile(&value)
                    .map_err(surface_error)?
                    .0,
            )
            .map_err(surface_error)?;
        control.poll()?;
        if !canonical_ground_value_matches_sort(&value, sort) {
            return Ok(None);
        }
        control.poll()?;
        values.push(value);
    }
    Ok(Some(values))
}
