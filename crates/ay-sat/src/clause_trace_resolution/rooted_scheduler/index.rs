// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn build(
    num_vars: usize,
    originals: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    candidates: &[u64],
    admitted: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<(Vec<usize>, Vec<usize>, usize)>, ResolutionValidationError> {
    let mut literals = 0;
    for &id in candidates {
        meter.charge(1)?;
        let Some(clause) = prior_clause_by_id(originals, derived, id) else {
            return Ok(None);
        };
        literals =
            checked_resource_add(literals, clause.len(), ResolutionValidationResource::Bytes)?;
    }
    let codes = checked_resource_add(
        checked_resource_mul(num_vars, 2, ResolutionValidationResource::Bytes)?,
        1,
        ResolutionValidationResource::Bytes,
    )?;
    let count = candidates.len();
    let mut capacities = [codes, literals, count, count, count, codes];
    Scheduler::check_capacities(capacities, admitted)?;
    let mut heads = Vec::new();
    reserve_exact(
        &mut heads,
        codes,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    capacities[0] = heads.capacity();
    Scheduler::check_capacities(capacities, admitted)?;
    zero_fill(&mut heads, codes, meter)?;
    for &id in candidates {
        meter.charge(1)?;
        let Some(clause) = prior_clause_by_id(originals, derived, id) else {
            return Ok(None);
        };
        for &literal in clause {
            meter.charge(1)?;
            let variable = literal.variable().index();
            if variable >= num_vars {
                return Err(ResolutionDagValidateError::VarOutOfRange {
                    clause: id,
                    var: variable,
                    num_vars,
                }
                .into());
            }
            let code = literal_code(variable, literal.is_positive());
            heads[code] =
                checked_resource_add(heads[code], 1, ResolutionValidationResource::Bytes)?;
        }
    }
    let mut running = 0usize;
    for head in &mut heads {
        meter.charge(1)?;
        let count = *head;
        *head = running;
        running = checked_resource_add(running, count, ResolutionValidationResource::Bytes)?;
    }
    let mut items = Vec::new();
    reserve_exact(
        &mut items,
        literals,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    capacities[1] = items.capacity();
    Scheduler::check_capacities(capacities, admitted)?;
    zero_fill(&mut items, literals, meter)?;
    let mut cursor = Vec::new();
    reserve_exact(
        &mut cursor,
        codes,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    capacities[5] = cursor.capacity();
    Scheduler::check_capacities(capacities, admitted)?;
    for chunk in heads.chunks(CONTROL_POLL_INTERVAL) {
        meter.charge(chunk.len())?;
        cursor.extend_from_slice(chunk);
    }
    for (position, &id) in candidates.iter().enumerate() {
        meter.charge(1)?;
        let Some(clause) = prior_clause_by_id(originals, derived, id) else {
            return Ok(None);
        };
        for &literal in clause {
            meter.charge(1)?;
            let code = literal_code(literal.variable().index(), literal.is_positive());
            items[cursor[code]] = position;
            cursor[code] += 1;
        }
    }
    meter.check_controls()?;
    Ok(Some((heads, items, cursor.capacity())))
}

fn zero_fill(
    values: &mut Vec<usize>,
    len: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    while values.len() < len {
        let count = (len - values.len()).min(CONTROL_POLL_INTERVAL);
        meter.charge(count)?;
        values.resize(values.len() + count, 0);
    }
    Ok(())
}
