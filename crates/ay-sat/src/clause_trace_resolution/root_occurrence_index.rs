// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Preserve the existing representation-only no-index fallback. Resource
/// errors after an index is admitted are terminal, not another fallback.
fn dimensions(num_vars: usize, clauses: usize, literals: usize) -> Option<usize> {
    u32::try_from(clauses).ok()?;
    u32::try_from(literals).ok()?;
    num_vars.checked_mul(2)?.checked_add(1)
}

pub(super) fn planned_bytes(
    num_vars: usize,
    clauses: usize,
    literals: usize,
) -> Result<usize, ResolutionValidationError> {
    let Some(codes) = dimensions(num_vars, clauses, literals) else {
        return Ok(0);
    };
    bytes(codes, literals, codes)
}

/// The heads and items survive the build; the equally sized cursor is live
/// alongside both while filling the CSR and may then become row-retirement
/// scratch. This same three-Vec capacity/header allowance remains reserved
/// across later repair lanes (including candidate scheduling), not replay.
fn bytes(heads: usize, items: usize, cursor: usize) -> Result<usize, ResolutionValidationError> {
    let slots = checked_resource_add(
        checked_resource_add(heads, items, ResolutionValidationResource::Bytes)?,
        cursor,
        ResolutionValidationResource::Bytes,
    )?;
    checked_resource_add(
        checked_resource_mul(slots, size_of::<u32>(), ResolutionValidationResource::Bytes)?,
        checked_resource_mul(
            3,
            size_of::<Vec<u32>>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )
}

fn check_capacities(
    heads: usize,
    items: usize,
    cursor: usize,
    admitted: usize,
) -> Result<(), ResolutionValidationError> {
    enforce_resource(
        ResolutionValidationResource::Bytes,
        bytes(heads, items, cursor)?,
        admitted,
    )
}

/// Restrict indexing to the completed root assignment. Rooted repair only
/// extends it: opposed targets use full synthesis, and cleanup retracts only
/// row-local assignments. The original clauses and root reasons stay intact.
fn root_clause_is_active(
    id: u64,
    clause: &[Literal],
    assign: &[Option<bool>],
    num_vars: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<bool, ResolutionValidationError> {
    meter.charge(1)?;
    let mut satisfied = false;
    for &literal in clause {
        meter.charge(1)?;
        let variable = literal.variable().index();
        let value = assign.get(variable).filter(|_| variable < num_vars).ok_or(
            ResolutionDagValidateError::VarOutOfRange {
                clause: id,
                var: variable,
                num_vars: num_vars.min(assign.len()),
            },
        )?;
        satisfied |= value.is_some_and(|value| value == literal.is_positive());
    }
    // Do not stop at a satisfying literal: even an omitted clause must have
    // valid literal indices before the index can be published.
    Ok(!satisfied)
}

pub(super) fn build(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    num_vars: usize,
    admitted_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    meter.check_controls()?;
    let mut total_literals = 0usize;
    for (_, clause) in original_clauses {
        meter.charge(1)?;
        total_literals = checked_resource_add(
            total_literals,
            clause.len(),
            ResolutionValidationResource::OriginalLiterals,
        )?;
    }
    let Some(code_count) = dimensions(num_vars, original_clauses.len(), total_literals) else {
        return Ok(());
    };
    // Check the whole future peak before allocation. After each reservation,
    // substitute its actual capacity while still including pending buffers.
    check_capacities(code_count, total_literals, code_count, admitted_bytes)?;
    let mut heads: Vec<u32> = Vec::new();
    reserve_exact(
        &mut heads,
        code_count,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    check_capacities(heads.capacity(), total_literals, code_count, admitted_bytes)?;
    let mut filled = 0usize;
    while filled < code_count {
        let chunk = (code_count - filled).min(CONTROL_POLL_INTERVAL);
        meter.charge(chunk)?;
        filled += chunk;
        heads.resize(filled, 0);
    }
    for (id, clause) in original_clauses {
        if !root_clause_is_active(*id, clause, &root.assign, num_vars, meter)? {
            continue;
        }
        for &literal in clause {
            meter.charge(1)?;
            let variable = literal.variable().index();
            if root.assign[variable].is_none() {
                heads[literal_code(variable, literal.is_positive())] += 1;
            }
        }
    }
    let mut running = 0u32;
    for head in heads.iter_mut() {
        meter.charge(1)?;
        let count = *head;
        *head = running;
        running = running.saturating_add(count);
    }
    let indexed_literals = running as usize;
    let mut items: Vec<u32> = Vec::new();
    reserve_exact(
        &mut items,
        indexed_literals,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    check_capacities(
        heads.capacity(),
        items.capacity(),
        code_count,
        admitted_bytes,
    )?;
    let mut fill = 0usize;
    while fill < indexed_literals {
        let chunk = (indexed_literals - fill).min(CONTROL_POLL_INTERVAL);
        meter.charge(chunk)?;
        fill += chunk;
        items.resize(fill, 0);
    }
    let mut cursor: Vec<u32> = Vec::new();
    reserve_exact(
        &mut cursor,
        heads.len(),
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    check_capacities(
        heads.capacity(),
        items.capacity(),
        cursor.capacity(),
        admitted_bytes,
    )?;
    meter.charge(heads.len())?;
    cursor.extend_from_slice(&heads);
    for (position, (id, clause)) in original_clauses.iter().enumerate() {
        if !root_clause_is_active(*id, clause, &root.assign, num_vars, meter)? {
            continue;
        }
        for &literal in clause {
            meter.charge(1)?;
            let variable = literal.variable().index();
            if root.assign[variable].is_some() {
                continue;
            }
            let code = literal_code(variable, literal.is_positive());
            items[cursor[code] as usize] = position as u32;
            cursor[code] += 1;
        }
    }
    let retired =
        rooted_retirement::RetiredOriginals::from_cursor(cursor, original_clauses.len(), meter)?;
    // Cursor initialization and its final control poll finish before any index
    // state is published. No partial index escapes resource/cancel refusal.
    meter.check_controls()?;
    // heads[code]..heads[code + 1] is the bucket for that literal;
    // the extra trailing slot is the total-occurrence sentinel.
    root.index_heads = Some(heads);
    root.index_items = items;
    root.index_retired = retired;
    Ok(())
}

#[cfg(test)]
mod tests;
