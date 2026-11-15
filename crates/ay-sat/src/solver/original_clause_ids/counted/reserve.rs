// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::CountedAdmissionError;

pub(super) fn row(
    solver: &mut Solver,
    len: usize,
    owner: &CountedAdmission,
) -> Result<Option<usize>> {
    registration(solver, len, owner)?;
    if len == 0 {
        return Ok(None);
    }
    let offset = solver.arena.reserve_original_counted(len, owner)?;
    clause_ids(solver, offset, owner)?;
    owner.admit((offset + 1).saturating_sub(solver.cold.clause_ids.len()), 0)?;
    solver.provenance.reserve_tag_counted(offset, owner)?;
    Ok(Some(offset))
}

fn clause_ids(solver: &mut Solver, offset: usize, owner: &CountedAdmission) -> Result<()> {
    // Preserve the ordinary hint/capacity schedule: it feeds reduction policy.
    if solver.cold.clause_ids.capacity() == 0 && solver.cold.clause_ids_reserve_hint > 0 {
        solver.cold.clause_ids = try_reserved_exact(owner, solver.cold.clause_ids_reserve_hint)?;
    }
    let additional = (offset + 1).saturating_sub(solver.cold.clause_ids.len());
    crate::counted_storage::try_reserve(owner, &mut solver.cold.clause_ids, additional)
}

pub(super) fn identity(solver: &mut Solver, owner: &CountedAdmission) -> Result<()> {
    owner.admit(1, 0)?;
    let id = solver
        .cold
        .next_clause_id
        .max(solver.cold.next_original_clause_id);
    let required = usize::try_from(id)
        .ok()
        .filter(|_| id < u64::MAX)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let additional = required.saturating_sub(solver.cold.original_clause_id_bits.len());
    crate::counted_storage::try_reserve(
        owner,
        &mut solver.cold.original_clause_id_bits,
        additional,
    )?;
    owner.admit(
        required.saturating_sub(solver.cold.original_clause_id_bits.len()),
        0,
    )?;
    owner.admit(32, 0)
}

fn registration(solver: &mut Solver, len: usize, owner: &CountedAdmission) -> Result<()> {
    identity(solver, owner)?;
    solver
        .cold
        .original_ledger
        .reserve_original_counted(len, owner)?;
    // Shared original allocation, ledger append, bounds/debug scans, factor /
    // subsume marks, arena headers, provenance and constant trace-state gates.
    let work = len
        .checked_mul(16)
        .and_then(|n| n.checked_add(128))
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, 0)
}
