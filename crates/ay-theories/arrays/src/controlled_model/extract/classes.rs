// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordered, already-current, store-free class DATA. No cache preparation.

use super::*;

mod complete;
mod order;
mod propagate;

pub(super) struct Plan {
    pub(super) members: Vec<TermId>,
    pub(super) ends: Vec<usize>,
}

pub(super) fn prepare(
    solver: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<Plan, QueryError> {
    work.charge(16)?;
    if solver.dirty
        || solver.var_layer_dirty
        || solver.assign_dirty
        || solver.shadow_uf_stale
        || solver.populated_terms != solver.terms.len()
        || !solver.pending_registered_equalities.is_empty()
        || !solver.store_cache.is_empty()
        || solver.array_var_merge_undo.len() != solver.array_var_merge_log.len()
    {
        return Err(work.refuse_exhaustion());
    }
    // Nonempty merge history is completed state, not permission to replay it.
    // Warm assignment/structural flags and parallel undo parity are mandatory.
    order::prepare(solver, work)
}

impl Plan {
    pub(super) fn additional_entries(&self) -> usize {
        self.members.len()
    }

    pub(super) fn propagate(
        &self,
        solver: &ArraySolver<'_>,
        output: &mut ArrayModel,
        buckets: usize,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        propagate::apply(self, solver, output, buckets, work)
    }

    pub(super) fn finish(self, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
        let visits = owned::checked(self.members.len().checked_add(self.ends.len()), work)?;
        work.charge(visits)?;
        drop(self);
        work.charge(0)
    }
}

fn scalar(source: &Sort, work: &mut WorkBudget<'_>) -> Result<(u8, u32), QueryError> {
    work.charge(1)?;
    match source {
        Sort::Bool => Ok((0, 0)),
        Sort::Int => Ok((1, 0)),
        Sort::Real => Ok((2, 0)),
        Sort::BitVec(value) if (1..=128).contains(&value.width) => Ok((3, value.width)),
        _ => Err(work.refuse_exhaustion()),
    }
}

fn signature(
    solver: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<((u8, u32), (u8, u32)), QueryError> {
    scan::live(solver, term, work)?;
    let Sort::Array(sort) = solver.terms.sort(term) else {
        return Err(work.refuse_exhaustion());
    };
    Ok((
        scalar(&sort.index_sort, work)?,
        scalar(&sort.element_sort, work)?,
    ))
}

// The complete sibling validates the flat, current source before this census.
// Existing store-free preparation/refusal semantics remain unchanged.
pub(super) fn prepare_reconciled(
    solver: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<Plan, QueryError> {
    complete::prepare(solver, work)
}
