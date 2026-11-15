// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// Legacy clear() retains bucket backing and clears all control bytes. Restore
// that exact EMPTY shape before ordered replay; do not copy borrowed payloads.
pub(super) fn restore(
    source: &ArraySolver<'_>,
    view: &mut ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    map(&source.select_cache, &mut view.select_cache, work)?;
    map(&source.select_pair_index, &mut view.select_pair_index, work)?;
    map(&source.const_array_cache, &mut view.const_array_cache, work)?;
    map(&source.default_cache, &mut view.default_cache, work)?;
    map(&source.equality_cache, &mut view.equality_cache, work)?;
    map(
        &source.term_to_equalities,
        &mut view.term_to_equalities,
        work,
    )?;
    map(&source.eq_pair_index, &mut view.eq_pair_index, work)?;
    map(&source.array_vars, &mut view.array_vars, work)
}

fn map<K: maps::Key, V>(
    source: &HashMap<K, V>,
    target: &mut HashMap<K, V>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    maps::layout::<K, V>(work)?;
    work.charge(16)?;
    let capacity = source.capacity();
    owned::reserve_table::<(K, V)>(capacity, work)?;
    target
        .try_reserve(capacity)
        .map_err(|_| work.refuse_exhaustion())?;
    // Identical T and pinned Group/Layout make allocation_size strictly
    // increasing with power-of-two buckets. Same bytes => same bucket count.
    // Tombstones can reduce capacity() below the retained allocation: if the
    // fresh reservation does not recreate it exactly, refuse, never reorder.
    work.charge(1)?;
    if target.allocation_size() != source.allocation_size() {
        return Err(work.refuse_exhaustion());
    }
    work.charge(0)
}
