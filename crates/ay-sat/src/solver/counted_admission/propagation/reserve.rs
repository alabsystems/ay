// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::watched::counted::reserve_vec;

/// Reserve only storage reachable from this watch transaction. The source
/// list's restoration cannot grow: SEARCH adds no HBR overflow to that list.
pub(super) fn buffers(
    solver: &mut Solver,
    owner: &CountedAdmission,
    false_lit: Literal,
    watch_len: usize,
    tail_bound: usize,
) -> Result<(), SatUnknownReason> {
    let mut destinations = Vec::new();
    reserve_vec(&mut destinations, tail_bound, owner).map_err(reason)?;
    for index in 0..watch_len {
        owner.admit(1, 0).map_err(reason)?;
        let entry = solver.watches.entry_raw(false_lit, index);
        if watched::entry_is_binary(entry) {
            continue;
        }
        let offset = watched::entry_clause_off(entry) as usize;
        if solver.arena.bcp_header(offset).is_garbage_any() {
            continue;
        }
        for literal in &solver.arena.literals(offset)[2..] {
            owner.admit(1, 0).map_err(reason)?;
            // Already-false literals stay false throughout this transaction.
            // Every other tail occurrence is a possible replacement target.
            if solver.lit_val(*literal) >= 0 {
                destinations.push(*literal);
            }
        }
    }
    sort_destinations(&mut destinations, owner)?;
    solver
        .watches
        .reserve_counted_replacements(&destinations, owner)
        .map_err(reason)?;
    solver
        .deferred_watch_list
        .reserve_counted(watch_len, owner)
        .map_err(reason)?;
    reserve_vec(&mut solver.deferred_replacement_watches, watch_len, owner).map_err(reason)?;
    let trail_bound = solver
        .trail
        .len()
        .checked_add(watch_len)
        .ok_or_else(|| reason(owner.refuse(CountedAdmissionError::StorageExhausted)))?
        .min(solver.num_vars);
    reserve_vec(&mut solver.trail, trail_bound, owner).map_err(reason)?;
    owner.check().map_err(reason)
}

/// In-place heapsort (Williams, CACM 1964, Algorithm 232). Every comparison and
/// swap is admitted directly, without relying on a library-sort cost constant.
/// Refusal may leave this private scratch unordered; no solver state is changed.
fn sort_destinations(
    values: &mut [Literal],
    owner: &CountedAdmission,
) -> Result<(), SatUnknownReason> {
    let len = values.len();
    for root in (0..len / 2).rev() {
        sift(values, root, len, owner)?;
    }
    for end in (1..len).rev() {
        owner.admit(1, 0).map_err(reason)?;
        values.swap(0, end);
        sift(values, 0, end, owner)?;
    }
    owner.check().map_err(reason)
}

fn sift(
    values: &mut [Literal],
    mut root: usize,
    end: usize,
    owner: &CountedAdmission,
) -> Result<(), SatUnknownReason> {
    loop {
        owner.admit(1, 0).map_err(reason)?;
        let Some(mut child) = root
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .filter(|child| *child < end)
        else {
            return Ok(());
        };
        if child + 1 < end {
            owner.admit(1, 0).map_err(reason)?;
            if values[child] < values[child + 1] {
                child += 1;
            }
        }
        owner.admit(1, 0).map_err(reason)?;
        if values[root] >= values[child] {
            return Ok(());
        }
        owner.admit(1, 0).map_err(reason)?;
        values.swap(root, child);
        root = child;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::FiniteAdmissionGrant;
    use std::sync::Arc;

    #[test]
    fn counted_heap_sort_preserves_duplicates_and_has_an_exact_work_boundary() {
        let input = [19, 2, 13, 0, 13, 19, 7, 1, 4, 7].map(Literal);
        let mut expected = input;
        expected.sort_unstable();
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(10_000, 0),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let mut baseline = input;
        sort_destinations(&mut baseline, &owner).unwrap();
        assert_eq!(baseline, expected);
        let used = owner.usage().unwrap().work_admitted;
        for grant in [used - 1, used] {
            let owner = CountedAdmission::new(
                FiniteAdmissionGrant::new(grant, 0),
                None,
                Arc::new(|| false),
            )
            .unwrap();
            let mut values = input;
            let result = sort_destinations(&mut values, &owner);
            if grant == used {
                assert_eq!(result, Ok(()));
                assert_eq!(values, expected);
            } else {
                assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
                assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
            }
        }
    }
}
