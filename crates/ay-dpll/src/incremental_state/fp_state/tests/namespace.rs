// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const LIMIT: u32 = i32::MAX as u32;
const REFUSAL: UnknownOrigin = UnknownOrigin::DeterministicResourceBudget;

fn counters(state: &IncrementalFpState) -> (u32, u32, u32, Option<i32>) {
    (
        state.tseitin_state.next_var,
        state.next_fp_var,
        state.fp_cache.next_var,
        state.fp_var_offset,
    )
}

#[test]
fn combined_frontier_and_selector_boundaries_need_no_large_allocation() {
    let mut state = IncrementalFpState::new();
    assert_eq!(state.checked_total_vars(0, 0), Ok(0));
    state.fp_var_offset = Some((LIMIT - 3) as i32);
    state.next_fp_var = 4;
    state.fp_cache.next_var = 4;
    state.tseitin_state.next_var = LIMIT + 1;
    assert_eq!(state.checked_total_vars(0, 0), Ok(LIMIT as usize));
    assert_eq!(state.checked_total_vars(0, 1), Err(REFUSAL));
    state.sync_with_solver_total(LIMIT as usize).unwrap();
    assert_eq!(
        counters(&state),
        (LIMIT + 1, 4, 4, Some((LIMIT - 3) as i32))
    );
    let before = counters(&state);
    assert_eq!(
        state.sync_with_solver_total(LIMIT as usize + 1),
        Err(REFUSAL)
    );
    assert_eq!(state.sync_with_solver_total(usize::MAX), Err(REFUSAL));
    assert_eq!(state.checked_total_vars(0, usize::MAX), Err(REFUSAL));
    assert_eq!(counters(&state), before);
}

#[test]
fn zero_negative_and_overwide_frontiers_refuse_without_mutating_mirrors() {
    for case in 0..6 {
        let mut state = IncrementalFpState::new();
        match case {
            0 => state.tseitin_state.next_var = 0,
            1 => state.next_fp_var = 0,
            2 => state.fp_cache.next_var = 0,
            3 => state.fp_var_offset = Some(-1),
            4 => state.tseitin_state.next_var = LIMIT + 2,
            _ => {
                state.fp_var_offset = Some(1);
                state.fp_cache.next_var = LIMIT + 1;
            }
        }
        let before = counters(&state);
        assert_eq!(state.checked_total_vars(0, 0), Err(REFUSAL));
        assert_eq!(state.sync_tseitin_next_var(), Err(REFUSAL));
        assert_eq!(state.sync_next_fp_var(), Err(REFUSAL));
        assert_eq!(state.sync_with_solver_total(3), Err(REFUSAL));
        assert_eq!(counters(&state), before);
    }
}

#[test]
fn fixed_offset_sync_is_tight_and_honors_the_larger_imported_cache() {
    let mut state = IncrementalFpState::new();
    state.fp_var_offset = Some(8);
    state.tseitin_state.next_var = 20;
    state.next_fp_var = 3;
    state.fp_cache.next_var = 7;
    assert_eq!(state.checked_total_vars(0, 0), Ok(19));
    state.sync_tseitin_next_var().unwrap();
    state.sync_next_fp_var().unwrap();
    assert_eq!(counters(&state), (20, 12, 12, Some(8)));
    for _ in 0..4 {
        state.sync_tseitin_next_var().unwrap();
        state.sync_next_fp_var().unwrap();
        assert_eq!(counters(&state), (20, 12, 12, Some(8)));
    }
    state.fp_cache.next_var = 15;
    state.sync_tseitin_next_var().unwrap();
    state.sync_next_fp_var().unwrap();
    assert_eq!(counters(&state), (23, 15, 15, Some(8)));
    assert_eq!(state.checked_total_vars(0, 2), Ok(24));
}

#[test]
fn owned_and_detached_solver_selectors_both_advance_the_namespace() {
    let mut state = IncrementalFpState::new();
    state.fp_var_offset = Some(2);
    state.persistent_sat = Some(SatSolver::new(4));
    state.push();
    assert_eq!(state.persistent_sat.as_ref().unwrap().total_num_vars(), 5);
    assert_eq!(state.checked_total_vars(0, 0), Ok(5));
    state.sync_tseitin_next_var().unwrap();
    state.sync_next_fp_var().unwrap();
    assert_eq!(counters(&state), (6, 4, 4, Some(2)));
    let mut solver = state.persistent_sat.take().unwrap();
    solver.push();
    state
        .sync_with_solver_total(solver.total_num_vars())
        .unwrap();
    assert_eq!(counters(&state), (7, 5, 5, Some(2)));
    assert_eq!(state.checked_total_vars(solver.total_num_vars(), 0), Ok(6));
}
