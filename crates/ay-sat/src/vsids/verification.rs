// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for VSIDS heap invariants.
//!
//! Proves: max-heap property after bump/insert/remove, position map
//! consistency, and pick_branching_variable correctness.

use super::*;

/// Helper: verify max-heap property holds for the entire heap.
/// Every child's priority must be <= its parent's priority.
fn assert_max_heap_property(vsids: &VSIDS) {
    for pos in 1..vsids.heap.len() {
        let parent = (pos - 1) / 2;
        let var = vsids.heap[pos] as usize;
        let parent_var = vsids.heap[parent] as usize;
        // var_less(a, b) returns true if a has higher priority than b.
        // Parent must have >= priority (i.e. child must NOT have higher priority).
        assert!(
            !vsids.var_less(var, parent_var),
            "Heap property violated: child var {var} at pos {pos} has higher \
             priority than parent var {parent_var} at pos {parent}"
        );
    }
}

/// Helper: verify position map is consistent with heap contents.
fn assert_position_map_consistent(vsids: &VSIDS) {
    for (pos, &var_idx) in vsids.heap.iter().enumerate() {
        assert_eq!(
            vsids.heap_pos[var_idx as usize], pos as u32,
            "Position map inconsistent: heap[{pos}] = {var_idx} but heap_pos[{var_idx}] = {}",
            vsids.heap_pos[var_idx as usize]
        );
    }
    // Every variable not in the heap must have INVALID_POS.
    for (var, &pos) in vsids.heap_pos.iter().enumerate() {
        if pos != INVALID_POS {
            assert!(
                (pos as usize) < vsids.heap.len(),
                "Position map out of bounds: heap_pos[{var}] = {pos} but heap.len() = {}",
                vsids.heap.len()
            );
            assert_eq!(
                vsids.heap[pos as usize], var as u32,
                "Position map reverse inconsistent: heap_pos[{var}] = {pos} but heap[{pos}] = {}",
                vsids.heap[pos as usize]
            );
        }
    }
}

/// Prove that VSIDS::new creates a valid max-heap with consistent position map.
///
/// Invariant: After construction, the heap contains all variables and the
/// max-heap property holds. This is the base case for all heap invariants.
#[kani::proof]
#[kani::unwind(12)]
fn proof_vsids_new_valid_heap() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars > 0 && num_vars <= 5);

    let vsids = VSIDS::new(num_vars);

    // All variables must be in the heap
    assert_eq!(vsids.heap.len(), num_vars);

    // Heap property must hold
    assert_max_heap_property(&vsids);

    // Position map must be consistent
    assert_position_map_consistent(&vsids);
}

/// Prove that bump_score preserves the max-heap property.
///
/// Invariant: After bumping a symbolic variable's activity, the heap
/// still satisfies the max-heap property and the position map is consistent.
/// This is the core inductive step for VSIDS correctness.
///
/// Reference: CaDiCaL analyze.cpp:105-125 (bump_variable_score).
#[kani::proof]
#[kani::unwind(12)]
fn proof_vsids_bump_preserves_heap() {
    const NUM_VARS: usize = 4;
    let mut vsids = VSIDS::new(NUM_VARS);

    // Bump a symbolic variable
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < NUM_VARS as u32);

    vsids.bump_score(Variable(var_idx));

    // Heap property must still hold
    assert_max_heap_property(&vsids);
    assert_position_map_consistent(&vsids);

    // The bumped variable's activity must be > 0
    assert!(
        vsids.activities[var_idx as usize] > 0.0,
        "Bumped variable must have positive activity"
    );
}

/// Prove that remove_from_heap + insert_into_heap preserves heap invariants.
///
/// Invariant: After removing a variable from the heap and re-inserting it,
/// the max-heap property and position map consistency are maintained.
/// This sequence occurs during decide (remove) and backtrack (re-insert).
#[kani::proof]
#[kani::unwind(12)]
fn proof_vsids_remove_insert_roundtrip() {
    const NUM_VARS: usize = 4;
    let mut vsids = VSIDS::new(NUM_VARS);

    // Bump some variables to create non-trivial heap ordering
    vsids.bump_score(Variable(2));
    vsids.bump_score(Variable(2));
    vsids.bump_score(Variable(1));

    // Remove a symbolic variable
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < NUM_VARS as u32);

    vsids.remove_from_heap(Variable(var_idx));

    // After removal: heap still valid, variable not in heap
    assert_max_heap_property(&vsids);
    assert_position_map_consistent(&vsids);
    assert_eq!(
        vsids.heap_pos[var_idx as usize], INVALID_POS,
        "Removed variable must not be in heap"
    );

    // Re-insert
    vsids.insert_into_heap(Variable(var_idx));

    // After re-insert: heap valid, variable back in heap
    assert_max_heap_property(&vsids);
    assert_position_map_consistent(&vsids);
    assert_ne!(
        vsids.heap_pos[var_idx as usize], INVALID_POS,
        "Re-inserted variable must be in heap"
    );
}

/// Prove that pick_branching_variable returns the highest-activity unassigned variable.
///
/// Invariant: The variable returned by pick_branching_variable has an activity
/// >= all other unassigned variables in the heap. This is the fundamental
/// correctness property of VSIDS decision heuristic.
#[kani::proof]
#[kani::unwind(12)]
fn proof_vsids_pick_returns_max_activity() {
    const NUM_VARS: usize = 4;
    let mut vsids = VSIDS::new(NUM_VARS);

    // Bump variables with different frequencies to create distinct activities
    vsids.bump_score(Variable(0));
    vsids.bump_score(Variable(1));
    vsids.bump_score(Variable(1));
    vsids.bump_score(Variable(2));
    vsids.bump_score(Variable(2));
    vsids.bump_score(Variable(2));

    // All variables unassigned
    let vals = vec![0i8; NUM_VARS * 2];

    let picked = vsids.pick_branching_variable(&vals);
    assert!(
        picked.is_some(),
        "Must pick a variable when all are unassigned"
    );

    let picked_var = picked.unwrap();
    let picked_activity = vsids.activities[picked_var.index()];

    // The picked variable must have the highest activity among all unassigned
    for v in 0..NUM_VARS {
        if vals[v * 2] == 0 {
            // Variable v is unassigned
            assert!(
                picked_activity >= vsids.activities[v]
                    || (picked_activity == vsids.activities[v] && picked_var.index() <= v),
                "Picked var {} (activity={}) but unassigned var {} has higher activity ({})",
                picked_var.index(),
                picked_activity,
                v,
                vsids.activities[v]
            );
        }
    }

    // Heap invariants still hold after pick
    assert_max_heap_property(&vsids);
}

/// Prove that multiple bumps followed by decay preserves heap invariants.
///
/// Invariant: After a sequence of bumps and a decay, the relative ordering
/// of activities is preserved (decay is a uniform scaling), and the heap
/// property holds.
#[kani::proof]
#[kani::unwind(12)]
fn proof_vsids_bump_decay_preserves_ordering() {
    const NUM_VARS: usize = 4;
    let mut vsids = VSIDS::new(NUM_VARS);

    // Bump var 0 once, var 1 twice
    vsids.bump_score(Variable(0));
    vsids.bump_score(Variable(1));
    vsids.bump_score(Variable(1));

    let activity_0_before = vsids.activities[0];
    let activity_1_before = vsids.activities[1];

    // var 1 should have higher activity before decay
    assert!(activity_1_before > activity_0_before);

    // Decay
    vsids.decay();

    // After decay, relative ordering is preserved (both scaled equally)
    // Var 1 should still have higher activity than var 0
    assert!(
        vsids.activities[1] > vsids.activities[0],
        "Decay must preserve relative ordering"
    );

    // Heap property must hold after decay
    assert_max_heap_property(&vsids);
    assert_position_map_consistent(&vsids);
}
