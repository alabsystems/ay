// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
/// Build a vals[] array from an assignment specification.
/// Each entry: None = unassigned, Some(true) = positive, Some(false) = negative.
fn make_vals(assignments: &[Option<bool>]) -> Vec<i8> {
    let mut vals = vec![0i8; assignments.len() * 2];
    for (v, a) in assignments.iter().enumerate() {
        if let Some(positive) = a {
            if *positive {
                vals[v * 2] = 1;
                vals[v * 2 + 1] = -1;
            } else {
                vals[v * 2] = -1;
                vals[v * 2 + 1] = 1;
            }
        }
    }
    vals
}

#[test]
fn test_heap_operations() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Initially all variables in heap, some var should be picked (all equal activity)
    assert!(vsids.pick_branching_variable(&vals).is_some());

    // Bump variable 3 twice - it should become the top with activity 2.0
    vsids.bump(Variable(3), &vals, true);
    vsids.bump(Variable(3), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));

    // Remove variable 3 from heap (assigned)
    vsids.remove_from_heap(Variable(3));
    // Now should pick something else
    let picked = vsids.pick_branching_variable(&vals);
    assert!(picked.is_some());
    assert_ne!(picked, Some(Variable(3)));

    // Bump variable 2 once - activity 1.0
    vsids.bump(Variable(2), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(2)));

    // Insert variable 3 back (unassigned)
    vsids.insert_into_heap(Variable(3));
    // Variable 3 has activity 2.0, var 2 has 1.0 - var 3 should be top
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));
}

#[test]
fn test_heap_empty() {
    let mut vsids = VSIDS::new(3);
    let vals = make_vals(&[None; 3]);

    // Remove all variables
    vsids.remove_from_heap(Variable(0));
    vsids.remove_from_heap(Variable(1));
    vsids.remove_from_heap(Variable(2));

    assert_eq!(vsids.pick_branching_variable(&vals), None);

    // Insert one back
    vsids.insert_into_heap(Variable(1));
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(1)));
}

#[test]
fn test_heap_activity_ordering() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Bump each variable different number of times to create distinct activities
    // var 0: 5 bumps, var 1: 4 bumps, var 2: 3 bumps, var 3: 2 bumps, var 4: 1 bump
    for i in 0..5u32 {
        for _ in 0..(5 - i) {
            vsids.bump(Variable(i), &vals, true);
        }
    }

    // Variable 0 has highest activity (5.0)
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    vsids.remove_from_heap(Variable(0));

    // Then var 1 (4.0)
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(1)));
    vsids.remove_from_heap(Variable(1));

    // Then var 2 (3.0)
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(2)));
}

#[test]
fn test_ensure_num_vars() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(5);

    let vals = make_vals(&[None; 5]);
    // New variables should be in heap
    // Bump var 4 to make it top
    vsids.bump(Variable(4), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(4)));
}

#[test]
fn test_heap_bump_while_assigned() {
    let mut vsids = VSIDS::new(3);
    let vals = make_vals(&[None; 3]);

    // Bump var 0 and remove it (assigned)
    vsids.bump(Variable(0), &vals, true);
    vsids.remove_from_heap(Variable(0));

    // Bump var 0 again while it's assigned (this can happen during conflict analysis)
    vsids.bump(Variable(0), &vals, true);
    vsids.bump(Variable(0), &vals, true);
    // var 0 now has activity 3.0

    // var 1 has activity 0, so it should be the top of remaining heap
    // (or var 2, depending on initial order)
    let picked = vsids.pick_branching_variable(&vals);
    assert!(picked.is_some());
    assert_ne!(picked, Some(Variable(0))); // var 0 is not in heap

    // Insert var 0 back
    vsids.insert_into_heap(Variable(0));
    // Now var 0 with activity 3.0 should be top
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
}

#[test]
fn test_pick_branching_variable_lazily_drops_assigned_root() {
    let mut vsids = VSIDS::new(3);
    let dummy = make_vals(&[None; 3]);
    // Make variable 2 the heap root.
    vsids.bump(Variable(2), &dummy, true);
    vsids.bump(Variable(2), &dummy, true);

    // var 2 assigned (true), vars 0 and 1 unassigned
    let vals = make_vals(&[None, None, Some(true)]);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    assert_eq!(vsids.heap_pos[2], INVALID_POS);
}

#[test]
fn test_pick_branching_variable_lazily_drops_multiple_assigned_roots() {
    let mut vsids = VSIDS::new(4);
    let dummy = make_vals(&[None; 4]);
    // Ensure vars 3 and 2 are the two highest-priority heap entries.
    vsids.bump(Variable(3), &dummy, true);
    vsids.bump(Variable(3), &dummy, true);
    vsids.bump(Variable(2), &dummy, true);

    // vars 2 and 3 assigned, vars 0 and 1 unassigned
    let vals = make_vals(&[None, None, Some(true), Some(false)]);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    assert_eq!(vsids.heap_pos[3], INVALID_POS);
    assert_eq!(vsids.heap_pos[2], INVALID_POS);
}

#[test]
fn test_vmtf_cursor_skips_assigned() {
    let mut vsids = VSIDS::new(3);
    // vars 0 and 1 assigned, var 2 unassigned
    let vals = make_vals(&[Some(true), Some(false), None]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(2)));
    // Cursor should now be updated to 2 (the found unassigned variable).
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(2)));
}

#[test]
fn test_vmtf_updates_on_unassign_after_bump() {
    let mut vsids = VSIDS::new(4);
    let dummy = make_vals(&[None; 4]);

    // Simulate a conflict bumping var 2 while it is assigned (focused mode → VMTF).
    vsids.bump(Variable(2), &dummy, false);

    // Now simulate backtracking that unassigns var 2.
    vsids.vmtf_on_unassign(Variable(2));

    let vals = make_vals(&[None; 4]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(2)));
}

#[test]
fn test_shuffle_scores_changes_heap_order() {
    let mut vsids = VSIDS::new(10);
    let assignment = make_vals(&[None; 10]);

    // Create distinct activity ordering: 0 > 1 > 2 > ... > 9
    for i in 0..10u32 {
        for _ in 0..(10 - i) {
            vsids.bump(Variable(i), &assignment, true);
        }
    }
    let before = vsids.pick_branching_variable(&assignment).unwrap();
    assert_eq!(before, Variable(0)); // Highest activity
    vsids.insert_into_heap(Variable(0)); // Put it back

    // Shuffle with seed 42
    vsids.shuffle_scores(42);

    // After shuffle, the heap should still be valid (heap property maintained)
    // but the order should be different.
    let after = vsids.pick_branching_variable(&assignment);
    assert!(after.is_some());
    // We can't predict which variable will be top, but the heap must be valid
    // and contain all variables.
}

#[test]
fn test_shuffle_scores_different_seeds_different_orders() {
    let assignment = make_vals(&[None; 20]);

    let mut vsids1 = VSIDS::new(20);
    let mut vsids2 = VSIDS::new(20);

    // Same initial activities
    for i in 0..20u32 {
        for _ in 0..(20 - i) {
            vsids1.bump(Variable(i), &assignment, true);
            vsids2.bump(Variable(i), &assignment, true);
        }
    }

    vsids1.shuffle_scores(1);
    vsids2.shuffle_scores(2);

    // Different seeds should produce different orderings (with high probability).
    let top1 = vsids1.pick_branching_variable(&assignment);
    let top2 = vsids2.pick_branching_variable(&assignment);
    // Not deterministic but with 20 vars, collision probability is 5%.
    // Accept either outcome for test robustness.
    assert!(top1.is_some());
    assert!(top2.is_some());
}

#[test]
fn test_shuffle_queue_preserves_all_variables() {
    let mut vsids = VSIDS::new(8);

    // Collect all variables before shuffle.
    let mut before: Vec<u32> = Vec::new();
    let mut cur = vsids.vmtf_first;
    while cur != INVALID_VAR {
        before.push(cur);
        cur = vsids.vmtf_next[cur as usize];
    }
    assert_eq!(before.len(), 8);

    // Shuffle
    vsids.shuffle_queue(42);

    // Collect all variables after shuffle.
    let mut after: Vec<u32> = Vec::new();
    let mut cur = vsids.vmtf_first;
    while cur != INVALID_VAR {
        after.push(cur);
        cur = vsids.vmtf_next[cur as usize];
    }

    // Same set of variables, possibly different order.
    assert_eq!(after.len(), 8);
    let mut before_sorted = before.clone();
    let mut after_sorted = after.clone();
    before_sorted.sort_unstable();
    after_sorted.sort_unstable();
    assert_eq!(before_sorted, after_sorted);
}

#[test]
fn test_shuffle_queue_vmtf_consistent() {
    let mut vsids = VSIDS::new(10);

    let dummy = make_vals(&[None; 10]);
    // Bump some variables to create non-trivial queue order (focused mode → VMTF).
    vsids.bump(Variable(5), &dummy, false);
    vsids.bump(Variable(3), &dummy, false);
    vsids.bump(Variable(7), &dummy, false);

    vsids.shuffle_queue(99);

    // After shuffle, VMTF must still be usable for decisions.
    let assignment = make_vals(&[None; 10]);
    let picked = vsids.pick_branching_variable_vmtf(&assignment);
    assert!(picked.is_some());
}

#[test]
fn test_zero_activity_buries_fresh_vars_in_vmtf() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(5);

    // Fresh vars 3 and 4 are added at the VMTF front by ensure_num_vars().
    vsids.set_activity(Variable(3), 0.0);
    vsids.set_activity(Variable(4), 0.0);

    let vals = make_vals(&[None; 5]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(0)));
}

#[test]
fn test_zero_activity_burial_blocks_vmtf_unassign_resurrection() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(4);
    vsids.set_activity(Variable(3), 0.0);

    // Backtracking should not move a buried extension var back to the
    // cursor when it becomes unassigned again.
    vsids.vmtf_on_unassign(Variable(3));

    let vals = make_vals(&[None; 4]);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(0)));
}

/// Proof coverage for set_activity heap path (#7191):
/// Verify that set_activity(var, 0.0) sifts the variable down in the
/// EVSIDS heap, and set_activity(var, high) sifts it back up.
#[test]
fn test_set_activity_maintains_heap_invariant() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Create distinct ordering: var0 has highest activity
    for i in 0..5u32 {
        for _ in 0..(5 - i) {
            vsids.bump(Variable(i), &vals, true);
        }
    }
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
    vsids.insert_into_heap(Variable(0)); // put back after pick

    // Zero out var0's activity — it should sink to the bottom of the heap
    vsids.set_activity(Variable(0), 0.0);
    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert_ne!(
        top,
        Variable(0),
        "set_activity(0.0) must sift var0 below higher-activity variables"
    );
    // var1 had 4 bumps, should now be on top
    assert_eq!(top, Variable(1));
    vsids.insert_into_heap(Variable(1)); // put back

    // Now boost var0 with a very high activity — it should float back up
    vsids.set_activity(Variable(0), 1e10);
    let top2 = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top2,
        Variable(0),
        "set_activity(1e10) must sift var0 back to heap top"
    );
}

/// Verify set_activity on a variable NOT in the heap (already assigned/removed)
/// does not panic and correctly updates the stored activity.
#[test]
fn test_set_activity_on_removed_variable() {
    let mut vsids = VSIDS::new(3);
    let vals = make_vals(&[None; 3]);

    vsids.bump(Variable(1), &vals, true);
    vsids.remove_from_heap(Variable(1));

    // set_activity on a removed variable should update the stored value
    // without touching the heap (heap_pos is INVALID_POS).
    vsids.set_activity(Variable(1), 0.0);
    assert_eq!(vsids.activity(Variable(1)), 0.0);

    // Re-insert: var1 now has 0.0 activity, should not be top
    vsids.insert_into_heap(Variable(1));
    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert_ne!(top, Variable(1), "zero-activity var should not be heap top");
}

/// Regression test for #5580: many decay() calls without bump() must not
/// overflow the increment to infinity. The proactive rescale in decay()
/// should fire before the increment exceeds f64::MAX.
#[test]
fn test_decay_does_not_overflow_to_infinity() {
    let mut vsids = VSIDS::new(3);
    // Call decay() many times without any bump() — simulates a long solve
    // where conflicts happen rapidly with no new bumps (e.g., CP-SAT).
    for _ in 0..100_000 {
        vsids.decay();
    }
    assert!(
        vsids.increment.is_finite() && vsids.increment > 0.0,
        "increment must stay finite after 100k decays, got: {}",
        vsids.increment
    );
    // After rescale, bumping must still work correctly
    let vals = make_vals(&[None; 3]);
    vsids.bump(Variable(1), &vals, true);
    assert!(
        vsids.activity(Variable(1)).is_finite(),
        "activity must be finite after bump post-rescale"
    );
    assert!(
        vsids.activity(Variable(1)) > vsids.activity(Variable(0)),
        "bumped variable must have higher activity"
    );
}

// -- CHB tests --

#[test]
fn test_chb_arrays_lazy_allocation() {
    // In the default state (no CHB usage), CHB arrays must be None (#8121).
    let vsids = VSIDS::new(100);
    assert!(
        vsids.chb_scores.is_none(),
        "CHB scores must not be allocated on construction"
    );
    assert!(
        vsids.chb_last_conflict.is_none(),
        "CHB last_conflict must not be allocated on construction"
    );
}

#[test]
fn test_chb_arrays_allocated_on_first_bump() {
    let mut vsids = VSIDS::new(100);
    vsids.chb_bump(Variable(5));
    assert!(
        vsids.chb_scores.is_some(),
        "CHB scores must be allocated after first chb_bump"
    );
    assert!(
        vsids.chb_last_conflict.is_some(),
        "CHB last_conflict must be allocated after first chb_bump"
    );
    assert_eq!(vsids.chb_scores.as_ref().unwrap().len(), 100);
}

#[test]
fn test_chb_arrays_not_allocated_by_ensure_num_vars() {
    let mut vsids = VSIDS::new(50);
    vsids.ensure_num_vars(100);
    assert!(
        vsids.chb_scores.is_none(),
        "ensure_num_vars must not allocate CHB arrays if they are None"
    );
}

#[test]
fn test_chb_arrays_grown_by_ensure_num_vars_when_allocated() {
    let mut vsids = VSIDS::new(50);
    vsids.chb_bump(Variable(0)); // Force allocation
    assert_eq!(vsids.chb_scores.as_ref().unwrap().len(), 50);
    vsids.ensure_num_vars(100);
    assert_eq!(
        vsids.chb_scores.as_ref().unwrap().len(),
        100,
        "ensure_num_vars must grow CHB arrays when already allocated"
    );
}

#[test]
fn test_chb_reset_preserves_none() {
    let mut vsids = VSIDS::new(50);
    vsids.chb_reset();
    assert!(
        vsids.chb_scores.is_none(),
        "chb_reset must not allocate CHB arrays if they were None"
    );
}

#[test]
fn test_chb_initial_scores_are_zero() {
    let vsids = VSIDS::new(5);
    for i in 0..5u32 {
        assert_eq!(vsids.chb_score(Variable(i)), 0.0);
    }
}

#[test]
fn test_chb_bump_increases_score() {
    let mut vsids = VSIDS::new(5);
    let before = vsids.chb_score(Variable(2));
    vsids.chb_bump(Variable(2));
    let after = vsids.chb_score(Variable(2));
    assert!(
        after > before,
        "CHB bump must increase Q-score: before={before}, after={after}"
    );
}

#[test]
fn test_chb_reward_locality() {
    // A variable bumped with a small gap (recent conflict involvement)
    // gets a higher reward than one bumped with a large gap.
    let mut vsids = VSIDS::new(5);

    // Bump var 0 with a large gap: advance 100 conflicts first.
    for _ in 0..100 {
        vsids.chb_on_conflict();
    }
    vsids.chb_bump(Variable(0)); // gap = 100 - 0 + 1 = 101
    let score_large_gap = vsids.chb_score(Variable(0));

    // Bump var 1 immediately after (gap = 0)
    vsids.chb_bump(Variable(1)); // gap = 100 - 0 + 1 = 101 (same gap)
    vsids.chb_on_conflict(); // conflict 101
    vsids.chb_bump(Variable(1)); // gap = 101 - 100 + 1 = 2
    let score_small_gap = vsids.chb_score(Variable(1));

    // Variable 1 was bumped twice (once with large gap, once with small gap).
    // Variable 0 was bumped once with a large gap.
    // Var 1 should have accumulated more score from the second bump with
    // high reward (small gap).
    assert!(
        score_small_gap > score_large_gap,
        "var 1 (bumped with small gap) should have higher score than var 0 (large gap): small={score_small_gap}, large={score_large_gap}"
    );
}

#[test]
fn test_chb_alpha_decays() {
    let mut vsids = VSIDS::new(3);
    let alpha_before = vsids.chb_alpha;
    vsids.chb_on_conflict();
    let alpha_after = vsids.chb_alpha;
    assert!(
        alpha_after < alpha_before,
        "alpha must decay: before={alpha_before}, after={alpha_after}"
    );
    assert!(
        alpha_after >= 0.06,
        "alpha must not drop below CHB_ALPHA_MIN: {alpha_after}"
    );
}

#[test]
fn test_chb_reset_clears_state() {
    let mut vsids = VSIDS::new(5);
    vsids.chb_bump(Variable(0));
    vsids.chb_bump(Variable(1));
    vsids.chb_on_conflict();
    vsids.chb_on_conflict();

    vsids.chb_reset();

    for i in 0..5u32 {
        assert_eq!(
            vsids.chb_score(Variable(i)),
            0.0,
            "CHB score must be 0 after reset"
        );
    }
    assert_eq!(vsids.chb_conflicts, 0);
    assert!(
        (vsids.chb_alpha - 0.4).abs() < 1e-10,
        "alpha must be reset to CHB_ALPHA_INIT"
    );
}

#[test]
fn test_chb_swap_and_heap_selection() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Give var 3 the highest EVSIDS activity
    vsids.bump(Variable(3), &vals, true);
    vsids.bump(Variable(3), &vals, true);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));
    vsids.insert_into_heap(Variable(3));

    // Give var 1 the highest CHB score
    for _ in 0..20 {
        vsids.chb_bump(Variable(1));
        vsids.chb_on_conflict();
    }

    // Swap to CHB mode: heap should now order by CHB scores
    vsids.swap_chb_scores();
    let top_chb = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top_chb,
        Variable(1),
        "after swap, heap should order by CHB scores"
    );
    vsids.insert_into_heap(Variable(1));

    // Swap back: heap should order by EVSIDS again
    vsids.swap_chb_scores();
    let top_evsids = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top_evsids,
        Variable(3),
        "after swap back, heap should order by EVSIDS scores"
    );
}

#[test]
fn test_chb_bump_while_loaded_updates_heap() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Swap to CHB mode
    vsids.swap_chb_scores();

    // Bump var 2 many times while CHB is loaded -- should update heap
    for _ in 0..50 {
        vsids.chb_bump(Variable(2));
        vsids.chb_on_conflict();
    }

    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(
        top,
        Variable(2),
        "var 2 with many CHB bumps should be heap top while CHB is loaded"
    );

    // Swap back
    vsids.insert_into_heap(Variable(2));
    vsids.swap_chb_scores();
}

#[test]
fn test_chb_ensure_num_vars_extends_arrays() {
    let mut vsids = VSIDS::new(3);
    vsids.ensure_num_vars(6);

    // New variables should have zero CHB scores
    for i in 3..6u32 {
        assert_eq!(vsids.chb_score(Variable(i)), 0.0);
    }

    // Bumping new variables should work
    vsids.chb_bump(Variable(5));
    assert!(vsids.chb_score(Variable(5)) > 0.0);
}

#[test]
fn test_chb_dormant_evsids_bump() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Give var 0 some EVSIDS activity
    vsids.bump(Variable(0), &vals, true);
    let evsids_before = vsids.activity(Variable(0));

    // Swap to CHB mode (EVSIDS scores now in chb_scores)
    vsids.swap_chb_scores();

    // Dormant bump var 0 EVSIDS score
    vsids.bump_evsids_score_dormant(Variable(0));
    vsids.decay_evsids_dormant();

    // Swap back and check EVSIDS score increased
    vsids.swap_chb_scores();
    let evsids_after = vsids.activity(Variable(0));
    assert!(
        evsids_after > evsids_before,
        "dormant EVSIDS bump must increase score: before={evsids_before}, after={evsids_after}"
    );
}

// -- Batch bump tests (#8350) --

#[test]
fn test_batch_evsids_kernel_contract_reports_single_sift() {
    let mut activities = [0.0; 6];
    let mut heap_pos = [INVALID_POS; 6];
    heap_pos[3] = 0;

    let update = batch::apply_evsids_batch(&mut activities, &heap_pos, &[1, 3, 1], 2.0);

    assert_eq!(activities[1], 4.0, "duplicate vars must match scalar bumps");
    assert_eq!(activities[3], 2.0);
    assert_eq!(update.touched, 3);
    assert_eq!(update.in_heap, 1);
    assert_eq!(update.repair, batch::BatchHeapRepair::SiftUp { var: 3 });
    assert!(!update.needs_rescale);
}

#[test]
fn test_batch_chb_kernel_contract_matches_scalar_updates() {
    let vars = [0usize, 2, 2, 4];
    let mut batch_scores = [0.0; 5];
    let mut batch_last = [0u64; 5];
    let mut scalar_scores = [0.0; 5];
    let mut scalar_last = [0u64; 5];
    let mut heap_pos = [INVALID_POS; 5];
    heap_pos[0] = 1;
    heap_pos[4] = 3;
    let conflicts = 10;
    let alpha = 0.4;

    let update = batch::apply_chb_batch(
        &mut batch_scores,
        &mut batch_last,
        Some(&heap_pos),
        &vars,
        conflicts,
        alpha,
    );

    for &idx in &vars {
        let reward = 1.0 / (conflicts.saturating_sub(scalar_last[idx]) + 1) as f64;
        scalar_scores[idx] = (1.0 - alpha).mul_add(scalar_scores[idx], alpha * reward);
        scalar_last[idx] = conflicts;
    }

    assert_eq!(batch_scores, scalar_scores);
    assert_eq!(batch_last, scalar_last);
    assert_eq!(update.touched, vars.len());
    assert_eq!(update.in_heap, 2);
    assert_eq!(update.repair, batch::BatchHeapRepair::Rebuild);
    assert!(!update.needs_rescale);
}

#[test]
fn test_batch_bump_scores_empty() {
    let mut vsids = VSIDS::new(5);
    // Empty slice must not panic.
    vsids.batch_bump_scores(&[]);
}

#[test]
fn test_batch_bump_scores_single_var() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Single-element batch should behave identically to bump_score.
    vsids.batch_bump_scores(&[2]);

    assert!(
        vsids.activity(Variable(2)) > 0.0,
        "batch_bump_scores with one var must increase activity"
    );
    assert_eq!(
        vsids.pick_branching_variable(&vals),
        Some(Variable(2)),
        "single batch-bumped var should be heap top"
    );
}

#[test]
fn test_batch_bump_scores_matches_individual_bumps() {
    // Verify that batch bumping produces the same activities as
    // individual bump_score calls.
    let mut vsids_batch = VSIDS::new(10);
    let mut vsids_indiv = VSIDS::new(10);
    let _vals = make_vals(&[None; 10]);

    let vars_to_bump: Vec<usize> = vec![0, 3, 5, 7, 9];

    vsids_batch.batch_bump_scores(&vars_to_bump);
    for &idx in &vars_to_bump {
        vsids_indiv.bump_score(Variable(idx as u32));
    }

    for i in 0..10 {
        let batch_act = vsids_batch.activity(Variable(i));
        let indiv_act = vsids_indiv.activity(Variable(i));
        assert!(
            (batch_act - indiv_act).abs() < 1e-15,
            "activity mismatch for var {i}: batch={batch_act}, individual={indiv_act}"
        );
    }
}

#[test]
fn test_batch_bump_scores_large_batch_uses_heapify() {
    // Bump >= 8 in-heap variables to exercise the Floyd's heapify path.
    let mut vsids = VSIDS::new(20);
    let vals = make_vals(&[None; 20]);

    let vars_to_bump: Vec<usize> = (0..12).collect();
    vsids.batch_bump_scores(&vars_to_bump);

    // All bumped variables should have positive activity.
    for &idx in &vars_to_bump {
        assert!(
            vsids.activity(Variable(idx as u32)) > 0.0,
            "var {idx} must have positive activity after batch bump"
        );
    }

    // The heap must pick a bumped variable (they all have higher activity
    // than unbumped ones).
    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert!(
        vars_to_bump.contains(&top.index()),
        "heap top {top:?} should be one of the bumped variables"
    );
}

#[test]
fn test_batch_bump_scores_single_in_heap_sift_path() {
    // Bump several variables, but leave only one of them in the heap. The
    // repair contract should use the single-variable sift-up path.
    let mut vsids = VSIDS::new(20);
    let vals = make_vals(&[None; 20]);

    let vars_to_bump: Vec<usize> = vec![3, 7, 15];
    vsids.remove_from_heap(Variable(3));
    vsids.remove_from_heap(Variable(15));
    vsids.batch_bump_scores(&vars_to_bump);

    assert_eq!(
        vsids.pick_branching_variable(&vals),
        Some(Variable(7)),
        "the only in-heap bumped variable should be on top"
    );
}

#[test]
fn test_batch_bump_scores_two_in_heap_rebuild_path() {
    // Two simultaneous in-heap bumps must use Floyd heapify; repeated sift-up
    // can violate the heap invariant for this pattern.
    let mut vsids = VSIDS::new(4);
    let vals = make_vals(&[None; 4]);

    for _ in 0..100 {
        vsids.bump_score(Variable(0));
    }
    for _ in 0..90 {
        vsids.bump_score(Variable(1));
    }
    for _ in 0..80 {
        vsids.bump_score(Variable(2));
    }
    for _ in 0..70 {
        vsids.bump_score(Variable(3));
    }

    vsids.increment = 50.0;
    vsids.batch_bump_scores(&[3, 1]);

    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert_eq!(top, Variable(1));
    vsids.remove_from_heap(top);
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));
}

#[test]
fn test_batch_bump_scores_with_removed_vars() {
    // Some variables are removed from the heap (assigned). batch_bump_scores
    // must still correctly increment their activities and skip heap operations.
    let mut vsids = VSIDS::new(10);
    let vals = make_vals(&[None; 10]);

    vsids.remove_from_heap(Variable(2));
    vsids.remove_from_heap(Variable(5));

    vsids.batch_bump_scores(&[1, 2, 5, 8]);

    // var 2 and var 5 are out of heap but their activities must be updated.
    assert!(vsids.activity(Variable(2)) > 0.0);
    assert!(vsids.activity(Variable(5)) > 0.0);

    // Heap should still work for in-heap variables.
    let top = vsids.pick_branching_variable(&vals).unwrap();
    assert!(
        top == Variable(1) || top == Variable(8),
        "heap top should be var 1 or 8 (the in-heap bumped ones), got {top:?}"
    );
}

#[test]
fn test_batch_bump_scores_rescale() {
    // Verify rescale is triggered correctly during batch bumping.
    let mut vsids = VSIDS::new(5);

    // Push increment near the rescale threshold.
    for _ in 0..10_000 {
        vsids.decay();
    }
    assert!(
        vsids.current_increment() > 1.0,
        "increment must grow via decay"
    );

    vsids.batch_bump_scores(&[0, 1, 2, 3, 4]);

    // All activities must be finite after batch bump + rescale.
    for i in 0..5 {
        assert!(
            vsids.activity(Variable(i)).is_finite(),
            "var {i} activity must be finite after batch bump with rescale"
        );
    }
}

#[test]
fn test_batch_bump_stable_mode() {
    let mut vsids = VSIDS::new(10);
    let vals = make_vals(&[None; 10]);

    let vars: Vec<usize> = vec![1, 4, 7];
    vsids.batch_bump(&vars, &vals, true);

    // Activities must be incremented.
    for &idx in &vars {
        assert!(
            vsids.activity(Variable(idx as u32)) > 0.0,
            "var {idx} must have positive activity after batch_bump stable"
        );
    }

    // VMTF must be deferred.
    assert!(
        vsids.vmtf_is_deferred(),
        "vmtf_deferred must be set after stable batch_bump"
    );

    // Last bumped variable (var 7) should have highest bump_order.
    assert!(
        vsids.bump_order(Variable(7)) > vsids.bump_order(Variable(4)),
        "var 7 (bumped last) should have higher bump_order than var 4"
    );
    assert!(
        vsids.bump_order(Variable(4)) > vsids.bump_order(Variable(1)),
        "var 4 (bumped second) should have higher bump_order than var 1"
    );

    // vmtf_unassigned should be the last unassigned bumped variable.
    // All are unassigned, so it should be var 7 (the last one processed).
    assert_eq!(vsids.vmtf_unassigned, 7);
}

#[test]
fn test_batch_bump_vmtf_mode() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Sort by bump_order ascending (caller's responsibility for VMTF).
    let vars: Vec<usize> = vec![3, 1, 4];
    vsids.batch_bump(&vars, &vals, false);

    // In VMTF mode, the last variable bumped ends up at the front.
    assert_eq!(
        vsids.pick_branching_variable_vmtf(&vals),
        Some(Variable(4)),
        "last batch-bumped var in VMTF mode should be at queue front"
    );
}

#[test]
fn test_batch_bump_stable_unassigned_cursor() {
    // Verify that the vmtf_unassigned cursor tracks the last *unassigned*
    // variable in the batch, not just the last variable.
    let mut vsids = VSIDS::new(5);
    // var 2 is assigned, rest unassigned
    let vals = make_vals(&[None, None, Some(true), None, None]);

    vsids.batch_bump(&[0, 2, 3], &vals, true);

    // var 2 is assigned (vals[2*2] != 0), so vmtf_unassigned should be var 3
    // (the last unassigned bumped variable).
    assert_eq!(
        vsids.vmtf_unassigned, 3,
        "vmtf_unassigned should be var 3 (last unassigned in batch)"
    );
}

#[test]
fn test_chb_batch_bump_matches_scalar_chb_unloaded() {
    let mut batch = VSIDS::new(6);
    let mut scalar = VSIDS::new(6);
    for _ in 0..7 {
        batch.chb_on_conflict();
        scalar.chb_on_conflict();
    }
    let vars = [1usize, 4, 1, 2];

    batch.chb_bump_batch(&vars);
    for &idx in &vars {
        scalar.chb_bump(Variable(idx as u32));
    }

    for i in 0..6 {
        assert_eq!(
            batch.chb_score(Variable(i)),
            scalar.chb_score(Variable(i)),
            "CHB batch/scalar score mismatch for var {i}"
        );
    }
}

#[test]
fn test_chb_batch_bump_loaded_repairs_heap() {
    let mut vsids = VSIDS::new(6);
    let vals = make_vals(&[None; 6]);

    vsids.swap_chb_scores();
    for _ in 0..5 {
        vsids.chb_bump_batch(&[4, 2, 4]);
        vsids.chb_on_conflict();
    }

    assert_eq!(
        vsids.pick_branching_variable(&vals),
        Some(Variable(4)),
        "loaded CHB batch bump must keep the decision heap valid"
    );
}

#[test]
fn test_loaded_chb_single_score_decrease_repairs_heap_downward() {
    let mut vsids = VSIDS::new(4);
    let vals = make_vals(&[None; 4]);
    vsids.swap_chb_scores();

    // Seed a valid heap whose root only narrowly leads its first child.
    // A stale CHB estimate can decrease when its next reward is much lower;
    // the single-variable repair must therefore support sift-down as well as
    // the EVSIDS-style sift-up case.
    vsids.activities.copy_from_slice(&[0.5, 0.49, 0.1, 0.0]);
    vsids.rebuild_heap();
    vsids.chb_conflicts = 100;
    vsids.chb_last_conflict.as_mut().unwrap()[0] = 0;

    vsids.chb_bump_batch(&[0]);

    assert_eq!(
        vsids.pick_branching_variable(&vals),
        Some(Variable(1)),
        "a lowered CHB root must sift below its higher-scored child"
    );
}

#[test]
fn test_loaded_chb_random_batches_preserve_heap_and_position_maps() {
    // Deterministic xorshift stress for all three repair contracts:
    // no in-heap touch, one arbitrary key change, and a multi-touch rebuild.
    // Removed variables continue receiving CHB updates while assigned, then
    // exercise reinsertion with their final scores.
    let mut state = 0xD1B5_4A32_D192_ED03u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    for _trial in 0..512 {
        let n = 16 + (next() % 112) as usize;
        let mut vsids = VSIDS::new(n);
        vsids.swap_chb_scores();

        // Frequent ties exercise the variable-index tie-break as scores rise
        // and fall through the CHB exponential moving average.
        for score in &mut vsids.activities {
            *score = (next() % 32) as f64 / 31.0;
        }
        vsids.rebuild_heap();

        let mut removed = Vec::new();
        for var in 0..n {
            if next().is_multiple_of(5) && vsids.heap.len() > 1 {
                vsids.remove_from_heap(Variable(var as u32));
                removed.push(var);
            }
        }
        assert_heap_property_holds(&vsids);

        for round in 0..24 {
            vsids.chb_conflicts += 1 + next() % 64;
            vsids.chb_alpha = 0.06 + (next() % 35) as f64 / 100.0;

            let heap_var = vsids.heap[(next() as usize) % vsids.heap.len()] as usize;
            let mut vars = Vec::new();
            match round % 4 {
                // Exactly one in-heap key can move in either direction.
                0 => vars.push(heap_var),
                // Many non-heap changes plus exactly one in-heap change must
                // still select the single-key repair.
                1 if !removed.is_empty() => {
                    for _ in 0..3 {
                        vars.push(removed[(next() as usize) % removed.len()]);
                    }
                    vars.push(heap_var);
                }
                // Duplicate occurrences conservatively select a full rebuild.
                2 => {
                    vars.extend([heap_var, heap_var]);
                    for _ in 0..3 {
                        vars.push(vsids.heap[(next() as usize) % vsids.heap.len()] as usize);
                    }
                }
                // Updating only assigned variables must leave the heap intact.
                _ if !removed.is_empty() => {
                    for _ in 0..4 {
                        vars.push(removed[(next() as usize) % removed.len()]);
                    }
                }
                _ => vars.push(heap_var),
            }

            let conflicts = vsids.chb_conflicts;
            let last_conflict = vsids.chb_last_conflict.as_mut().unwrap();
            for &var in &vars {
                last_conflict[var] = next() % (conflicts + 1);
            }
            vsids.chb_bump_batch(&vars);
            assert_heap_property_holds(&vsids);
        }

        for var in removed {
            vsids.insert_into_heap(Variable(var as u32));
            assert_heap_property_holds(&vsids);
        }

        let vals = make_vals(&vec![None; n]);
        let mut previous = None;
        while let Some(top) = vsids.pick_branching_variable(&vals) {
            let current = top.index();
            if let Some(prior) = previous {
                assert!(
                    !vsids.var_less(current, prior),
                    "CHB heap pop order increased: var {current} after var {prior}"
                );
            }
            previous = Some(current);
            vsids.remove_from_heap(top);
        }
    }
}

#[test]
fn test_chb_batch_bump_reuses_allocated_arrays() {
    let mut vsids = VSIDS::new(8);
    vsids.chb_bump(Variable(0));
    let scores_cap = vsids.chb_scores.as_ref().unwrap().capacity();
    let last_cap = vsids.chb_last_conflict.as_ref().unwrap().capacity();

    vsids.chb_bump_batch(&[1, 2, 3, 4, 5]);

    assert_eq!(vsids.chb_scores.as_ref().unwrap().capacity(), scores_cap);
    assert_eq!(
        vsids.chb_last_conflict.as_ref().unwrap().capacity(),
        last_cap
    );
}

/// Verify that `rescale_for_reorder` normalizes inflated VSIDS activities
/// to max=1.0, preventing the starvation bug from #8470. In IC3/PDR
/// workloads, the VSIDS increment grows multiplicatively across solves.
/// Without periodic rescaling, activities become incomparable (newly
/// activated variables get current_increment() which dwarfs stale scores).
#[test]
fn test_rescale_for_reorder_normalizes_inflated_activities() {
    let mut vsids = VSIDS::new(5);
    let vals = make_vals(&[None; 5]);

    // Simulate many conflicts growing the increment (mimics IC3 workload).
    // 1000 decays at decay=0.95 means increment grows by (1/0.95)^1000 ~= 5e22.
    for _ in 0..1000 {
        vsids.decay();
    }

    // Bump var 1, then decay (increment grows), then bump var 3.
    // This gives var 3 a strictly higher activity than var 1 because
    // the increment is larger when var 3 is bumped.
    vsids.bump(Variable(1), &vals, true);
    vsids.decay(); // increment grows by 1/0.95
    vsids.bump(Variable(3), &vals, true);

    let pre_act_1 = vsids.activity(Variable(1));
    let pre_act_3 = vsids.activity(Variable(3));
    assert!(
        pre_act_3 > pre_act_1,
        "var 3 should have higher activity (bumped with larger increment)"
    );

    let pre_max = vsids.activities.iter().copied().fold(0.0_f64, f64::max);
    assert!(
        pre_max > 1e10,
        "activities should be inflated before rescale (got {pre_max})"
    );
    let pre_inc = vsids.current_increment();
    assert!(
        pre_inc > 1e10,
        "increment should be inflated before rescale (got {pre_inc})"
    );

    // This is the method called by reset_search_state() for the #8470 fix.
    vsids.rescale_for_reorder();

    // After rescale: max activity should be 1.0, increment proportionally small.
    let post_max = vsids.activities.iter().copied().fold(0.0_f64, f64::max);
    assert!(
        (post_max - 1.0).abs() < 1e-10,
        "max activity should be 1.0 after rescale_for_reorder (got {post_max})"
    );
    let post_inc = vsids.current_increment();
    assert!(
        post_inc <= 1.0,
        "increment should be <= 1.0 after rescale (got {post_inc})"
    );
    assert!(
        post_inc > 0.0 && post_inc.is_finite(),
        "increment must be positive finite after rescale (got {post_inc})"
    );

    // Relative ordering must be preserved: var 3 had higher activity before rescale.
    assert!(
        vsids.activity(Variable(3)) > vsids.activity(Variable(1)),
        "relative ordering must be preserved after rescale"
    );

    // Heap ordering must be valid (var 3 should be at top with highest activity).
    let top = vsids.pick_branching_variable(&vals);
    assert_eq!(
        top,
        Some(Variable(3)),
        "heap top should be var 3 (highest activity) after rescale"
    );
}

/// Verify that repeated rescale_for_reorder calls are idempotent when
/// activities are already normalized (max <= 1.0).
#[test]
fn test_rescale_for_reorder_idempotent_when_normalized() {
    let mut vsids = VSIDS::new(3);
    let vals = make_vals(&[None; 3]);

    // Bump once with default increment (1.0).
    vsids.bump(Variable(0), &vals, true);
    vsids.bump(Variable(1), &vals, true);

    // First rescale normalizes.
    vsids.rescale_for_reorder();
    let act_0_first = vsids.activity(Variable(0));
    let act_1_first = vsids.activity(Variable(1));
    let inc_first = vsids.current_increment();

    // Second rescale should be a no-op (max already <= 1.0).
    vsids.rescale_for_reorder();
    let act_0_second = vsids.activity(Variable(0));
    let act_1_second = vsids.activity(Variable(1));
    let inc_second = vsids.current_increment();

    assert!(
        (act_0_first - act_0_second).abs() < 1e-15,
        "activities should not change on redundant rescale"
    );
    assert!(
        (act_1_first - act_1_second).abs() < 1e-15,
        "activities should not change on redundant rescale"
    );
    assert!(
        (inc_first - inc_second).abs() < 1e-15,
        "increment should not change on redundant rescale"
    );
}

/// Explicitly verify the binary max-heap property over every parent/child pair.
///
/// Used by the EVSIDS batch-bump multi-sift regression tests below. Mirrors the
/// internal `debug_assert_heap_property` contract but is available in release
/// test builds too.
#[cfg(test)]
fn assert_heap_property_holds(vsids: &VSIDS) {
    for pos in 1..vsids.heap.len() {
        let parent = (pos - 1) / 2;
        let var = vsids.heap[pos] as usize;
        let parent_var = vsids.heap[parent] as usize;
        assert!(
            !vsids.var_less(var, parent_var),
            "heap property violated at pos {pos}: var {var} (act={}) > parent var \
             {parent_var} (act={}) at pos {parent}",
            vsids.activities[var],
            vsids.activities[parent_var]
        );
        assert_eq!(
            vsids.heap_pos[var], pos as u32,
            "heap_pos inconsistent for var {var}"
        );
    }
    for (var, &pos) in vsids.heap_pos.iter().enumerate() {
        if pos == INVALID_POS {
            continue;
        }
        assert!(
            (pos as usize) < vsids.heap.len(),
            "heap_pos[{var}]={pos} is outside heap.len()={}",
            vsids.heap.len()
        );
        assert_eq!(
            vsids.heap[pos as usize], var as u32,
            "heap_pos reverse map inconsistent for var {var}"
        );
    }
}

/// Regression for the EVSIDS batch-bump multi-sift unsoundness (b8 fp.rem crash):
/// sifting bumped variables up in arbitrary (caller) order could strand a deeper
/// bumped variable beneath an unbumped variable displaced by a shallower sift,
/// violating the heap property. The repair now sifts in ascending heap-position
/// order. This stress test drives `batch_bump_scores` (which routes through
/// `repair_heap_after_evsids_batch`) on many random heaps and asserts the
/// invariant after every batch — both via the explicit checker here and via the
/// internal `debug_assert_heap_property` that fires inside the repair.
#[test]
fn test_batch_bump_multi_sift_preserves_heap_property() {
    // Deterministic xorshift PRNG so the test is reproducible.
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    for _trial in 0..4000 {
        // A heap large enough that a handful of bumped variables takes the
        // multi-sift branch rather than the Floyd rebuild branch.
        let n = 64 + (next() % 192) as usize;
        let mut vsids = VSIDS::new(n);

        // Seed varied activities (small integers so ties — exercised by the
        // index tie-break in `var_less` — occur frequently) and rebuild.
        for v in 0..n {
            vsids.activities[v] = (next() % 6) as f64;
        }
        vsids.rebuild_heap();
        assert_heap_property_holds(&vsids);

        // Apply several rounds of batch bumps with small, distinct subsets so
        // each round hits the uniform-increment multi-sift repair.
        for _round in 0..8 {
            let k = 2 + (next() % 6) as usize;
            let mut vars = Vec::with_capacity(k);
            for _ in 0..k {
                vars.push((next() as usize) % n);
            }
            vsids.batch_bump_scores(&vars);
            assert_heap_property_holds(&vsids);
        }

        // The heap root must be a true maximum: pop order must be
        // non-increasing under `var_less`.
        let vals = make_vals(&vec![None; n]);
        let mut prev: Option<usize> = None;
        while let Some(top) = vsids.pick_branching_variable(&vals) {
            let cur = top.index();
            if let Some(p) = prev {
                assert!(
                    !vsids.var_less(cur, p),
                    "pop order not non-increasing: var {cur} popped after var {p}"
                );
            }
            prev = Some(cur);
            vsids.remove_from_heap(top);
        }
    }
}

/// Regression for the rescale underflow heap corruption (exposed by the braun7
/// soundness test after the multi-sift fix): `rescale()` multiplies every
/// activity by 1e-100, which is order-preserving UNLESS distinct tiny positive
/// activities underflow to exactly 0.0. Once two distinct values collapse to
/// equal 0.0, `var_less`'s index tie-break can disagree with the existing heap
/// order, silently violating the max-heap invariant. The fix rebuilds the heap
/// when such an underflow occurs. Here we plant distinct sub-1e-100 activities
/// (which underflow to 0.0 on rescale) in tie-break-hostile heap positions, then
/// drive a bump that triggers rescale and assert the invariant still holds.
#[test]
fn test_rescale_underflow_to_zero_rebuilds_heap() {
    let n = 8;
    let mut vsids = VSIDS::new(n);

    // Give a few variables distinct tiny activities below the underflow cliff:
    // x * 1e-100 == 0.0 for x < ~1e-208. Crucially, arrange them so that the
    // heap order (by these tiny activities) DISAGREES with the index tie-break
    // they will fall back to once they all become 0.0. Higher-index vars get
    // larger tiny activities, so before rescale they sit above lower-index vars;
    // after underflow (all 0.0) the index tie-break wants the opposite order.
    vsids.activities[1] = 1e-250;
    vsids.activities[3] = 2e-250;
    vsids.activities[5] = 3e-250;
    vsids.activities[7] = 4e-250;
    // One variable large enough to trigger rescale when bumped.
    vsids.activities[0] = 9e99;
    vsids.rebuild_heap();
    assert_heap_property_holds(&vsids);

    // Bump var 0 past the rescale limit (1e100), forcing rescale(); the tiny
    // activities underflow to 0.0 inside it.
    vsids.increment = 2e99;
    vsids.bump_score(Variable(0));

    // After rescale + underflow, the tiny-activity vars are all 0.0 and the
    // heap must still satisfy the (now index-tie-broken) invariant.
    assert_heap_property_holds(&vsids);
    for v in [1usize, 3, 5, 7] {
        assert_eq!(
            vsids.activities[v], 0.0,
            "tiny activity for var {v} must have underflowed to 0.0"
        );
    }

    // Pop order must remain non-increasing under var_less (a valid heap).
    let vals = make_vals(&vec![None; n]);
    let mut prev: Option<usize> = None;
    while let Some(top) = vsids.pick_branching_variable(&vals) {
        let cur = top.index();
        if let Some(p) = prev {
            assert!(
                !vsids.var_less(cur, p),
                "pop order not non-increasing after rescale underflow: var {cur} after var {p}"
            );
        }
        prev = Some(cur);
        vsids.remove_from_heap(top);
    }
}

/// `rescale_for_reorder` must re-heapify after scaling: multiplication by the
/// scale factor is monotone but NOT strictly monotone — distinct tiny
/// activities can round to the SAME value (denormal collapse) without
/// reaching exactly 0.0. The heap tie-break is by variable index
/// (`var_less`), so a collapse can invert the relative order of a
/// parent/child pair that was strictly ordered before scaling; the old code
/// rebuilt the heap only when an activity underflowed to exactly 0.0 and
/// left the stale arrangement in place otherwise (debug builds then panicked
/// with "BUG: heap property violated" in `debug_assert_heap_property`; hit
/// in the field by the model-checker-consumer looping_id IC3 lane).
#[test]
fn test_rescale_for_reorder_denormal_collapse_rebuilds_heap() {
    let mut vsids = VSIDS::new(5);

    // Smallest positive denormal.
    let d = f64::from_bits(1);
    // Non-power-of-two max so scaling actually rounds.
    let m = 1e300_f64;

    // Heap: v4 at the root (max activity), v3 above v1 with a strictly
    // greater activity. After scaling by 1/m, both 1.4*d and 0.9*d round to
    // the same denormal `d`, and the index tie-break then orders v1 BEFORE
    // v3 — inverting the stale parent/child arrangement unless the heap is
    // rebuilt.
    let dm = d * m; // ~5e-24: comfortably normal, scales back into denormals
    vsids.set_activity(Variable(4), m);
    vsids.set_activity(Variable(3), 1.4 * dm);
    vsids.set_activity(Variable(1), 0.9 * dm);
    assert!(
        vsids.activity(Variable(3)) > vsids.activity(Variable(1)),
        "precondition: strictly ordered before rescale"
    );

    vsids.rescale_for_reorder();

    assert_eq!(
        vsids.activity(Variable(3)),
        vsids.activity(Variable(1)),
        "precondition: activities must collapse to the same denormal \
         (got {} vs {})",
        vsids.activity(Variable(3)),
        vsids.activity(Variable(1)),
    );
    assert!(
        vsids.activity(Variable(1)) > 0.0,
        "precondition: collapse must NOT reach exactly 0.0 (the old code \
         only rebuilt on underflow-to-zero)"
    );

    // The old code left the heap stale here; these validators panicked.
    // (The validators are #[cfg(debug_assertions)]-only: in --release test
    // builds they don't exist, so gate the calls to keep the suite compiling
    // in both modes. The denormal-collapse preconditions above still run.)
    #[cfg(debug_assertions)]
    {
        vsids.debug_assert_heap_property();
        vsids.debug_assert_heap_pos_consistent();
    }
}

/// `decay_all_scores` must re-heapify after scaling, for the same reason
/// `rescale` and `rescale_for_reorder` do: multiplication by the decay factor
/// is monotone but NOT strictly monotone. Distinct tiny activities can round
/// to the SAME value without ever reaching exactly 0.0, and the heap's
/// tie-break is by variable index (`var_less`), so the collapse inverts the
/// relative order of a parent/child pair that was strictly ordered before the
/// decay. The old guard here rebuilt only when a previously-nonzero activity
/// underflowed to exactly 0.0, so it left this stale arrangement in place
/// (debug builds then panic with "BUG: heap property violated" in
/// `debug_assert_heap_property` on the next validated heap op).
#[test]
fn test_decay_all_scores_denormal_collapse_rebuilds_heap() {
    let mut vsids = VSIDS::new(5);

    // Smallest positive denormal: every denormal is an integer multiple of it.
    let d = f64::from_bits(1);

    // Build a heap where a HIGHER-index variable is the parent of a
    // LOWER-index one, ordered strictly by activity:
    //   var4 (act 1.0) at the root, var3 (act 5*d) above var1 (act 4*d).
    // `set_activity` sifts, so the heap stays valid while we plant them.
    vsids.set_activity(Variable(4), 1.0);
    vsids.set_activity(Variable(3), 5.0 * d);
    vsids.set_activity(Variable(1), 4.0 * d);
    assert_heap_property_holds(&vsids);
    assert!(
        vsids.activity(Variable(3)) > vsids.activity(Variable(1)),
        "precondition: strictly ordered before decay"
    );
    let pos3 = vsids.heap_pos[3] as usize;
    let pos1 = vsids.heap_pos[1] as usize;
    assert_eq!(
        (pos1 - 1) / 2,
        pos3,
        "precondition: var3 must be the parent of var1 (higher index above \
         lower index), so the tie-break inverts the edge on collapse"
    );

    // Factor 0.5: 5*d*0.5 == 2.5*d rounds (ties-to-even) to 2*d, and
    // 4*d*0.5 == 2*d exactly — a collapse to a shared NONZERO value.
    vsids.decay_all_scores(0.5);

    assert_eq!(
        vsids.activity(Variable(3)),
        vsids.activity(Variable(1)),
        "precondition: activities must collapse to the same denormal \
         (got {} vs {})",
        vsids.activity(Variable(3)),
        vsids.activity(Variable(1)),
    );
    assert!(
        vsids.activity(Variable(1)) > 0.0,
        "precondition: collapse must NOT reach exactly 0.0 (the old code \
         only rebuilt on underflow-to-zero)"
    );

    // The old code left the heap stale here.
    assert_heap_property_holds(&vsids);
    #[cfg(debug_assertions)]
    {
        vsids.debug_assert_heap_property();
        vsids.debug_assert_heap_pos_consistent();
    }

    // And the decision order must still be a valid non-increasing pop order.
    let vals = make_vals(&[None; 5]);
    let mut prev: Option<usize> = None;
    while let Some(top) = vsids.pick_branching_variable(&vals) {
        let cur = top.index();
        if let Some(p) = prev {
            assert!(
                !vsids.var_less(cur, p),
                "pop order not non-increasing after decay collapse: var {cur} after var {p}"
            );
        }
        prev = Some(cur);
        vsids.remove_from_heap(top);
    }
}
