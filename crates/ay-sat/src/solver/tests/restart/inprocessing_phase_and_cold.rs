// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver::tests::restart` to preserve test FQNs.

/// Test that minimize_learned_clause removes a truly redundant literal.
///
/// Constructs a scenario where literal L is implied by the reason chain of
/// other literals in the learned clause. After minimization, L should be removed.
#[test]

// ========================================================================
// Restart-Inprocessing Interaction Tests
// ========================================================================

fn test_restart_inprocessing_is_noop_above_level_zero() {
    let mut solver: Solver = Solver::new(2);
    solver.decide(Literal::positive(Variable(0)));
    assert_eq!(solver.decision_level, 1);

    // Force all inprocessing schedules due.
    solver.num_conflicts = 0;
    solver.inproc_ctrl.vivify.next_conflict = 0;
    solver.inproc_ctrl.subsume.next_conflict = 0;
    solver.inproc_ctrl.probe.next_conflict = 0;
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.inproc_ctrl.bce.next_conflict = 0;
    solver.inproc_ctrl.transred.next_conflict = 0;
    solver.inproc_ctrl.htr.next_conflict = 0;
    solver.inproc_ctrl.sweep.next_conflict = 0;

    let qhead_before = solver.qhead;
    let trail_len_before = solver.trail.len();

    assert!(
        !solver.run_restart_inprocessing(),
        "inprocessing must not run above level 0"
    );
    assert_eq!(solver.decision_level, 1);
    assert_eq!(solver.qhead, qhead_before);
    assert_eq!(solver.trail.len(), trail_len_before);
}

#[test]
fn test_restart_inprocessing_does_not_derive_unsat_on_empty_solver() {
    let mut solver: Solver = Solver::new(4);

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on empty solver"
    );
}

// ========================================================================
// Focused-Mode Phase Cycling (Kissat decide.c:178-187)
// ========================================================================

/// Test that focused-mode phase cycling overrides phase selection on
/// specific mode_switch_count cycles. Kissat uses `(switched >> 1) & 7`
/// to produce an 8-step cycle where slots 1 and 3 force fixed polarities.
#[test]
fn test_phase_cycling_focused_mode_overrides() {
    let mut solver = Solver::new(4);
    solver.stable_mode = false;
    let var = Variable(0);

    // Slot 1 (mode_switch_count=2,3) forces positive regardless of saved phase
    solver.phase[0] = -1;
    solver.cold.mode_switch_count = 2; // (2 >> 1) & 7 = 1
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "slot 1: should force positive (Kissat INITIAL_PHASE)"
    );
    solver.cold.mode_switch_count = 3; // (3 >> 1) & 7 = 1
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "slot 1 (odd): should force positive"
    );

    // Slot 3 (mode_switch_count=6,7) forces negative regardless of saved phase
    solver.phase[0] = 1;
    solver.cold.mode_switch_count = 6; // (6 >> 1) & 7 = 3
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "slot 3: should force negative (Kissat inverted)"
    );
    solver.cold.mode_switch_count = 7; // (7 >> 1) & 7 = 3
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "slot 3 (odd): should force negative"
    );

    // Non-override slots use saved phase
    solver.phase[0] = -1;
    for count in [0u64, 1, 4, 5, 8, 9, 10, 11] {
        let slot = (count >> 1) & 7;
        if slot == 1 || slot == 3 {
            continue;
        }
        solver.cold.mode_switch_count = count;
        assert_eq!(
            solver.pick_phase(var),
            Literal::negative(var),
            "count={count} (slot {slot}): should use saved=negative"
        );
    }
}

/// Test that phase cycling does NOT apply in stable mode.
#[test]
fn test_phase_cycling_stable_mode_no_override() {
    let mut solver = Solver::new(4);
    solver.stable_mode = true;
    let var = Variable(0);
    solver.phase[0] = -1; // saved = negative

    // Even on cycle slots 1 and 3, stable mode should use target/saved phases
    solver.cold.mode_switch_count = 2; // (2 >> 1) & 7 = 1
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "stable mode: slot 1 should NOT override, uses saved phase"
    );

    solver.cold.mode_switch_count = 6; // (6 >> 1) & 7 = 3
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "stable mode: slot 3 should NOT override, uses saved phase"
    );
}

/// Test the full 8-slot cycle to verify wrap-around behavior.
/// Kissat `(switched >> 1) & 7` produces slots 0-7 from pairs of
/// consecutive switch counts. Slots 1 and 3 force fixed polarity;
/// the other 6 slots fall through to saved phase.
#[test]
fn test_phase_cycling_full_cycle() {
    let mut solver = Solver::new(4);
    let var = Variable(0);
    solver.phase[0] = -1; // saved = negative

    // Focused mode: slots 1 and 3 override, others use saved phase
    solver.stable_mode = false;
    for count in 0..16u64 {
        solver.cold.mode_switch_count = count;
        let slot = (count >> 1) & 7;
        let expected = match slot {
            1 => Literal::positive(var),
            3 => Literal::negative(var),
            _ => Literal::negative(var), // saved phase
        };
        assert_eq!(
            solver.pick_phase(var),
            expected,
            "focused mode, count={count} (slot {slot}): expected {expected:?}"
        );
    }

    // Stable mode: no cycling, uses target_phase if set, else saved phase
    solver.stable_mode = true;
    solver.target_phase[0] = 1;
    for count in 0..16u64 {
        solver.cold.mode_switch_count = count;
        assert_eq!(
            solver.pick_phase(var),
            Literal::positive(var),
            "stable mode, count={count}: should use target=positive"
        );
    }
}

// ========================================================================
// Mode-Switch Random Burst (Kissat mode.c:214)
// ========================================================================

/// Test that mode_switch_count is incremented when mode switches occur.
#[test]
fn test_mode_switch_count_incremented() {
    let mut solver = Solver::new(4);
    assert_eq!(solver.cold.mode_switch_count, 0);

    // Force a mode switch by setting up conditions:
    // Set high conflicts past min_conflicts, enable glucose restarts,
    // make the stabilization phase end.
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.stable_mode = false;
    solver.cold.glucose_restarts = true;
    solver.cold.stable_phase_length = 1; // Phase ends immediately
    solver.cold.stable_mode_start_conflicts = 0;

    // Call should_restart which triggers mode switch internally
    solver.should_restart();

    // After mode switch, counter should be incremented
    assert_eq!(
        solver.cold.mode_switch_count, 1,
        "mode_switch_count should be 1 after first switch"
    );
    assert!(solver.stable_mode, "should have switched to stable mode");
}

/// Test that consecutive mode switches increment the counter correctly.
#[test]
fn test_mode_switch_count_consecutive() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.glucose_restarts = true;

    // First switch: focused -> stable
    solver.stable_mode = false;
    solver.cold.stable_phase_length = 1;
    solver.cold.stable_mode_start_conflicts = 0;
    solver.should_restart();
    assert_eq!(solver.cold.mode_switch_count, 1);
    assert!(solver.stable_mode);

    // Second switch: stable -> focused
    // Set tick-based switch conditions
    solver.cold.stabilize_tick_inc = 1;
    solver.cold.stabilize_tick_limit = 0; // Already past limit
    solver.search_ticks[1] = 1; // stable mode ticks > limit
    solver.should_restart();
    assert_eq!(solver.cold.mode_switch_count, 2);
    assert!(!solver.stable_mode);
}

#[test]
fn test_stable_only_lock_survives_reset_search_state() {
    let mut solver = Solver::new(4);
    solver.set_stable_only(true);

    solver.reset_search_state();

    assert!(
        solver.stable_mode,
        "stable-only should survive search reset"
    );
}

#[test]
fn test_stable_phase_init_survives_reset_search_state_8140() {
    let mut solver = Solver::new(4);
    solver.set_stable_phase_init(4096);
    solver.cold.stable_phase_length = 123;

    solver.reset_search_state();

    assert_eq!(solver.cold.stable_phase_length, 4096);

    solver.cold.stable_phase_length = 321;
    solver.reset_search_state_incremental();

    assert_eq!(solver.cold.stable_phase_length, 4096);
}

#[test]
fn test_stable_only_lock_blocks_mode_switching() {
    let mut solver = Solver::new(4);
    solver.set_stable_only(true);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.stable_phase_length = 1;
    solver.cold.stable_mode_start_conflicts = 0;

    solver.should_restart();

    assert!(
        solver.stable_mode,
        "stable-only should prevent switching back to focused mode"
    );
    assert_eq!(
        solver.cold.mode_switch_count, 0,
        "mode switches must stay disabled under stable-only"
    );
}

// ========================================================================
// Cold Restart (Zhang et al. 2024, arXiv:2404.16387)
// ========================================================================

#[test]
fn test_should_cold_restart_respects_interval() {
    let mut solver = Solver::new(4);

    // Initially: 0 conflicts, cold_restart_count=0.
    // Threshold = COLD_RESTART_INTERVAL * (0 + 1) = 300_000.
    assert!(
        !solver.should_cold_restart(),
        "should_cold_restart must be false at 0 conflicts"
    );

    // Just under threshold.
    solver.num_conflicts = COLD_RESTART_INTERVAL - 1;
    assert!(
        !solver.should_cold_restart(),
        "should_cold_restart must be false just under threshold"
    );

    // At threshold.
    solver.num_conflicts = COLD_RESTART_INTERVAL;
    assert!(
        solver.should_cold_restart(),
        "should_cold_restart must be true at threshold"
    );

    // Well over threshold.
    solver.num_conflicts = COLD_RESTART_INTERVAL + 100;
    assert!(
        solver.should_cold_restart(),
        "should_cold_restart must be true above threshold"
    );
}

#[test]
fn test_should_cold_restart_linear_growth() {
    let mut solver = Solver::new(4);

    // After 1st cold restart: threshold = COLD_RESTART_INTERVAL * 2
    solver.cold.cold_restart_count = 1;
    solver.cold.cold_restart_last_conflict = COLD_RESTART_INTERVAL;
    solver.num_conflicts = COLD_RESTART_INTERVAL + COLD_RESTART_INTERVAL * 2 - 1;
    assert!(
        !solver.should_cold_restart(),
        "2nd cold restart should require 2x interval"
    );

    solver.num_conflicts = COLD_RESTART_INTERVAL + COLD_RESTART_INTERVAL * 2;
    assert!(
        solver.should_cold_restart(),
        "2nd cold restart should fire at 2x interval"
    );
}

#[test]
fn test_should_cold_restart_disabled() {
    let mut solver = Solver::new(4);
    solver.cold.cold_restart_enabled = false;
    solver.num_conflicts = COLD_RESTART_INTERVAL * 10;
    assert!(
        !solver.should_cold_restart(),
        "should_cold_restart must return false when disabled"
    );
}

#[test]
fn test_do_cold_restart_updates_state() {
    let mut solver = Solver::new(10);
    solver.num_conflicts = COLD_RESTART_INTERVAL;
    solver.conflicts_since_restart = 42;

    assert_eq!(solver.cold.cold_restart_count, 0);
    assert_eq!(solver.stats.cold_restarts, 0);

    solver.do_cold_restart();

    assert_eq!(solver.cold.cold_restart_count, 1);
    assert_eq!(solver.stats.cold_restarts, 1);
    assert_eq!(
        solver.cold.cold_restart_last_conflict,
        COLD_RESTART_INTERVAL
    );
    assert_eq!(solver.conflicts_since_restart, 0);
}

#[test]
fn test_do_cold_restart_fo_shuffles_scores() {
    let mut solver = Solver::new(20);
    // Insert some variables with known activities.
    for i in 0..20u32 {
        solver.vsids.set_activity(Variable(i), f64::from(i));
    }

    // Capture initial activity order.
    let mut activities_before = Vec::new();
    for i in 0..20u32 {
        activities_before.push(solver.vsids.activity(Variable(i)));
    }

    solver.cold.cold_restart_fo_enabled = true;
    solver.num_conflicts = COLD_RESTART_INTERVAL;
    solver.do_cold_restart();

    // After FO, activities should be different (randomized).
    let mut activities_after = Vec::new();
    for i in 0..20u32 {
        activities_after.push(solver.vsids.activity(Variable(i)));
    }

    assert_ne!(
        activities_before, activities_after,
        "FO cold restart should randomize VSIDS activities"
    );
}

#[test]
fn test_do_cold_restart_fp_randomizes_phases() {
    let mut solver = Solver::new(20);
    // Set all phases to positive.
    solver.phase.fill(1);

    solver.cold.cold_restart_fo_enabled = false;
    solver.cold.cold_restart_fp_enabled = true;
    solver.num_conflicts = COLD_RESTART_INTERVAL;
    solver.do_cold_restart();

    // After FP, not all phases should be positive (random assignment).
    let all_positive = solver.phase.iter().all(|&p| p == 1);
    assert!(
        !all_positive,
        "FP cold restart should randomize phases (statistically unlikely all stay positive)"
    );
}
