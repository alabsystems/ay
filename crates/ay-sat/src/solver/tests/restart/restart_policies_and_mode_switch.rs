// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver::tests::restart` to preserve test FQNs.

/// Test that Glucose-style restart does NOT fire when EMAs are close.
#[test]
fn test_should_restart_glucose_holds_on_stable_ema() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.glucose_restarts = true;
    solver.stable_mode = false;
    solver.cold.stable_phase_length = 1_000_000;
    solver.cold.stable_mode_start_conflicts = 0;

    // Set EMAs so fast < RESTART_MARGIN(1.10) * slow
    solver.cold.lbd_ema_slow = 5.0;
    solver.cold.lbd_ema_fast = 5.4; // 5.4 < 1.10 * 5.0 = 5.5
    assert!(
        !solver.should_restart(),
        "glucose restart should NOT fire when lbd_ema_fast < RESTART_MARGIN * lbd_ema_slow"
    );
}

/// Test that stable-mode restarts follow Knuth's reluctant doubling (Luby sequence).
/// The Luby sequence is: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
/// Each value is multiplied by RELUCTANT_INIT (1024) to get the interval.
#[test]
fn test_should_restart_reluctant_luby_sequence() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.stable_mode = true;
    solver.cold.stable_phase_length = 1_000_000;
    solver.cold.stable_mode_start_conflicts = 0;

    // Start at (u=1, v=1, countdown=1) so first tick fires immediately.
    // Set ticked_at = num_conflicts - 1 so 1 new conflict triggers the tick.
    solver.cold.reluctant_u = 1;
    solver.cold.reluctant_v = 1;
    solver.cold.reluctant_countdown = 1;
    solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;

    // Expected Luby sequence values (v after each restart fires):
    //   u=1,v=1: (1&-1)==1 -> u=2,v=1 -> countdown=1*1024
    //   u=2,v=1: (2&-2)=2!=1 -> v=2 -> countdown=2*1024
    //   u=2,v=2: (2&-2)==2 -> u=3,v=1 -> countdown=1*1024
    //   u=3,v=1: (3&-3)=1==1 -> u=4,v=1 -> countdown=1*1024
    //   u=4,v=1: (4&-4)=4!=1 -> v=2 -> countdown=2*1024
    //   u=4,v=2: (4&-4)=4!=2 -> v=4 -> countdown=4*1024
    //   u=4,v=4: (4&-4)==4 -> u=5,v=1 -> countdown=1*1024
    let expected_v: [u64; 7] = [1, 2, 1, 1, 2, 4, 1];

    solver.conflicts_since_restart = 1;
    // First tick fires: delta = num_conflicts - ticked_at = 1, countdown 1->0
    assert!(
        solver.should_restart(),
        "first tick should fire (countdown=1)"
    );

    for (i, &exp_v) in expected_v.iter().enumerate() {
        assert_eq!(
            solver.cold.reluctant_v,
            exp_v,
            "after restart {}, v should be {} (Luby sequence)",
            i + 1,
            exp_v,
        );
        assert_eq!(
            solver.cold.reluctant_countdown,
            exp_v * RELUCTANT_INIT,
            "countdown should be v * RELUCTANT_INIT after restart {}",
            i + 1,
        );
        // Drain countdown to trigger next restart: simulate 1 new conflict
        solver.cold.reluctant_countdown = 1;
        solver.num_conflicts += 1;
        solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;
        solver.conflicts_since_restart = 1;
        assert!(
            solver.should_restart(),
            "should fire after drain (restart {})",
            i + 1
        );
    }
}

/// Test geometric restart schedule: next_restart = initial * factor^n.
/// Z3 uses this for QF_LRA with initial=100, factor=1.1.
#[test]
fn test_should_restart_geometric_schedule() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.set_geometric_restarts(100.0, 1.1);

    // Restart 0: threshold = 100 * 1.1^0 = 100
    solver.cold.restarts = 0;
    solver.conflicts_since_restart = 99;
    assert!(
        !solver.should_restart(),
        "geometric: 99 < 100, should not restart"
    );
    solver.conflicts_since_restart = 100;
    assert!(
        solver.should_restart(),
        "geometric: 100 >= 100, should restart"
    );

    // Restart 1: threshold = 100 * 1.1^1 = 110
    solver.cold.restarts = 1;
    solver.conflicts_since_restart = 109;
    assert!(
        !solver.should_restart(),
        "geometric: 109 < 110, should not restart"
    );
    solver.conflicts_since_restart = 110;
    assert!(
        solver.should_restart(),
        "geometric: 110 >= 110, should restart"
    );

    // Restart 5: threshold = 100 * 1.1^5 ≈ 161
    solver.cold.restarts = 5;
    solver.conflicts_since_restart = 160;
    assert!(
        !solver.should_restart(),
        "geometric: 160 < 161, should not restart"
    );
    solver.conflicts_since_restart = 162;
    assert!(
        solver.should_restart(),
        "geometric: 162 >= 161, should restart"
    );
}

#[test]
fn test_should_restart_geometric_schedule_clamps_large_restart_exponent() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 1;
    solver.set_geometric_restarts(100.0, 1.1);

    // A u64 -> i32 cast would wrap this to a negative exponent and collapse
    // the threshold toward zero, causing a restart storm in long-running jobs.
    solver.cold.restarts = i32::MAX as u64 + 1;

    assert!(
        !solver.should_restart(),
        "geometric restart exponent overflow must not collapse the threshold"
    );
}

#[test]
fn test_should_restart_pure_ignores_theory_heavy_luby_policy() {
    let setup = |solver: &mut Solver| {
        solver.num_conflicts = 200;
        solver.conflicts_since_restart = THEORY_LUBY_BASE;
        solver.stable_mode = false;
        solver.cold.stable_phase_length = 1_000_000;
        solver.cold.stable_mode_start_conflicts = 0;
        solver.cold.glucose_restarts = true;
        solver.cold.lbd_ema_slow = 10.0;
        solver.cold.lbd_ema_fast = 10.0;
        solver.cold.theory_conflict_ratio = 1.0;
        solver.cold.ext_conflict_count = 21;
    };

    let mut theory_solver = Solver::new(4);
    setup(&mut theory_solver);
    assert!(
        theory_solver.should_restart(),
        "theory path should honor the theory-heavy Luby restart threshold"
    );

    let mut pure_solver = Solver::new(4);
    setup(&mut pure_solver);
    assert!(
        !pure_solver.should_restart_pure(),
        "pure path must not restart from theory-heavy policy state"
    );
}

#[test]
fn test_do_restart_pure_does_not_advance_theory_luby_index() {
    let setup = |solver: &mut Solver| {
        solver.num_conflicts = 200;
        solver.conflicts_since_restart = THEORY_LUBY_BASE;
        solver.cold.theory_conflict_ratio = 1.0;
        solver.cold.ext_conflict_count = 21;
    };

    let mut theory_solver = Solver::new(4);
    setup(&mut theory_solver);
    theory_solver.do_restart();
    assert_eq!(
        theory_solver.cold.theory_luby_idx, 2,
        "theory restart should advance the dedicated theory Luby index"
    );

    let mut pure_solver = Solver::new(4);
    setup(&mut pure_solver);
    pure_solver.do_restart_pure();
    assert_eq!(
        pure_solver.cold.theory_luby_idx, 1,
        "pure restart must leave the dedicated theory Luby index untouched"
    );
}

#[test]
fn test_pick_phase_focused_mode_uses_saved_phase() {
    // Kissat-style phase cycling (decide.c:178-187): in focused mode,
    // (mode_switch_count >> 1) & 7 selects an 8-slot cycle.
    // Slots 1 and 3 force fixed polarity; other slots use saved phase.
    let mut solver = Solver::new(1);
    let var = Variable(0);

    solver.stable_mode = false;

    // Slot 1 forces positive regardless of saved phase
    solver.cold.mode_switch_count = 2; // (2 >> 1) & 7 = 1
    solver.phase[var.index()] = -1;
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "focused mode slot 1 should force positive (Kissat INITIAL_PHASE)",
    );

    // Slot 3 forces negative regardless of saved phase
    solver.cold.mode_switch_count = 6; // (6 >> 1) & 7 = 3
    solver.phase[var.index()] = 1;
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "focused mode slot 3 should force negative (Kissat inverted)",
    );

    // Slot 0 uses saved phase
    solver.cold.mode_switch_count = 0; // (0 >> 1) & 7 = 0
    solver.phase[var.index()] = -1;
    assert_eq!(
        solver.pick_phase(var),
        Literal::negative(var),
        "focused mode slot 0 should use saved phase (negative)",
    );

    // No saved phase on non-override slot -> default positive
    solver.phase[var.index()] = 0;
    assert_eq!(
        solver.pick_phase(var),
        Literal::positive(var),
        "focused mode with no saved phase should default to positive",
    );
}

#[test]
fn test_should_restart_mode_switch_increments_counter_and_starts_random_burst() {
    let mut solver = Solver::new(1);

    solver.num_conflicts = solver.cold.restart_min_conflicts;
    solver.conflicts_since_restart = 1;
    solver.stable_mode = false;
    solver.cold.stable_phase_length = 1;
    solver.cold.stable_mode_start_conflicts = 0;

    assert!(
        !solver.should_restart(),
        "mode switch alone should not force a restart",
    );
    assert!(solver.stable_mode, "first switch should enter stable mode");
    assert_eq!(solver.cold.mode_switch_count, 1);
    assert_eq!(solver.cold.random_decision_phases, 1);
    assert!(
        solver.cold.randomized_deciding > 0,
        "mode switch should start a non-empty random decision burst",
    );
    assert_eq!(
        solver.cold.next_random_decision, solver.num_conflicts,
        "first mode switch should reuse the shared random-sequence scheduler",
    );

    let first_burst = solver.cold.randomized_deciding;

    solver.num_conflicts += 1;
    solver.conflicts_since_restart = 1;
    solver.search_ticks[usize::from(solver.stable_mode)] = solver.cold.stabilize_tick_limit + 1;

    assert!(
        !solver.should_restart(),
        "switching back to focused mode should not imply an immediate restart",
    );
    assert!(
        !solver.stable_mode,
        "second switch should return to focused mode",
    );
    assert_eq!(solver.cold.mode_switch_count, 2);
    assert_eq!(solver.cold.random_decision_phases, 2);
    assert!(
        solver.cold.randomized_deciding > 0 && solver.cold.randomized_deciding != first_burst,
        "second mode switch should refresh the random burst state",
    );
}

#[test]
fn test_bootstrapped_focused_mode_switch_uses_conflict_limit_not_ticks() {
    use super::super::rephase::nlogpow4;

    let mut solver = Solver::new(4);

    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.stable_mode = false;
    solver.cold.glucose_restarts = true;
    solver.cold.stable_phase_length = 10;
    solver.cold.stable_mode_start_conflicts = 0;
    solver.search_ticks[usize::from(false)] = 25;

    assert!(
        !solver.should_restart(),
        "initial mode switch should not force a restart"
    );
    assert!(solver.stable_mode, "first switch should enter stable mode");
    assert_eq!(solver.cold.mode_switch_count, 1);
    assert_eq!(solver.cold.stable_phase_count, 1);

    let stable_tick_limit = solver.cold.stabilize_tick_limit;
    solver.num_conflicts += 1;
    solver.conflicts_since_restart = 1;
    solver.search_ticks[usize::from(true)] = stable_tick_limit;

    assert!(
        !solver.should_restart(),
        "stable phase should switch on the absolute tick limit"
    );
    assert!(
        !solver.stable_mode,
        "second switch should return to focused mode"
    );
    assert_eq!(solver.cold.mode_switch_count, 2);

    let expected_focused_limit = solver
        .num_conflicts
        .saturating_add(solver.cold.stable_phase_length * nlogpow4(1));
    assert_eq!(
        solver.cold.stabilize_tick_limit, expected_focused_limit,
        "focused phase limit should be an absolute conflict limit"
    );

    solver.search_ticks[usize::from(false)] = expected_focused_limit + 1000;
    solver.num_conflicts = expected_focused_limit - 1;
    solver.conflicts_since_restart = 1;

    assert!(
        !solver.should_restart(),
        "focused phase must not switch only because focused ticks exceed the stored limit"
    );
    assert!(
        !solver.stable_mode,
        "focused phase should remain active until the conflict limit"
    );
    assert_eq!(solver.cold.mode_switch_count, 2);

    solver.num_conflicts = expected_focused_limit;
    solver.conflicts_since_restart = 1;

    assert!(
        !solver.should_restart(),
        "focused conflict-limit switch should not force a restart"
    );
    assert!(
        solver.stable_mode,
        "focused phase should switch when conflicts reach the limit"
    );
    assert_eq!(solver.cold.mode_switch_count, 3);
}
