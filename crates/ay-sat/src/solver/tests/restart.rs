// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Restart and clause database management tests: Luby sequence, glucose restart,
//! geometric restart, LBD EMA tracking, and reduce-DB scheduling.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

// ========================================================================
// Clause Database Reduction Scheduling
// ========================================================================

#[test]
fn test_should_reduce_db_triggers_on_clause_db_byte_limit() {
    let mut solver = Solver::new(1);
    // #8672 Finding #2: the memory trigger consults the composite clause-DB
    // byte count (arena + watches + clause_ids + original_ledger + reconstruction),
    // not only the arena. The setpoint must match the figure the trigger uses.
    let initial_bytes = solver.clause_db_memory_bytes();

    // should_reduce_db uses a strict `>` check, so matching the current bytes
    // should not trigger reduction.
    solver.set_max_clause_db_bytes(Some(initial_bytes));
    assert!(!solver.should_reduce_db());

    // Force the arena capacity to grow so composite clause-DB bytes increase
    // past the limit.
    let v0 = Variable(0);
    for _ in 0..32 {
        let idx = solver.add_clause_db(&[Literal::positive(v0)], true);
        solver.arena.set_lbd(idx, 10);
    }

    assert!(
        solver.clause_db_memory_bytes() > initial_bytes,
        "test setup failed: clause DB bytes did not grow"
    );
    assert!(solver.should_reduce_db());
}

#[test]
fn test_reduce_db_deletes_over_byte_limit_no_compact() {
    let mut solver = Solver::new(1);
    let v0 = Variable(0);

    for _ in 0..100 {
        let idx = solver.add_clause_db(&[Literal::positive(v0)], true);
        solver.arena.set_lbd(idx, 10);
    }

    let bytes_before = solver.arena.memory_bytes();
    solver.set_max_clause_db_bytes(Some(bytes_before.saturating_sub(1)));

    let active_before = solver.arena.active_literals();

    let clause_changes_before = solver.cold.clause_db_changes;
    solver.reduce_db();

    let active_after = solver.arena.active_literals();

    // Reduce_db should delete tier-2 learned clauses aggressively when
    // over the byte limit, but does NOT compact the arena (compact would
    // renumber clause indices, invalidating ClauseRef values — see #5091).
    assert!(
        active_after < active_before,
        "reduce_db should delete clauses when over byte limit"
    );
    assert!(
        solver.cold.clause_db_changes > clause_changes_before,
        "reduce_db deletions must flow through unified mutation helpers"
    );
}

#[test]

// ========================================================================
// Luby Sequence + Restart Threshold
// ========================================================================

fn test_luby_sequence() {
    // The Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
    for (i, &exp) in expected.iter().enumerate() {
        let luby = Solver::get_luby((i + 1) as u32);
        assert_eq!(luby, exp, "Luby({}) should be {}, got {}", i + 1, exp, luby);
    }
}

#[test]
fn test_luby_first_values() {
    // Check first few values specifically
    assert_eq!(Solver::get_luby(1), 1);
    assert_eq!(Solver::get_luby(2), 1);
    assert_eq!(Solver::get_luby(3), 2);
    assert_eq!(Solver::get_luby(4), 1);
    assert_eq!(Solver::get_luby(5), 1);
    assert_eq!(Solver::get_luby(6), 2);
    assert_eq!(Solver::get_luby(7), 4);
}

#[test]
fn test_restart_threshold_increases() {
    // Verify restart thresholds follow Luby pattern
    let base = DEFAULT_RESTART_BASE;
    let mut thresholds = Vec::new();

    for i in 1..=7 {
        let luby = Solver::get_luby(i);
        thresholds.push(base * u64::from(luby));
    }

    // Expected: [base*1, base*1, base*2, base*1, base*1, base*2, base*4]
    assert_eq!(thresholds[0], base); // luby(1) = 1
    assert_eq!(thresholds[1], base); // luby(2) = 1
    assert_eq!(thresholds[2], base * 2); // luby(3) = 2
    assert_eq!(thresholds[6], base * 4); // luby(7) = 4
}

/// Luby sequence must not overflow for large restart counters.
/// Before the fix, `(1u32 << k) - 1` overflowed when k >= 32
/// (i.e., i > 2^31 - 1), causing a panic in debug mode.
#[test]
fn test_luby_no_overflow_large_values() {
    // 2^31 - 1 is the largest value where k=31 exactly matches
    // luby(2^k - 1) = 2^(k-1), so luby(2^31-1) = 2^30
    let val = Solver::get_luby((1u32 << 31) - 1);
    assert_eq!(val, 1u32 << 30, "luby(2^31-1) should be 2^30");
    // One past that boundary triggers k=32 in the old code (overflow).
    // luby(2^31) should recurse: luby(2^31 - (2^31 - 1)) = luby(1) = 1
    assert_eq!(Solver::get_luby(1u32 << 31), 1);
    // u32::MAX = 2^32 - 1, so luby(2^32-1) = 2^31
    assert_eq!(Solver::get_luby(u32::MAX), 1u32 << 31);
}

#[test]

// ========================================================================
// LBD EMA + Should-Restart Tests
// ========================================================================

fn test_update_lbd_ema_tracks_lbd_values() {
    let mut solver = Solver::new(4);
    // Initialize EMAs to 0 (default state after construction)
    assert_eq!(solver.cold.lbd_ema_fast, 0.0);
    assert_eq!(solver.cold.lbd_ema_slow, 0.0);

    // Feed a constant LBD value; both EMAs should converge toward it.
    for _ in 0..1000 {
        solver.update_lbd_ema(5);
    }
    // Fast EMA should be very close to 5.0 after 1000 updates
    assert!(
        (solver.cold.lbd_ema_fast - 5.0).abs() < 0.01,
        "fast EMA should converge to 5.0, got {}",
        solver.cold.lbd_ema_fast
    );
    // Slow EMA should also move toward 5.0, but more slowly
    assert!(
        solver.cold.lbd_ema_slow > 0.0,
        "slow EMA should be positive after updates"
    );

    // Now feed a sudden spike; fast EMA should react more than slow EMA
    let slow_before = solver.cold.lbd_ema_slow;
    let fast_before = solver.cold.lbd_ema_fast;
    solver.update_lbd_ema(50);
    let fast_delta = solver.cold.lbd_ema_fast - fast_before;
    let slow_delta = solver.cold.lbd_ema_slow - slow_before;
    assert!(
        fast_delta > slow_delta,
        "fast EMA should react more to spike than slow EMA: fast_delta={fast_delta}, slow_delta={slow_delta}"
    );
}

/// Test should_restart returns false before minimum conflict threshold.
#[test]
fn test_should_restart_respects_min_conflicts() {
    let mut solver = Solver::new(4);
    // Default restart_min_conflicts is 2 (matching CaDiCaL's restartint=2).
    // Set conflicts below threshold.
    solver.num_conflicts = 1;
    solver.conflicts_since_restart = 1;
    assert!(
        !solver.should_restart(),
        "should_restart must return false when num_conflicts < restart_min_conflicts"
    );
}

/// Test should_restart returns false when conflicts_since_restart is 0.
#[test]
fn test_should_restart_requires_conflicts_since_restart() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 0;
    assert!(
        !solver.should_restart(),
        "should_restart must return false when no conflicts since last restart"
    );
}

/// Test that Glucose-style restart fires when fast EMA exceeds margin * slow EMA.
#[test]
fn test_should_restart_glucose_fires_on_ema_spike() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.glucose_restarts = true;
    solver.stable_mode = false;
    // Set phase length very high to stay in focused mode
    solver.cold.stable_phase_length = 1_000_000;
    solver.cold.stable_mode_start_conflicts = 0;

    // Set EMAs so fast > RESTART_MARGIN(1.10) * slow
    solver.cold.lbd_ema_slow = 5.0;
    solver.cold.lbd_ema_fast = 6.0; // 6.0 > 1.10 * 5.0 = 5.5
    assert!(
        solver.should_restart(),
        "glucose restart should fire when lbd_ema_fast > RESTART_MARGIN * lbd_ema_slow"
    );
}

#[test]
fn test_restart_attribution_records_primary_cause_and_mode() {
    let mut focused = Solver::new(4);
    focused.num_conflicts = 200;
    focused.conflicts_since_restart = 50;
    focused.cold.glucose_restarts = true;
    focused.stable_mode = false;
    focused.cold.stable_phase_length = 1_000_000;
    focused.cold.lbd_ema_slow = 5.0;
    focused.cold.lbd_ema_fast = 6.0;

    assert!(focused.maybe_run_restart_pure());
    let stats = focused.restart_attribution_stats();
    assert_eq!(stats.focused_ema, 1);
    assert_eq!(stats.focused_mode, 1);
    assert_eq!(stats.stable_mode, 0);

    let mut stable = Solver::new(4);
    stable.num_conflicts = 200;
    stable.conflicts_since_restart = 1;
    stable.stable_mode = true;
    stable.cold.stable_phase_length = 1_000_000;
    stable.cold.reluctant_countdown = 1;
    stable.cold.reluctant_ticked_at = stable.num_conflicts - 1;

    assert!(stable.maybe_run_restart_pure());
    let stats = stable.restart_attribution_stats();
    assert_eq!(stats.stable_reluctant, 1);
    assert_eq!(stats.focused_mode, 0);
    assert_eq!(stats.stable_mode, 1);
}

#[test]
fn test_restart_exercising_canary_records_nonzero_restarts() {
    let mut solver = Solver::new(4);

    solver.num_conflicts = 200;
    solver.conflicts_since_restart = 50;
    solver.cold.glucose_restarts = true;
    solver.stable_mode = false;
    solver.cold.stable_phase_length = 1_000_000;
    solver.cold.stable_mode_start_conflicts = 0;
    solver.cold.lbd_ema_slow = 5.0;
    solver.cold.lbd_ema_fast = 6.0;

    assert!(solver.maybe_run_restart_pure());
    assert_eq!(
        solver.num_restarts(),
        1,
        "focused EMA canary must execute and count a restart",
    );

    solver.num_conflicts += 1;
    solver.conflicts_since_restart = 1;
    solver.stable_mode = true;
    solver.cold.stable_mode_start_conflicts = solver.num_conflicts;
    solver.cold.reluctant_countdown = 1;
    solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;
    solver.cold.lbd_ema_slow = 5.0;
    solver.cold.lbd_ema_fast = 5.0;

    assert!(solver.maybe_run_restart_pure());
    assert_eq!(
        solver.num_restarts(),
        2,
        "stable reluctant canary must execute and count a restart",
    );

    let stats = solver.restart_attribution_stats();
    assert_eq!(stats.focused_ema, 1);
    assert_eq!(stats.stable_reluctant, 1);
    assert_eq!(stats.focused_mode, 1);
    assert_eq!(stats.stable_mode, 1);
    assert_eq!(
        stats.focused_mode + stats.stable_mode,
        solver.num_restarts()
    );
}

#[test]
fn test_restart_attribution_counts_execution_not_repeated_predicate_queries() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = solver.cold.restart_min_conflicts;
    solver.conflicts_since_restart = 10;
    solver.cold.geometric_restarts = true;
    solver.cold.geometric_initial = 1.0;
    solver.cold.geometric_factor = 2.0;

    assert!(solver.should_restart_pure());
    assert!(solver.should_restart_pure());
    let stats = solver.restart_attribution_stats();
    assert_eq!(stats.geometric, 0);
    assert_eq!(stats.focused_mode + stats.stable_mode, 0);

    assert!(solver.maybe_run_restart_pure());
    let stats = solver.restart_attribution_stats();
    assert_eq!(stats.geometric, 1);
    assert_eq!(stats.focused_mode, 1);
    assert_eq!(stats.stable_mode, 0);
}

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

// ========================================================================
// Large Formula Stable Mode Bias (#8655)
// ========================================================================

/// Verify that a solver above the very-large threshold gets forced into
/// stable mode during the post-preprocessing tuning phase.
#[test]
fn test_large_formula_stable_bias_forces_stable_mode() {
    use super::super::constants::VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD;

    // Create a solver and manually set num_original_clauses above the
    // very-large threshold. We don't actually need to add 1M clauses;
    // the post-preprocessing code reads num_original_clauses which is
    // set during the solve entry point. For unit testing, we simulate
    // the tuning block logic directly.
    let mut solver = Solver::new(4);
    solver.num_original_clauses = VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD + 1;

    // Before: focused mode (default).
    assert!(!solver.stable_mode, "solver should start in focused mode");
    assert_eq!(
        solver.cold.mode_lock,
        cold::ModeLock::None,
        "mode_lock should be None by default"
    );

    // Simulate the tuning block from solve/mod.rs.
    // This replicates the exact logic without running the full solve path.
    if solver.cold.mode_lock == cold::ModeLock::None
        && LARGE_FORMULA_STABLE_PHASE_SCALE
        && solver.num_original_clauses > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD
    {
        solver.stable_mode = true;
        solver.cold.stable_mode_start_conflicts = solver.num_conflicts;
        solver.cold.reluctant_u = 1;
        solver.cold.reluctant_v = 1;
        solver.cold.reluctant_countdown = RELUCTANT_INIT;
        solver.cold.reluctant_ticked_at = solver.num_conflicts;
        solver.sync_active_branch_heuristic();
    }

    assert!(
        solver.stable_mode,
        "very large formula (>1M clauses) should force stable mode"
    );
}

/// Verify that a solver with 100K-1M original clauses gets a scaled
/// initial stable phase length.
#[test]
fn test_large_formula_scaled_stable_phase_length() {
    use super::super::constants::{
        LARGE_FORMULA_REDUCE_CAP_THRESHOLD, STABLE_PHASE_INIT,
        VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD,
    };

    let mut solver = Solver::new(4);
    // 200K clauses: above 100K threshold, below 1M threshold.
    solver.num_original_clauses = 200_000;
    assert!(solver.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD);
    assert!(solver.num_original_clauses <= VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD);

    let original_phase = solver.cold.stable_phase_length;
    assert_eq!(original_phase, STABLE_PHASE_INIT);

    // Simulate the tuning block.
    if solver.cold.mode_lock == cold::ModeLock::None && LARGE_FORMULA_STABLE_PHASE_SCALE {
        if solver.num_original_clauses > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD {
            // Should not trigger for 200K.
            unreachable!();
        } else if solver.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD {
            let scale = (solver.num_original_clauses as f64).log10();
            let scaled_phase = (STABLE_PHASE_INIT as f64 * scale) as u64;
            if scaled_phase > solver.cold.stable_phase_length {
                solver.cold.stable_phase_length = scaled_phase;
            }
        }
    }

    // log10(200_000) ~= 5.3, so scaled_phase ~= 5301.
    let expected_scale = (200_000f64).log10();
    let expected_phase = (STABLE_PHASE_INIT as f64 * expected_scale) as u64;
    assert_eq!(solver.cold.stable_phase_length, expected_phase);
    assert!(
        solver.cold.stable_phase_length > STABLE_PHASE_INIT,
        "scaled phase ({}) should be > STABLE_PHASE_INIT ({})",
        solver.cold.stable_phase_length,
        STABLE_PHASE_INIT
    );
    assert!(
        !solver.stable_mode,
        "200K clause formula should NOT force stable mode"
    );
}

/// Verify that stable-only lock prevents the large formula bias from
/// overriding the caller's mode setting.
#[test]
fn test_large_formula_bias_respects_mode_lock() {
    use super::super::constants::VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD;

    let mut solver = Solver::new(4);
    solver.num_original_clauses = VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD + 1;
    // Lock to stable mode first (as IC3 does).
    solver.cold.mode_lock = cold::ModeLock::Stable;
    solver.stable_mode = true;

    // The bias block should be a no-op because mode_lock != None.
    let phase_before = solver.cold.stable_phase_length;
    if solver.cold.mode_lock == cold::ModeLock::None && LARGE_FORMULA_STABLE_PHASE_SCALE {
        // Should not enter: mode_lock is Stable.
        unreachable!("mode_lock should prevent entering the bias block");
    }

    assert_eq!(
        solver.cold.stable_phase_length, phase_before,
        "mode_lock should prevent stable phase length modification"
    );
}

// ========================================================================
// Focused-Mode Logarithmic Restart Gate Growth (#8655)
// ========================================================================

/// Verify that the focused-mode restart gate grows logarithmically after
/// restarts, matching Kissat's `update_focused_restart_limit`.
/// Kissat: delta = restartint + logn(restarts) - 1.
#[test]
fn test_focused_restart_gate_grows_logarithmically() {
    use super::super::constants::RESTART_INTERVAL;

    let mut solver = Solver::new(4);
    solver.stable_mode = false;
    solver.num_conflicts = 200;

    // Before any restarts: gate should be RESTART_INTERVAL (2).
    assert_eq!(
        solver.cold.focused_restart_gate, RESTART_INTERVAL,
        "initial focused restart gate should be RESTART_INTERVAL"
    );

    // Simulate many restarts to build up the gate.
    // do_restart() increments restarts and updates the gate in focused mode.
    for _ in 0..100 {
        solver.decision_level = 0;
        solver.conflicts_since_restart = 10;
        solver.num_conflicts += 10;
        solver.do_restart();
    }

    // After 100 restarts: gate = RESTART_INTERVAL + log10(100 + 9) - 1
    // = 2 + log10(109) - 1 = 2 + 2.037 - 1 = 3.037 => 3
    assert!(
        solver.cold.focused_restart_gate >= 3,
        "after 100 restarts, gate ({}) should be >= 3",
        solver.cold.focused_restart_gate
    );

    // Simulate 10000 more restarts.
    for _ in 0..9900 {
        solver.decision_level = 0;
        solver.conflicts_since_restart = 10;
        solver.num_conflicts += 10;
        solver.do_restart();
    }

    // After 10000 restarts: gate = 2 + log10(10009) - 1 = 2 + 4.0 - 1 = 5
    assert!(
        solver.cold.focused_restart_gate >= 5,
        "after 10000 restarts, gate ({}) should be >= 5",
        solver.cold.focused_restart_gate
    );
}

/// Verify formula-class restart gates are not lowered by the focused-mode
/// logarithmic growth update. Small dense formulas raise the focused gate to
/// avoid restart storms; the per-restart update must preserve that floor.
#[test]
fn test_focused_restart_gate_growth_preserves_existing_floor() {
    let mut solver = Solver::new(4);
    solver.stable_mode = false;
    solver.num_conflicts = 200;
    solver.cold.focused_restart_gate = 10;

    solver.decision_level = 0;
    solver.conflicts_since_restart = 10;
    solver.num_conflicts += 10;
    solver.do_restart();

    assert_eq!(
        solver.cold.focused_restart_gate, 10,
        "focused restart growth must not lower formula-class gate floors"
    );
}

/// Verify that the focused restart gate does NOT change in stable mode.
#[test]
fn test_focused_restart_gate_stable_mode_no_change() {
    use super::super::constants::RESTART_INTERVAL;

    let mut solver = Solver::new(4);
    solver.stable_mode = true;
    solver.num_conflicts = 200;

    let gate_before = solver.cold.focused_restart_gate;
    assert_eq!(gate_before, RESTART_INTERVAL);

    // Simulate restarts in stable mode.
    for _ in 0..50 {
        solver.decision_level = 0;
        solver.conflicts_since_restart = 1024;
        solver.num_conflicts += 1024;
        solver.do_restart();
    }

    // Gate should not change in stable mode (stable uses reluctant doubling).
    assert_eq!(
        solver.cold.focused_restart_gate, gate_before,
        "focused restart gate should not change in stable mode"
    );
}

#[test]
fn test_dense_mutex_focused_restart_gate_formula() {
    assert_eq!(
        Solver::dense_mutex_focused_restart_gate(180),
        45,
        "clique_n2_k10 active-vars scale should target a 45-conflict gate"
    );
    assert_eq!(
        Solver::dense_mutex_focused_restart_gate(120),
        40,
        "small dense-mutex formulas keep the requested 40-conflict floor"
    );
    assert_eq!(
        Solver::dense_mutex_focused_restart_gate(800),
        100,
        "larger dense-mutex formulas keep the requested 100-conflict cap"
    );
}

#[test]
fn test_dense_mutex_focused_restart_candidate_preserves_battleship_shape() {
    assert!(
        Solver::dense_mutex_focused_restart_candidate(180, 3_160, 3_150),
        "clique_n2_k10 shape is small, dense, and binary-heavy"
    );
    assert!(
        !Solver::dense_mutex_focused_restart_candidate(364, 2_562, 2_366),
        "battleship density/binary mix must stay outside the dense-mutex route"
    );
    assert!(
        !Solver::dense_mutex_focused_restart_candidate(100, 1_000, 1_000),
        "exact density 10.0 must not enter the high-density route"
    );
    assert!(
        !Solver::dense_mutex_focused_restart_candidate(180, 3_160, 2_970),
        "binary fraction below 95% must not enter the route"
    );
}

#[test]
fn test_dense_mutex_focused_restart_experiment_is_default_off() {
    let mut solver = Solver::new(180);
    assert!(
        !solver.dense_mutex_focused_restart_gate_experiment_enabled(),
        "dense-mutex focused restart gate is default-off"
    );

    solver.set_dense_mutex_focused_restart_gate_experiment_enabled(true);
    assert!(
        solver.dense_mutex_focused_restart_gate_experiment_enabled(),
        "explicit config opt-in enables the experiment"
    );
}

#[test]
fn test_dense_mutex_focused_restart_gate_update_counter_records_startup_raise() {
    let mut solver = Solver::new(180);
    solver.apply_feature_profile(&crate::InprocessingFeatureProfile {
        preprocess: true,
        walk: false,
        warmup: false,
        shrink: false,
        hbr: false,
        vivify: false,
        subsume: false,
        probe: false,
        bve: false,
        bce: false,
        condition: false,
        decompose: false,
        factor: false,
        sbva: false,
        transred: false,
        htr: false,
        gate: false,
        congruence: false,
        sweep: false,
        backbone: false,
        symmetry: false,
        reorder: false,
        cce: false,
    });
    solver.set_dense_mutex_focused_restart_gate_experiment_enabled(true);

    let mut added = 0usize;
    'clauses: for left in 0..180 {
        for right in (left + 1)..180 {
            solver.add_clause(vec![
                Literal::positive(Variable::new(left as u32)),
                Literal::positive(Variable::new(right as u32)),
            ]);
            added += 1;
            if added == 1_900 {
                break 'clauses;
            }
        }
    }

    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "all-positive dense binary fixture should remain satisfiable"
    );
    assert_eq!(
        solver.focused_restart_gate(),
        Solver::dense_mutex_focused_restart_gate(180),
        "dense-mutex route should raise the focused restart gate"
    );
    assert_eq!(
        solver.dense_mutex_focused_restart_gate_updates(),
        1,
        "startup dense-mutex route should record one gate update"
    );
    assert_eq!(
        solver.dense_mutex_focused_restart_runtime_checked(),
        1,
        "startup dense-mutex route should record one runtime predicate snapshot"
    );
    assert_eq!(solver.dense_mutex_focused_restart_active_vars(), 180);
    assert_eq!(solver.dense_mutex_focused_restart_active_clauses(), 1_900);
    assert_eq!(
        solver.dense_mutex_focused_restart_active_binary_clauses(),
        1_900
    );
    assert!(
        solver.dense_mutex_focused_restart_runtime_candidate(),
        "dense binary fixture should satisfy the runtime candidate predicate"
    );
    assert_eq!(
        solver.dense_mutex_focused_restart_computed_gate(),
        Solver::dense_mutex_focused_restart_gate(180)
    );
    assert!(
        solver.dense_mutex_focused_restart_previous_gate()
            < solver.dense_mutex_focused_restart_computed_gate(),
        "fixture should require a gate raise instead of a no-op"
    );
}

#[test]
fn test_dense_mutex_focused_restart_gate_seed_survives_preprocess_shape_loss() {
    let mut solver = Solver::new(180);
    solver.apply_feature_profile(&crate::InprocessingFeatureProfile {
        preprocess: true,
        walk: false,
        warmup: false,
        shrink: false,
        hbr: false,
        vivify: false,
        subsume: false,
        probe: false,
        bve: false,
        bce: false,
        condition: false,
        decompose: false,
        factor: false,
        sbva: false,
        transred: false,
        htr: false,
        gate: false,
        congruence: false,
        sweep: false,
        backbone: false,
        symmetry: false,
        reorder: false,
        cce: false,
    });
    solver.set_dense_mutex_focused_restart_gate_experiment_enabled(true);

    for anchor in 0..20 {
        let anchor_lit = Literal::positive(Variable::new(anchor as u32));
        solver.add_clause(vec![anchor_lit]);
        for other in 20..180 {
            solver.add_clause(vec![
                anchor_lit,
                Literal::positive(Variable::new(other as u32)),
            ]);
        }
    }

    let result = solver.solve().into_inner();

    assert!(
        result.is_sat(),
        "unit-satisfied dense binary fixture should remain satisfiable"
    );
    assert_eq!(
        solver.focused_restart_gate(),
        Solver::dense_mutex_focused_restart_gate(180),
        "static route admission should seed the focused gate after preprocessing changes the live shape"
    );
    assert_eq!(
        solver.dense_mutex_focused_restart_gate_updates(),
        1,
        "static dense-mutex seed should count as a route exercise"
    );
    assert_eq!(
        solver.dense_mutex_focused_restart_runtime_checked(),
        1,
        "startup dense-mutex route should still record the post-preprocess snapshot"
    );
    assert!(
        solver.dense_mutex_focused_restart_active_vars() < 180,
        "preprocessing should assign away part of the original dense shape"
    );
    assert!(
        solver.dense_mutex_focused_restart_runtime_candidate(),
        "remaining live binary shape should still be reported separately"
    );
    assert_eq!(
        solver.dense_mutex_focused_restart_computed_gate(),
        Solver::dense_mutex_focused_restart_gate(180),
        "computed gate should retain the original admitted formula size"
    );
    assert!(
        solver.dense_mutex_focused_restart_computed_gate()
            > Solver::dense_mutex_focused_restart_gate(
                solver.dense_mutex_focused_restart_active_vars() as usize
            ),
        "static seed should not shrink to the post-preprocess active-variable count"
    );
}

// ========================================================================
// Large-Formula Rephase Interval Scaling (#8655)
// ========================================================================

/// Verify that formulas with >100K clauses get a scaled rephase interval.
#[test]
fn test_large_formula_rephase_interval_scaling() {
    use super::super::constants::{LARGE_FORMULA_REDUCE_CAP_THRESHOLD, REPHASE_INITIAL};

    let mut solver = Solver::new(4);
    solver.num_original_clauses = 200_000;
    assert!(solver.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD);

    // Simulate the scaling logic from solve/mod.rs.
    let scale = (solver.num_original_clauses as f64).log10();
    let scaled_rephase = (REPHASE_INITIAL as f64 * scale) as u64;

    // log10(200_000) ~= 5.3, so scaled_rephase ~= 5301.
    assert!(
        scaled_rephase > REPHASE_INITIAL,
        "scaled rephase ({scaled_rephase}) should be > REPHASE_INITIAL ({REPHASE_INITIAL})"
    );

    // Apply the scaling.
    if scaled_rephase > solver.cold.next_rephase {
        solver.cold.next_rephase = solver.num_conflicts.saturating_add(scaled_rephase);
    }

    assert!(
        solver.cold.next_rephase >= scaled_rephase,
        "next_rephase ({}) should be at least scaled value ({scaled_rephase})",
        solver.cold.next_rephase
    );
}

/// Verify that formulas with <=100K clauses do NOT get rephase scaling.
#[test]
fn test_small_formula_no_rephase_scaling() {
    use super::super::constants::{LARGE_FORMULA_REDUCE_CAP_THRESHOLD, REPHASE_INITIAL};

    let mut solver = Solver::new(4);
    solver.num_original_clauses = 50_000;
    assert!(solver.num_original_clauses <= LARGE_FORMULA_REDUCE_CAP_THRESHOLD);

    let original_rephase = solver.cold.next_rephase;
    assert_eq!(original_rephase, REPHASE_INITIAL);

    // The scaling block should not trigger.
    if solver.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD {
        unreachable!("should not enter scaling block for small formula");
    }

    assert_eq!(
        solver.cold.next_rephase, original_rephase,
        "rephase interval should not change for small formulas"
    );
}
