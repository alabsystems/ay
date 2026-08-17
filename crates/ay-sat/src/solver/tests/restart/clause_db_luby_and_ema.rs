// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver::tests::restart` to preserve test FQNs.

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
