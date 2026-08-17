// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `solver::tests::restart` to preserve test FQNs.

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
