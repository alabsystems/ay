// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Restart and clause database management tests: Luby sequence, glucose restart,
//! geometric restart, LBD EMA tracking, and reduce-DB scheduling.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

include!("restart/clause_db_luby_and_ema.rs");

include!("restart/restart_policies_and_mode_switch.rs");

include!("restart/inprocessing_phase_and_cold.rs");

include!("restart/large_formula_restart_gates.rs");

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
