// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing skip-reason contract tests.

use super::*;
use crate::solver::inprocessing::{
    BceSkipReason, BveSkipReason, ProbeSkipReason, SubsumeSkipReason, TransredSkipReason,
};

const SUBSUME_TICK_THRESHOLD: u64 = 2;
const TRANSRED_TICK_THRESHOLD: u64 = 2;
const BCE_TICK_THRESHOLD: u64 = 2;

// ======== Probe skip reason tests (#8148) ========

#[test]
fn test_probe_skip_reason_disabled_flag() {
    let mut solver: Solver = Solver::new(3);
    solver.set_probe_enabled(false);
    assert_eq!(
        solver.probe_skip_reason(),
        Some(ProbeSkipReason::DisabledFlag),
        "probe should report DisabledFlag when disabled",
    );
}

#[test]
fn test_probe_skip_reason_interval_not_due() {
    let mut solver: Solver = Solver::new(3);
    solver.set_probe_enabled(true);
    solver.num_conflicts = 0; // interval not reached
    assert_eq!(
        solver.probe_skip_reason(),
        Some(ProbeSkipReason::IntervalNotDue),
        "probe should report IntervalNotDue when conflicts < next_conflict",
    );
}

#[test]
fn test_probe_skip_reason_fires_when_interval_due() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.set_probe_enabled(true);
    solver.num_conflicts = PROBE_INTERVAL;
    // PROBE_TICK_THRESHOLD=0 means threshold gate is always satisfied (no-op).
    assert_eq!(
        solver.probe_skip_reason(),
        None,
        "probe should fire when interval is due (threshold=0 is no-op)",
    );
}

// ======== Subsume skip reason tests (#8148) ========

#[test]
fn test_subsume_skip_reason_disabled_flag() {
    let mut solver: Solver = Solver::new(3);
    solver.set_subsume_enabled(false);
    assert_eq!(
        solver.subsume_skip_reason(),
        Some(SubsumeSkipReason::DisabledFlag),
        "subsume should report DisabledFlag when disabled",
    );
}

#[test]
fn test_subsume_skip_reason_interval_not_due() {
    let mut solver: Solver = Solver::new(3);
    solver.set_subsume_enabled(true);
    solver.num_conflicts = 0;
    assert_eq!(
        solver.subsume_skip_reason(),
        Some(SubsumeSkipReason::IntervalNotDue),
        "subsume should report IntervalNotDue when conflicts < next_conflict",
    );
}

#[test]
fn test_subsume_skip_reason_delays_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.cold.last_subsume_ticks = 100;
    solver.search_ticks = [
        100 + SUBSUME_TICK_THRESHOLD * solver.num_clauses() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.subsume_skip_reason(),
        Some(SubsumeSkipReason::ThresholdDelay),
        "subsume should defer when tick budget is below threshold",
    );
}

#[test]
fn test_subsume_skip_reason_allows_first_call_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = SUBSUME_INTERVAL;
    // last_subsume_ticks == 0 means first call — threshold is bypassed.
    solver.cold.last_subsume_ticks = 0;
    solver.search_ticks = [0, 0];

    assert_eq!(
        solver.subsume_skip_reason(),
        None,
        "first subsume call should not be delayed by tick threshold",
    );
}

#[test]
fn test_subsume_skip_reason_passes_above_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.cold.last_subsume_ticks = 100;
    solver.search_ticks = [
        100 + SUBSUME_TICK_THRESHOLD * solver.num_clauses() as u64,
        0,
    ];

    assert_eq!(
        solver.subsume_skip_reason(),
        None,
        "subsume should fire when tick budget meets threshold",
    );
}

// ======== BVE skip reason tests (#8148) ========

#[test]
fn test_bve_skip_reason_disabled_flag() {
    let solver: Solver = Solver::new(3);
    // BVE is disabled by default.
    assert_eq!(
        solver.bve_skip_reason(),
        Some(BveSkipReason::DisabledFlag),
        "bve should report DisabledFlag when disabled (default)",
    );
}

#[test]
fn test_bve_skip_reason_interval_not_due() {
    let mut solver: Solver = Solver::new(3);
    solver.set_bve_enabled(true);
    solver.inproc_ctrl.bve.next_conflict = 1000;
    solver.num_conflicts = 0;
    assert_eq!(
        solver.bve_skip_reason(),
        Some(BveSkipReason::IntervalNotDue),
        "bve should report IntervalNotDue when conflicts < next_conflict",
    );
}

#[test]
fn test_bve_skip_reason_fixpoint_guard() {
    let mut solver: Solver = Solver::new(3);
    solver.set_bve_enabled(true);
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.num_conflicts = 100;
    // Trigger fixpoint guard: last_bve_fixed == fixed_count,
    // last_bve_marked == bve_marked, no dirty candidates.
    solver.cold.last_bve_fixed = solver.fixed_count;
    solver.cold.last_bve_marked = solver.cold.bve_marked;

    assert_eq!(
        solver.bve_skip_reason(),
        Some(BveSkipReason::FixpointGuard),
        "bve should report FixpointGuard when no new units or irredundant changes",
    );
}

#[test]
fn test_bve_skip_reason_fires_when_fixpoint_broken() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.set_bve_enabled(true);
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.num_conflicts = 100;
    // Break the fixpoint: simulate a new level-0 unit by advancing fixed_count
    // beyond last_bve_fixed so the guard condition fails.
    solver.fixed_count = 1;
    solver.cold.last_bve_fixed = 0;
    solver.cold.last_bve_marked = solver.cold.bve_marked;
    // BVE_TICK_THRESHOLD=0 means threshold gate is always satisfied (no-op).

    assert_eq!(
        solver.bve_skip_reason(),
        None,
        "bve should fire when fixpoint is broken (new units discovered)",
    );
}

// ======== Transred skip reason tests (#8148) ========

#[test]
fn test_transred_skip_reason_disabled_flag() {
    let mut solver: Solver = Solver::new(3);
    solver.set_transred_enabled(false);
    assert_eq!(
        solver.transred_skip_reason(),
        Some(TransredSkipReason::DisabledFlag),
        "transred should report DisabledFlag when disabled",
    );
}

#[test]
fn test_transred_skip_reason_interval_not_due() {
    let mut solver: Solver = Solver::new(3);
    solver.set_transred_enabled(true);
    solver.num_conflicts = 0;
    assert_eq!(
        solver.transred_skip_reason(),
        Some(TransredSkipReason::IntervalNotDue),
        "transred should report IntervalNotDue when conflicts < next_conflict",
    );
}

#[test]
fn test_transred_skip_reason_delays_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = TRANSRED_INTERVAL;
    solver.cold.last_transred_ticks = 100;
    solver.search_ticks = [
        100 + TRANSRED_TICK_THRESHOLD * solver.num_clauses() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.transred_skip_reason(),
        Some(TransredSkipReason::ThresholdDelay),
        "transred should defer when tick budget is below threshold",
    );
}

#[test]
fn test_transred_skip_reason_allows_first_call_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = TRANSRED_INTERVAL;
    // last_transred_ticks == 0 means first call — threshold is bypassed.
    solver.cold.last_transred_ticks = 0;
    solver.search_ticks = [0, 0];

    assert_eq!(
        solver.transred_skip_reason(),
        None,
        "first transred call should not be delayed by tick threshold",
    );
}

#[test]
fn test_transred_skip_reason_passes_above_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = TRANSRED_INTERVAL;
    solver.cold.last_transred_ticks = 100;
    solver.search_ticks = [
        100 + TRANSRED_TICK_THRESHOLD * solver.num_clauses() as u64,
        0,
    ];

    assert_eq!(
        solver.transred_skip_reason(),
        None,
        "transred should fire when tick budget meets threshold",
    );
}

// ======== BCE skip reason tests (#8148) ========

#[test]
fn test_bce_skip_reason_disabled_flag() {
    let solver: Solver = Solver::new(3);
    // BCE is disabled by default.
    assert_eq!(
        solver.bce_skip_reason(),
        Some(BceSkipReason::DisabledFlag),
        "bce should report DisabledFlag when disabled (default)",
    );
}

#[test]
fn test_bce_skip_reason_interval_not_due() {
    let mut solver: Solver = Solver::new(3);
    solver.set_bce_enabled(true);
    solver.num_conflicts = 0;
    assert_eq!(
        solver.bce_skip_reason(),
        Some(BceSkipReason::IntervalNotDue),
        "bce should report IntervalNotDue when conflicts < next_conflict",
    );
}

#[test]
fn test_bce_skip_reason_delays_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.set_bce_enabled(true);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = BCE_INTERVAL;
    solver.cold.last_bce_ticks = 100;
    solver.search_ticks = [
        100 + BCE_TICK_THRESHOLD * solver.num_clauses() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.bce_skip_reason(),
        Some(BceSkipReason::ThresholdDelay),
        "bce should defer when tick budget is below threshold",
    );
}

#[test]
fn test_bce_skip_reason_allows_first_call_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.set_bce_enabled(true);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = BCE_INTERVAL;
    // last_bce_ticks == 0 means first call — threshold is bypassed.
    solver.cold.last_bce_ticks = 0;
    solver.search_ticks = [0, 0];

    assert_eq!(
        solver.bce_skip_reason(),
        None,
        "first bce call should not be delayed by tick threshold",
    );
}

#[test]
fn test_bce_skip_reason_passes_above_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.set_bce_enabled(true);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = BCE_INTERVAL;
    solver.cold.last_bce_ticks = 100;
    solver.search_ticks = [100 + BCE_TICK_THRESHOLD * solver.num_clauses() as u64, 0];

    assert_eq!(
        solver.bce_skip_reason(),
        None,
        "bce should fire when tick budget meets threshold",
    );
}
