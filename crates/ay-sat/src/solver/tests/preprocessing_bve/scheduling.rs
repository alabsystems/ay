// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Unit theory lemma regression tests (#6242)
// =========================================================================
//
// Before the fix, a unit theory lemma whose literal conflicts with a
// decision at level > 0 would falsely mark the empty clause (UNSAT).
// After the fix, it returns a conflict clause for backtracking.
// =========================================================================
// add_theory_propagation unit tests (P1:130)
// =========================================================================
//
// Tests for the lightweight theory propagation path that skips watch setup.
// Covers: empty clause, already-true (redundant), already-false (conflict
// fallback), normal enqueue, and propagated-literal position swap.
#[test]
fn test_freeze_melt_basic() {
    let mut solver = Solver::new(3);

    let v0 = Variable(0);
    let v1 = Variable(1);

    // Initially not frozen
    assert!(!solver.is_frozen(v0));
    assert!(!solver.is_frozen(v1));

    // Freeze v0
    solver.freeze(v0);
    assert!(solver.is_frozen(v0));
    assert!(!solver.is_frozen(v1));

    // Double freeze
    solver.freeze(v0);
    assert!(solver.is_frozen(v0));

    // Melt once - still frozen (ref count)
    solver.melt(v0);
    assert!(solver.is_frozen(v0));

    // Melt again - now unfrozen
    solver.melt(v0);
    assert!(!solver.is_frozen(v0));

    // Extra melts should be safe (saturating_sub)
    solver.melt(v0);
    assert!(!solver.is_frozen(v0));
}

#[test]
fn test_bve_schedule_disabled_by_default() {
    let mut solver = Solver::new(1);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    assert!(
        !solver.should_bve(),
        "BVE disabled by default; focused callers can opt in with set_bve_enabled(true)."
    );
}

#[test]
fn test_bve_schedule_can_be_enabled() {
    let mut solver = Solver::new(1);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    solver.set_bve_enabled(true);
    assert!(
        solver.should_bve(),
        "BVE should be enabled after set_bve_enabled(true)"
    );
}

#[test]
fn test_bve_occ_delta_validation_gate_default_off_and_toggle() {
    let mut solver = Solver::new(2);

    assert!(
        !solver.is_bve_occ_delta_validation_enabled(),
        "BVE occurrence-delta validation must be default-off"
    );
    solver.set_bve_occ_delta_validation_enabled(true);
    assert!(
        solver.is_bve_occ_delta_validation_enabled(),
        "setter should enable the cold BVE occurrence-delta gate"
    );
    solver.set_bve_occ_delta_validation_enabled(false);
    assert!(
        !solver.is_bve_occ_delta_validation_enabled(),
        "setter should disable the cold BVE occurrence-delta gate"
    );
}

#[test]
fn test_bve_occ_saved_state_reuse_gate_default_off_and_toggle() {
    let mut solver = Solver::new(2);

    assert!(
        !solver.is_bve_occ_saved_state_reuse_enabled(),
        "BVE occurrence saved-state reuse must be default-off"
    );
    solver.set_bve_occ_saved_state_reuse_enabled(true);
    assert!(
        solver.is_bve_occ_saved_state_reuse_enabled(),
        "setter should enable the cold BVE occurrence saved-state reuse candidate"
    );
    solver.set_bve_occ_saved_state_reuse_enabled(false);
    assert!(
        !solver.is_bve_occ_saved_state_reuse_enabled(),
        "setter should disable the cold BVE occurrence saved-state reuse candidate"
    );
}

#[test]
fn test_bve_schedule_skips_when_both_signals_unchanged() {
    let mut solver = Solver::new(1);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    solver.set_bve_enabled(true);
    solver.cold.last_bve_fixed = solver.fixed_count;
    assert!(
        !solver.should_bve(),
        "BVE should skip when no new level-0 units were discovered"
    );
}

/// Regression test for #4051: BVE must NOT re-fire from clause DB mutations
/// alone, or it forms a mutual re-triggering cycle with subsumption on random
/// 3-SAT instances.
#[test]
fn test_bve_skips_on_clause_db_changes_without_new_units() {
    let mut solver = Solver::new(1);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    solver.set_bve_enabled(true);
    // Snapshot fixed-count signal (simulates BVE just completed).
    solver.cold.last_bve_fixed = solver.fixed_count;

    // No new units — fixed_count unchanged.
    assert!(!solver.should_bve(), "BVE should not fire at fixpoint");

    // Simulate clause DB mutation by another inprocessing technique
    // (e.g., subsumption deleting a clause).
    solver.cold.clause_db_changes += 1;
    assert!(
        !solver.should_bve(),
        "BVE should ignore clause DB-only mutations and wait for new units (#4051)"
    );
}

/// Clause additions alone should not trigger BVE. The schedule now tracks only
/// newly fixed level-0 units.
#[test]
fn test_bve_skips_on_clause_addition_without_new_units() {
    let mut solver = Solver::new(2);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    solver.set_bve_enabled(true);
    solver.cold.last_bve_fixed = solver.fixed_count;

    assert!(!solver.should_bve(), "BVE should not fire at fixpoint");

    // Simulate an inprocessing pass adding an irredundant binary clause.
    let mut added = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    let _ = solver.add_clause_watched(&mut added);
    assert!(
        solver.cold.clause_db_changes > 0,
        "add_clause_watched must count clause DB mutations"
    );
    assert!(
        !solver.should_bve(),
        "BVE should remain gated on fixed-count/bve_marked changes, not clause additions"
    );
}

/// CaDiCaL `mark_elim` parity: BVE re-fires when `bve_marked` is incremented
/// by subsumption/vivification/decompose, even if no new level-0 units exist.
/// This ensures BVE re-evaluates candidates whose occurrence counts changed
/// due to irredundant clause modifications (CaDiCaL elim.cpp:79).
#[test]
fn test_bve_fires_on_bve_marked_increment() {
    let mut solver = Solver::new(1);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    solver.set_bve_enabled(true);
    // Snapshot both fixpoint guards (simulates BVE just completed).
    solver.cold.last_bve_fixed = solver.fixed_count;
    solver.cold.last_bve_marked = solver.cold.bve_marked;

    // No new units and no new marks — BVE should not fire.
    assert!(!solver.should_bve(), "BVE should not fire at dual fixpoint");

    // Simulate subsumption modifying an irredundant clause.
    solver.cold.bve_marked += 1;
    assert!(
        solver.should_bve(),
        "BVE should fire when bve_marked diverges from last_bve_marked"
    );
}

/// Regression: `clause_db_changes` alone must NOT trigger BVE (cycle guard #4051).
/// Only `bve_marked` (irredundant-only events) is the second trigger.
#[test]
fn test_bve_skips_on_clause_db_changes_but_fires_on_bve_marked() {
    let mut solver = Solver::new(1);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    solver.set_bve_enabled(true);
    solver.cold.last_bve_fixed = solver.fixed_count;
    solver.cold.last_bve_marked = solver.cold.bve_marked;

    solver.cold.clause_db_changes += 100;
    assert!(
        !solver.should_bve(),
        "clause_db_changes must not trigger BVE (#4051)"
    );

    solver.cold.bve_marked += 1;
    assert!(
        solver.should_bve(),
        "bve_marked must trigger BVE even when clause_db_changes is high"
    );
}

/// #5060 AC-1: BVE fires when `fixed_count` diverges from `last_bve_fixed`
/// alone, even when `bve_marked` is at fixpoint. This exercises the
/// `fixed_count` arm of the disjunctive guard in `should_bve()`.
#[test]
fn test_bve_fires_on_fixed_count_delta() {
    let mut solver = Solver::new(1);
    solver.num_conflicts = solver.inproc_ctrl.bve.next_conflict;
    solver.set_bve_enabled(true);
    // Snapshot both fixpoint guards (simulates BVE just completed).
    solver.cold.last_bve_fixed = solver.fixed_count;
    solver.cold.last_bve_marked = solver.cold.bve_marked;

    // Dual fixpoint — should not fire.
    assert!(!solver.should_bve(), "BVE should not fire at dual fixpoint");

    // Simulate a new level-0 unit discovered (e.g., by propagation).
    solver.fixed_count += 1;
    assert!(
        solver.should_bve(),
        "BVE should fire when fixed_count diverges from last_bve_fixed"
    );
}

#[test]
fn test_uniform_nonbinary_classifier_detects_large_random_3sat() {
    let mut solver = Solver::new(64);
    add_uniform_3sat_clauses(&mut solver, 64, 160);
    assert!(
        solver.is_uniform_nonbinary_irredundant_formula(),
        "uniform 3-SAT without binaries should match random-k-SAT classifier"
    );
}

#[test]
fn test_uniform_nonbinary_classifier_rejects_binary_clause() {
    let mut solver = Solver::new(64);
    add_uniform_3sat_clauses(&mut solver, 64, 160);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    assert!(
        !solver.is_uniform_nonbinary_irredundant_formula(),
        "binary clauses should disable random-k-SAT classifier"
    );
}

#[test]
fn test_preprocess_skips_gate_and_bve_on_uniform_nonbinary_formula() {
    let mut solver = Solver::new(64);
    add_uniform_3sat_clauses(&mut solver, 64, 160);
    solver.set_bve_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_sweep_enabled(false);

    let congr_rounds_before = solver.congruence_stats().rounds;
    assert!(
        !solver.preprocess(),
        "preprocess should not derive UNSAT here"
    );

    assert_eq!(
        solver.congruence_stats().rounds,
        congr_rounds_before,
        "congruence should be skipped on large random 3-SAT formulas"
    );
    // BVE fastelim (pass 1, bound=8) now runs on uniform non-binary formulas
    // to match CaDiCaL behavior (#6928). Gate-based BVE passes (bounds 1-2)
    // are still skipped since random formulas lack useful gate structure.
    assert!(
        solver.cold.bve_phases >= 1,
        "BVE fastelim should run on random 3-SAT (CaDiCaL eliminates ~19/500 vars)"
    );
}
