// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Mutex;

static MEMORY_LIMIT_TEST_LOCK: Mutex<()> = Mutex::new(());

struct GlobalMemoryGuard;

impl GlobalMemoryGuard {
    fn force_exceeded() -> Self {
        // DEFAULT_TERM_MEMORY_LIMIT is usize::MAX (unlimited), so the
        // term-byte comparison alone cannot trigger global_memory_exceeded().
        // Force the process-level RSS limit to 1 byte so that
        // process_memory_exceeded() fires.
        ay_core::term::TermStore::force_process_memory_exceeded_for_testing();
        Self
    }
}

impl Drop for GlobalMemoryGuard {
    fn drop(&mut self) {
        ay_core::term::TermStore::reset_global_term_bytes();
        ay_core::term::TermStore::reset_process_memory_limit_for_testing();
    }
}

/// T3 (#4172): Subsumption must route through `delete_clause_checked`
/// (unified safety contract). Verify that clause_db_changes is incremented
/// (raw `clause_db.delete()` would not update the counter).
///
/// Calls `subsume()` directly — preprocessing quick mode (d060cc2) defers
/// subsumption to inprocessing, matching CaDiCaL internal.cpp:742-792.
#[test]
fn test_preprocess_subsumption_uses_unified_delete_contract() {
    // (x0 v x1) subsumes (x0 v x1 v x2): the ternary clause should be
    // deleted via delete_clause_checked, incrementing clause_db_changes.
    let mut solver: Solver = Solver::new(5);
    solver.preprocessing_quick_mode = false; // test needs subsumption during preprocess
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]); // binary subsumer
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]); // ternary subsumed
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]); // unrelated padding
    assert!(solver.process_initial_clauses().is_none());

    // Disable all passes then re-enable only subsumption.
    solver.disable_all_inprocessing();
    solver.inproc_ctrl.subsume.enabled = true;

    let changes_before = solver.cold.clause_db_changes;
    solver.subsume();

    assert!(
        solver.cold.clause_db_changes > changes_before,
        "subsume() must go through delete_clause_checked \
         (clause_db_changes should increase)"
    );
}

#[test]
fn test_reset_search_state_resets_all_scheduling_counters() {
    let mut solver: Solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
    ]);

    // Simulate a previous solve that advanced ALL scheduling counters.
    solver.num_conflicts = 50_000;
    solver.inproc_ctrl.condition.next_conflict = 60_000;
    solver.inproc_ctrl.decompose.next_conflict = 70_000;
    solver.inproc_ctrl.factor.next_conflict = 80_000;
    solver.inproc_ctrl.congruence.next_conflict = 90_000;
    solver.cold.next_rephase = 100_000;
    solver.tiers.next_recompute_tier = 110_000;
    solver.inproc_ctrl.vivify.next_conflict = 120_000;
    solver.inproc_ctrl.vivify_irred.next_conflict = 130_000;
    solver.inproc_ctrl.subsume.next_conflict = 140_000;
    solver.inproc_ctrl.probe.next_conflict = 150_000;
    solver.inproc_ctrl.bve.next_conflict = 160_000;
    solver.inproc_ctrl.bce.next_conflict = 170_000;
    solver.inproc_ctrl.transred.next_conflict = 180_000;
    solver.inproc_ctrl.htr.next_conflict = 190_000;
    solver.inproc_ctrl.sweep.next_conflict = 200_000;
    solver.cold.next_reduce_db = 210_000;
    solver.cold.num_reductions = 15;
    solver.cold.last_inprobe_reduction = 12;
    solver.cold.eager_subsumed = 7;
    solver.cold.vivify_irred_delay_multiplier = 4;
    solver.fixed_count = 8;
    // Tick watermarks from a previous solve (#8159):
    solver.cold.last_factor_ticks = 999_999;
    solver.cold.last_sweep_ticks = 888_888;
    solver.cold.last_backbone_ticks = 777_777;
    solver.cold.last_vivify_ticks = 666_666;
    solver.cold.last_vivify_irred_ticks = 555_555;
    solver.inproc.prober.set_last_search_ticks(444_444);
    solver.inproc.htr.set_last_search_ticks(333_333);
    solver.inproc.transred_engine.set_last_propagations(222_222);
    solver.cold.last_sbva_ticks = 111_111;
    // Effort demotion persistence (#8159 D4):
    solver.cold.bve_effort_permille = 10;
    solver.cold.subsume_effort_permille = 60;

    solver.reset_search_state();

    // num_conflicts is reset to 0, so all counters must be relative to 0.
    // Since num_conflicts was 50_000, lifetime_conflicts is now 50_000 > 0,
    // making this an incremental re-solve where base_or_zero returns 0 (#8208).
    assert_eq!(solver.num_conflicts, 0);
    assert_eq!(
        solver.inproc_ctrl.condition.next_conflict, 0,
        "incremental re-solve: base_or_zero returns 0"
    );
    assert_eq!(
        solver.inproc_ctrl.decompose.next_conflict, 0,
        "next_decompose should fire on first check"
    );
    assert_eq!(
        solver.inproc_ctrl.factor.next_conflict, 0,
        "incremental re-solve: base_or_zero returns 0"
    );
    assert_eq!(
        solver.inproc_ctrl.congruence.next_conflict, 0,
        "next_congruence should fire on first check"
    );
    assert_eq!(solver.cold.next_rephase, REPHASE_INITIAL);
    assert_eq!(solver.tiers.next_recompute_tier, TIER_RECOMPUTE_INIT);
    // Additional reset fields that previously lacked direct assertions (#3630):
    // incremental re-solve: all intervals are 0 (#8208).
    assert_eq!(solver.inproc_ctrl.vivify.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.vivify_irred.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.subsume.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.probe.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.bve.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.bce.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.transred.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.htr.next_conflict, 0);
    assert_eq!(solver.inproc_ctrl.sweep.next_conflict, 0);
    assert_eq!(solver.cold.next_reduce_db, FIRST_REDUCE_DB);
    assert_eq!(
        solver.cold.num_reductions, 0,
        "num_reductions must reset (#5130)"
    );
    assert_eq!(
        solver.cold.last_inprobe_reduction, 0,
        "last_inprobe_reduction must reset (#5130)"
    );
    assert_eq!(
        solver.cold.eager_subsumed, 0,
        "eager_subsumed must reset (#5136)"
    );
    assert_eq!(solver.cold.vivify_irred_delay_multiplier, 1);
    assert_eq!(solver.fixed_count, 0);
    // Tick watermark resets (#8159): all must be zeroed so saturating_sub
    // effort computations produce non-zero budgets on the second solve.
    assert_eq!(
        solver.cold.last_factor_ticks, 0,
        "last_factor_ticks must reset (#8159)"
    );
    assert_eq!(
        solver.cold.last_sweep_ticks, 0,
        "last_sweep_ticks must reset (#8159)"
    );
    assert_eq!(
        solver.cold.last_backbone_ticks, 0,
        "last_backbone_ticks must reset (#8159)"
    );
    assert_eq!(
        solver.cold.last_vivify_ticks, 0,
        "last_vivify_ticks must reset"
    );
    assert_eq!(
        solver.cold.last_vivify_irred_ticks, 0,
        "last_vivify_irred_ticks must reset"
    );
    assert_eq!(
        solver.inproc.prober.last_search_ticks(),
        0,
        "prober.last_search_ticks must reset (#8159)"
    );
    assert!(
        solver.inproc.htr.last_search_ticks().is_none(),
        "htr.last_search_ticks must reset to None (#8159)"
    );
    assert_eq!(
        solver.inproc.transred_engine.last_propagations(),
        0,
        "transred.last_propagations must reset (#8159)"
    );
    assert_eq!(
        solver.cold.last_sbva_ticks, 0,
        "last_sbva_ticks must reset (#8159)"
    );
    // Effort demotion persistence (#8159 D4): effort permille must reset
    // to defaults so the runtime demotion selector can re-evaluate.
    assert_eq!(
        solver.cold.bve_effort_permille, BVE_EFFORT_PER_MILLE,
        "bve_effort_permille must reset to default (#8159 D4)"
    );
    assert_eq!(
        solver.cold.subsume_effort_permille, SUBSUME_EFFORT_PER_MILLE,
        "subsume_effort_permille must reset to default (#8159 D4)"
    );
}

#[test]
fn test_on_conflict_random_decision_polls_process_memory_limit() {
    let _lock = MEMORY_LIMIT_TEST_LOCK
        .lock()
        .expect("memory-limit tests must serialize global process limit state");
    let _guard = GlobalMemoryGuard::force_exceeded();

    let mut solver = Solver::new(2);
    solver.num_conflicts = PROCESS_MEMORY_CHECK_INTERVAL - 1;
    solver.on_conflict_random_decision();
    assert!(
        !solver.is_interrupted(),
        "memory poll must not fire before the configured conflict interval"
    );

    solver.num_conflicts = PROCESS_MEMORY_CHECK_INTERVAL;
    solver.on_conflict_random_decision();
    assert!(
        !solver.is_interrupted(),
        "#sparse-gap Cluster A: the FIRST positive poll only ARMS the pending \
         flag — a transient allocator spike must not poison the run"
    );

    // Sustained pressure: a confirming poll AFTER the 500ms window latches.
    std::thread::sleep(std::time::Duration::from_millis(550));
    solver.num_conflicts += PROCESS_MEMORY_CHECK_INTERVAL;
    solver.on_conflict_random_decision();
    assert!(
        solver.is_interrupted(),
        "sustained mid-solve process memory overflow must trip the internal \
         interrupt gate after the confirmation window"
    );
}

#[test]
fn test_reset_search_state_clears_process_memory_interrupt() {
    let _lock = MEMORY_LIMIT_TEST_LOCK
        .lock()
        .expect("memory-limit tests must serialize global process limit state");
    let _guard = GlobalMemoryGuard::force_exceeded();

    let mut solver = Solver::new(2);
    // Two-poll confirmation (#sparse-gap Cluster A): arm, wait out the
    // confirmation window, then confirm to latch the interrupt.
    solver.num_conflicts = PROCESS_MEMORY_CHECK_INTERVAL;
    solver.on_conflict_random_decision();
    std::thread::sleep(std::time::Duration::from_millis(550));
    solver.num_conflicts += PROCESS_MEMORY_CHECK_INTERVAL;
    solver.on_conflict_random_decision();
    assert!(
        solver.is_interrupted(),
        "test setup failed: process memory limit should have tripped the interrupt gate"
    );

    solver.reset_search_state();
    assert!(
        !solver.is_interrupted(),
        "reset_search_state must clear solver-owned process-memory interrupts"
    );
}

/// Regression test for #3644 Wave 3: targeted reactivation in reset_search_state().
///
/// A decompose-substituted variable (with no witness entry) must NOT be
/// reactivated by reset_search_state(), while a BVE-eliminated variable
/// (with witness entries) must be reactivated.
#[test]
fn test_reset_search_state_targeted_reactivation_preserves_substituted() {
    use crate::solver::lifecycle::VarState;

    // 4 variables: x0, x1, x2, x3
    let mut solver: Solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
    ]);

    // x1 is BVE-eliminated with witness entries in the reconstruction stack.
    solver.var_lifecycle.mark_eliminated(1);
    solver.inproc.reconstruction.push_bve(
        Variable(1),
        vec![vec![
            Literal::positive(Variable(1)),
            Literal::positive(Variable(0)),
        ]],
        vec![vec![
            Literal::negative(Variable(1)),
            Literal::negative(Variable(2)),
        ]],
    );

    // x3 is decompose-substituted WITHOUT any witness entry.
    solver.var_lifecycle.mark_substituted(3);

    // Precondition: both variables are removed.
    assert!(solver.var_lifecycle.is_removed(1));
    assert!(solver.var_lifecycle.is_removed(3));

    solver.reset_search_state();

    // x1 should be reactivated (its witness entries were drained and clauses restored).
    assert_eq!(
        solver.var_lifecycle.as_slice()[1],
        VarState::Active,
        "BVE-eliminated variable with witness should be reactivated"
    );

    // x3 should stay Substituted (no witness entry → not in drain_result.reactivate_vars).
    assert_eq!(
        solver.var_lifecycle.as_slice()[3],
        VarState::Substituted,
        "Decompose-substituted variable without witness must not be reactivated"
    );
}

#[test]
fn test_reset_search_state_reactivation_invalidates_bve_occ_saved_state() {
    let mut solver: Solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    solver.set_bve_occ_delta_validation_enabled(true);
    solver.inproc.bve.rebuild_with_vals_at_epoch(
        &solver.arena,
        &solver.vals,
        solver.cold.clause_db_changes,
    );
    assert!(solver.inproc.bve.is_occ_populated());

    solver.var_lifecycle.mark_eliminated(1);
    solver.inproc.reconstruction.push_bve(
        Variable(1),
        vec![vec![
            Literal::positive(Variable(1)),
            Literal::positive(Variable(0)),
        ]],
        vec![vec![
            Literal::negative(Variable(1)),
            Literal::positive(Variable(2)),
        ]],
    );

    solver.reset_search_state();

    assert!(
        !solver.inproc.bve.is_occ_populated(),
        "reactivating BVE witness variables must invalidate saved occurrence lists"
    );
}

#[test]
fn test_reset_search_state_ledger_rebuild_invalidates_bve_occ_saved_state() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    solver.set_bve_occ_delta_validation_enabled(true);
    solver.inproc.bve.rebuild_with_vals_at_epoch(
        &solver.arena,
        &solver.vals,
        solver.cold.clause_db_changes,
    );
    assert!(solver.inproc.bve.is_occ_populated());

    solver.cold.inprocessing_modified_clause_db = true;
    solver.reset_search_state();

    assert!(
        !solver.inproc.bve.is_occ_populated(),
        "destructive ledger replay must invalidate saved occurrence lists"
    );
}

/// Test VarState::Fixed lifecycle transitions (#3906).
///
/// Verifies:
/// - mark_fixed() transitions Active -> Fixed
/// - Fixed variables are not considered removed (is_removed() == false)
/// - Fixed variables are inactive (is_inactive() == true)
/// - Fixed variables cannot be reactivated (can_reactivate() == false)
/// - reset_fixed() reverts Fixed -> Active
#[test]
fn test_lifecycle_fixed_state_transitions() {
    use crate::solver::lifecycle::{VarLifecycle, VarState};

    let mut lc = VarLifecycle::new(4);

    // All start Active.
    assert_eq!(lc.as_slice()[0], VarState::Active);
    assert!(!lc.is_removed(0));
    assert!(!lc.is_fixed(0));

    // Mark var 0 as Fixed.
    lc.mark_fixed(0);
    assert_eq!(lc.as_slice()[0], VarState::Fixed);
    assert!(lc.is_fixed(0));
    // Fixed is NOT considered "removed" (still in clauses with valid watches).
    assert!(!lc.is_removed(0));
    // Fixed IS inactive (not Active).
    assert!(lc.as_slice()[0].is_inactive());
    // Fixed cannot be reactivated.
    assert!(!lc.can_reactivate(0));

    // Mark var 1 as Eliminated — verify it IS removed.
    lc.mark_eliminated(1);
    assert!(lc.is_removed(1));
    assert!(lc.as_slice()[1].is_inactive());
    assert!(lc.can_reactivate(1));

    // count_removed: only Eliminated/Substituted, not Fixed.
    assert_eq!(lc.count_removed(), 1);

    // reset_fixed: reverts Fixed -> Active, leaves Eliminated alone.
    lc.reset_fixed();
    assert_eq!(lc.as_slice()[0], VarState::Active);
    assert!(!lc.is_fixed(0));
    assert_eq!(lc.as_slice()[1], VarState::Eliminated);
}

/// Test that process_initial_clauses marks unit variables as Fixed (#3906).
///
/// Original unit clauses should have their variables marked Fixed in the
/// lifecycle, matching CaDiCaL clause.cpp:363.
#[test]
fn test_process_initial_clauses_marks_fixed() {
    use crate::solver::lifecycle::VarState;

    let mut solver: Solver = Solver::new(3);

    // Add a unit clause: x0 = true
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    // Add a non-unit clause
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);

    // Before processing, all are Active.
    assert_eq!(solver.var_lifecycle.as_slice()[0], VarState::Active);
    assert_eq!(solver.fixed_count, 0);

    assert!(solver.process_initial_clauses().is_none());

    // After processing, x0 should be Fixed.
    assert_eq!(solver.var_lifecycle.as_slice()[0], VarState::Fixed);
    assert_eq!(solver.fixed_count, 1);

    // x1 and x2 should still be Active (non-unit clause).
    assert_eq!(solver.var_lifecycle.as_slice()[1], VarState::Active);
    assert_eq!(solver.var_lifecycle.as_slice()[2], VarState::Active);
}

// ========================================================================
// Variable/solver growth tests (extracted from tests.rs, Part of #5142)
// ========================================================================

#[test]
fn test_new_var_updates_model_len() {
    let mut solver = Solver::new(1);
    let v0 = Variable(0);
    let v1 = solver.new_var();
    assert_eq!(v1, Variable(1));

    // Force both variables true so the model is fully assigned.
    solver.add_clause(vec![Literal::positive(v0)]);
    solver.add_clause(vec![Literal::positive(v1)]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert_eq!(
                model.len(),
                2,
                "model should include dynamically added variables"
            );
            assert!(model[0]);
            assert!(model[1]);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_ensure_num_vars_updates_model_len() {
    let mut solver = Solver::new(1);
    solver.ensure_num_vars(3);

    // Constrain just the first variable; the others are don't-cares but should
    // still appear in the returned model.
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert_eq!(model.len(), 3, "model should include ensured variables");
            assert!(model[0]);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_new_var_and_ensure_num_vars_keep_unit_proof_id_in_sync() {
    // After #8069 (Phase 2a), unit_proof_id is always allocated
    // unconditionally for deferred backward proof reconstruction.
    let solver: Solver = Solver::new(1);
    assert_eq!(
        solver.unit_proof_id.len(),
        solver.num_vars,
        "unit_proof_id must always be allocated (#8069)"
    );

    let mut solver = Solver::new(1);
    assert_eq!(solver.unit_proof_id.len(), solver.num_vars);

    for _ in 0..4 {
        solver.new_var();
    }
    assert_eq!(solver.unit_proof_id.len(), solver.num_vars);

    solver.ensure_num_vars(10);
    assert_eq!(solver.unit_proof_id.len(), solver.num_vars);

    let newest = solver.num_vars - 1;
    solver.unit_proof_id[newest] = 7;
    assert_eq!(solver.unit_proof_id[newest], 7);
}

/// Regression test for #5509: ensure_num_vars must resize minimize_flags
/// (which contains packed LRAT_A/LRAT_B bits).
///
/// Without the fix, solve_with_assumptions after ensure_num_vars panics with
/// index-out-of-bounds in append_lrat_unit_chain because minimize_flags was
/// not resized to match the new num_vars.
#[test]
fn test_ensure_num_vars_lrat_work_arrays_in_sync() {
    let mut solver = Solver::new(2);

    // Add some clauses with the initial variables.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // Grow the solver via ensure_num_vars.
    solver.ensure_num_vars(10);

    // Verify minimize_flags length matches num_vars (LRAT bits are packed here).
    assert_eq!(solver.min.minimize_flags.len(), solver.num_vars);

    // Add clauses using the new variables to force conflict analysis to touch them.
    let v8 = Variable(8);
    let v9 = Variable(9);
    solver.add_clause(vec![Literal::positive(v8), Literal::positive(v9)]);
    solver.add_clause(vec![Literal::negative(v8), Literal::negative(v9)]);

    // solve_with_assumptions exercises the conflict analysis path that crashed.
    let assumptions = vec![Literal::positive(v8), Literal::positive(v9)];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    // The specific result doesn't matter — what matters is no panic.
    match result {
        AssumeResult::Sat(_) | AssumeResult::Unsat(..) | AssumeResult::Unknown => {}
    }
}

/// Regression test: ensure_num_vars must resize e2i/i2e.
///
/// Without the fix, Solver::new(0) followed by ensure_num_vars(N) left
/// e2i/i2e empty (len=0). Preprocessing (decompose) then panicked with
/// "index out of bounds: the len is 0 but the index is N" in externalize().
/// This affected CHC incremental SAT contexts which create Solver::new(0)
/// and grow variables via ensure_num_vars.
#[test]
fn test_ensure_num_vars_from_zero_e2i_i2e_sync() {
    let mut solver = Solver::new(0);
    assert_eq!(solver.cold.e2i.len(), 0);
    assert_eq!(solver.cold.i2e.len(), 0);

    solver.ensure_num_vars(28);
    assert_eq!(
        solver.cold.e2i.len(),
        28,
        "e2i must grow with ensure_num_vars"
    );
    assert_eq!(
        solver.cold.i2e.len(),
        28,
        "i2e must grow with ensure_num_vars"
    );

    // Identity mapping: for a solver with no compaction, e2i[v] == v and i2e[v] == v.
    for v in 0..28u32 {
        assert_eq!(
            solver.cold.e2i[v as usize], v,
            "e2i[{v}] should be identity"
        );
        assert_eq!(
            solver.cold.i2e[v as usize], v,
            "i2e[{v}] should be identity"
        );
    }
}

/// Regression test: solve_with_assumptions after ensure_num_vars from 0
/// must not panic in preprocessing (decompose/externalize).
///
/// Exercises the full code path: Solver::new(0) → ensure_num_vars → add clauses →
/// solve_with_assumptions (triggers preprocessing with decompose). Before the e2i/i2e
/// fix, this panicked in externalize() inside decompose.
#[test]
fn test_ensure_num_vars_from_zero_solve_with_assumptions() {
    let mut solver = Solver::new(0);
    solver.ensure_num_vars(10);

    // Create binary implications to exercise decompose's SCC analysis.
    // x0 → x1, x1 → x0 (equivalence) and x2 → x3, x3 → x2 (another SCC)
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(0)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(2)),
    ]);

    // Force one polarity so it's satisfiable.
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let assumptions = vec![Literal::positive(Variable(5))];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    // What matters is no panic — the specific result depends on solver decisions.
    match result {
        AssumeResult::Sat(model) => {
            assert!(
                model.len() >= 10,
                "model should cover all ensured variables"
            );
        }
        AssumeResult::Unsat(..) | AssumeResult::Unknown => {}
    }
}

/// Regression test for #5513: ensure_num_vars must resize level-indexed arrays
/// (glue_stamp, minimize_level_seen) to num_vars + 1,
/// matching the constructor allocation. Without the fix, conflict analysis at
/// high decision levels could read past the end of these arrays.
#[test]
fn test_ensure_num_vars_level_indexed_arrays_plus_one() {
    let mut solver = Solver::new(2);
    // Constructor allocates glue_stamp etc. at num_vars + 1 = 3.
    assert_eq!(solver.glue_stamp.len(), 3);
    assert_eq!(solver.min.minimize_level_seen.len(), 3);

    solver.ensure_num_vars(10);

    // Level-indexed arrays must be num_vars + 1 = 11, not num_vars = 10.
    assert_eq!(
        solver.glue_stamp.len(),
        11,
        "glue_stamp must be num_vars + 1 (level-indexed)"
    );
    assert_eq!(
        solver.min.minimize_level_seen.len(),
        11,
        "minimize_level_seen must be num_vars + 1 (level-indexed)"
    );

    // shrink_stamp is variable-indexed, so it should be exactly num_vars.
    assert_eq!(
        solver.shrink_stamp.len(),
        10,
        "shrink_stamp must be num_vars (variable-indexed)"
    );
}

/// Verify that marking an empty clause WITHOUT a solution witness does not panic.
/// Normal UNSAT derivation (no witness loaded) should proceed without assertion failure.
#[test]
fn test_empty_clause_without_witness_does_not_panic() {
    let mut solver: Solver = Solver::new(2);
    // No set_solution call — solution_witness is None.

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.mark_empty_clause();
    }));

    assert!(
        panic.is_ok(),
        "empty clause without loaded witness should not panic"
    );
    assert!(solver.has_empty_clause, "empty clause flag should be set");
}

#[test]
fn test_add_clause_normalizes_duplicate_literals() {
    let mut solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    assert!(solver.add_clause(vec![x0, x0, x1]));
    assert_eq!(
        solver.arena.num_clauses(),
        1,
        "exactly one clause should be added"
    );

    let clause = solver.arena.literals(0);
    assert_eq!(clause.len(), 2, "duplicate literal must be removed");
    assert!(clause.contains(&x0));
    assert!(clause.contains(&x1));

    let result = solver.solve_with_assumptions(&[x0.negated(), x1.negated()]);
    assert!(
        result.into_inner().is_unsat(),
        "normalized clause (x0 ∨ x1) must conflict under assumptions ¬x0, ¬x1"
    );
}

#[test]
fn test_add_clause_discards_tautology_after_dedup() {
    let mut solver = Solver::new(1);
    let x0 = Literal::positive(Variable(0));

    assert!(
        solver.add_clause(vec![x0, x0, x0.negated()]),
        "tautology should be treated as satisfied input"
    );
    assert_eq!(
        solver.arena.num_clauses(),
        0,
        "tautological clause must not be added to clause DB"
    );
}

// ===================== Disabled-feature guard tests =====================
// These tests verify that features disabled for soundness reasons stay off
// by default. If someone flips a default, these tests break immediately.

#[test]
fn test_hbr_enabled_by_default() {
    let solver: Solver = Solver::new(4);
    assert!(
        solver.hbr_enabled,
        "HBR should be enabled: probe_parent array fix makes it sound (#3419)"
    );
}

#[test]
fn test_hbr_enabled_by_default_with_proof() {
    let solver: Solver = Solver::with_proof(4, Vec::new());
    assert!(
        solver.hbr_enabled,
        "HBR should be enabled in proof mode: probe_parent array fix makes it sound (#3419)"
    );
}

#[test]
fn test_lrat_probe_parent_chain_learning_default_off() {
    let mut solver: Solver = Solver::with_proof(4, Vec::new());
    assert!(
        !solver.is_lrat_probe_parent_chain_enabled(),
        "LRAT probe parent-chain learning must stay default-off until checker evidence exists"
    );

    solver.set_lrat_probe_parent_chain_enabled(true);
    assert!(
        solver.is_lrat_probe_parent_chain_enabled(),
        "internal gate should be opt-in for focused proof experiments"
    );
}

#[test]
fn test_decompose_disabled_by_default_but_opt_in() {
    let mut solver: Solver = Solver::new(4);
    assert!(
        !solver.is_decompose_enabled(),
        "decompose must be opt-in until model reconstruction is safe by default"
    );
    solver.set_decompose_enabled(true);
    assert!(
        solver.is_decompose_enabled(),
        "decompose should remain available for focused experiments"
    );
}

#[test]
fn test_factor_enabled_by_default() {
    let solver: Solver = Solver::new(4);
    assert!(
        solver.is_factor_enabled(),
        "Factorization enabled: reconstruction removed per CaDiCaL (no extension stack entries for factor)"
    );
}

#[test]
fn test_condition_disabled_by_default() {
    let solver: Solver = Solver::new(4);
    assert!(
        !solver.is_condition_enabled(),
        "Conditioning disabled by default: CaDiCaL condition=0 (#8080)"
    );
}
