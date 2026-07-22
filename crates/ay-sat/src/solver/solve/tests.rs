// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the solve module: model verification fail-closed behavior.

use crate::TlaTraceable;

use super::super::*;

/// Helper: build a solver with clause (x0 v x1) and no reconstruction.
/// The model parameter [false, false] leaves (x0 v x1) unsatisfied,
/// triggering the fail-closed path.
fn make_unrepairable_model_solver() -> (Solver, Literal, Literal) {
    let mut solver: Solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x0, x1]);
    (solver, x0, x1)
}

/// Helper: build a solver where reconstruction runs but the model
/// is still unrepairable. Clause_db has (x0 v x1) — consistent.
/// original_clauses gets an extra (x2) injected directly — simulating
/// a clause lost during preprocessing. x2 is non-eliminated with
/// val=false, so (x2) is unsatisfied and repair can't flip it.
fn make_unrepairable_reconstruction_solver() -> (Solver, Literal, Literal) {
    let mut solver: Solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    solver.add_clause(vec![x0, x1]);
    solver
        .inproc
        .reconstruction
        .push_witness_clause(vec![x0.negated()], vec![x0.negated()]);
    // Inject clause only in original_ledger (not clause_db).
    solver.cold.original_ledger.push_clause(&[x2]);
    (solver, x0, x1)
}

// verify_against_original checks the immutable original formula and
// the repair pass (#5522) tries to fix models by flipping eliminated
// vars. Tests use unrepairable scenarios (no eliminated vars to flip,
// or non-eliminated vars unsatisfied) to verify the fail-closed path.

#[test]
fn test_invalid_sat_model_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_model_solver();

    // Pass a model where both x0=false and x1=false, so (x0 v x1) is
    // unsatisfied. finalize_sat_model (#8078) builds ext_model from the
    // model parameter, so the bad model propagates to verification.
    let result = solver.declare_sat_from_model(vec![false, false]);
    assert_eq!(result, SatResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail string must explain which clause failed.
    let detail = solver
        .last_unknown_detail()
        .expect("last_unknown_detail should be populated on InvalidSatModel");
    assert!(
        detail.contains("original clause"),
        "detail should identify the unsatisfied original clause, got: {detail}",
    );
}

#[test]
fn test_invalid_assume_sat_model_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_model_solver();

    // Same as above but for assumption-based solving path.
    // Model [false, false] leaves (x0 v x1) unsatisfied.
    let result = solver.declare_assume_sat_from_model(vec![false, false]);
    assert_eq!(result, AssumeResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail string must explain which clause failed.
    let detail = solver
        .last_unknown_detail()
        .expect("last_unknown_detail should be populated on InvalidSatModel");
    assert!(
        detail.contains("original clause"),
        "detail should identify the unsatisfied original clause, got: {detail}",
    );
}

#[test]
fn test_reconstruction_panic_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_reconstruction_solver();

    // Clause_db has (x0 v x1) — consistent. But original_clauses has
    // an extra (x2) with x2 non-eliminated and val=false.
    // Reconstruction runs, repair pass tries, but can't fix (x2).
    // verify_against_original catches the violation → Unknown.
    let result = solver.declare_sat_from_model(vec![true, true, false]);
    assert_eq!(result, SatResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail should mention the failing original clause.
    assert!(
        solver.last_unknown_detail().is_some(),
        "last_unknown_detail should be populated on reconstruction failure",
    );
}

#[test]
fn test_assume_reconstruction_panic_fails_closed_to_unknown() {
    let (mut solver, _x0, _x1) = make_unrepairable_reconstruction_solver();

    // Same as above but for assumption-based solving path.
    let result = solver.declare_assume_sat_from_model(vec![true, true, false]);
    assert_eq!(result, AssumeResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
    );
    // #7917: detail should mention the failing original clause.
    assert!(
        solver.last_unknown_detail().is_some(),
        "last_unknown_detail should be populated on reconstruction failure",
    );
}

#[test]
fn test_solve_no_assumptions_refreshes_num_original_clauses_after_bve() {
    let mut solver = Solver::new(5);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_walk_enabled(false);

    // BVE eliminates x0 by resolving {x0, x1} with {~x0, x2}.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);

    let result = solver.solve_no_assumptions(|| false);
    assert!(
        matches!(result, SatResult::Sat(_)),
        "formula should remain SAT after preprocessing, got {result:?}"
    );
    assert!(
        solver.bve_stats().vars_eliminated > 0,
        "test setup must shrink the formula via BVE"
    );

    let active = solver.arena.active_clause_count();
    assert!(
        active < 5,
        "BVE should reduce the active irredundant clause count, got {active}"
    );
    assert_eq!(
        solver.num_original_clauses, active,
        "solve_no_assumptions must refresh num_original_clauses after preprocessing shrink"
    );
}

fn run_initialized_pure_cdcl(solver: &mut Solver) -> SatResult {
    if let Some(result) = solver.init_solve() {
        result
    } else {
        solver.cdcl_loop_pure(|| false)
    }
}

fn add_branching_unsat_formula(solver: &mut Solver) {
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(2)),
    ]);
}

#[test]
fn test_cdcl_loop_pure_main_no_tla_route_solves_sat_and_unsat() {
    let mut sat_solver = Solver::new(2);
    sat_solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    let sat_result = run_initialized_pure_cdcl(&mut sat_solver);
    match sat_result {
        SatResult::Sat(model) => assert!(model[0] || model[1]),
        other => panic!("pure main CDCL route should solve SAT formula, got {other:?}"),
    }

    let mut unsat_solver = Solver::new(3);
    add_branching_unsat_formula(&mut unsat_solver);
    let unsat_result = run_initialized_pure_cdcl(&mut unsat_solver);
    assert!(
        matches!(unsat_result, SatResult::Unsat(_)),
        "pure main CDCL route should solve branching UNSAT formula, got {unsat_result:?}"
    );
}

#[test]
fn test_cdcl_loop_pure_keeps_tla_aware_route_when_trace_enabled() {
    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("pure_cdcl_tla.jsonl");
    let trace_path_str = trace_path.to_str().expect("utf8 path");

    let mut solver = Solver::new(2);
    solver.enable_tla_trace(
        trace_path_str,
        Solver::tla_module(),
        Solver::tla_variables(),
    );
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    let result = run_initialized_pure_cdcl(&mut solver);
    assert!(
        matches!(result, SatResult::Sat(_)),
        "TLA-aware pure CDCL route should preserve SAT behavior, got {result:?}"
    );
    solver.finish_tla_trace();

    let trace = std::fs::read_to_string(&trace_path).expect("read TLA trace");
    assert!(
        trace.contains("Decide"),
        "TLA-aware pure route should still emit decision steps, trace: {trace}"
    );
    assert!(
        trace.contains("DeclareSat"),
        "TLA-aware pure route should still emit terminal SAT step, trace: {trace}"
    );
}

#[test]
fn test_maybe_run_restart_executes_shared_restart_path() {
    struct RestartProbe {
        restarts: u32,
    }

    impl super::theory_callback::TheoryCallback for RestartProbe {
        fn propagate(&mut self, _solver: &mut Solver) -> TheoryPropResult {
            TheoryPropResult::Continue
        }

        fn on_restart(&mut self) -> Vec<Variable> {
            self.restarts += 1;
            Vec::new()
        }
    }

    let mut solver = Solver::new(1);
    let mut callback = RestartProbe { restarts: 0 };

    solver.num_conflicts = solver.cold.restart_min_conflicts;
    solver.conflicts_since_restart = 1;
    solver.stable_mode = true;
    solver.cold.reluctant_countdown = 1;
    solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;

    assert!(
        solver.maybe_run_restart(&mut callback),
        "helper should execute a pending stable-mode restart",
    );
    assert_eq!(callback.restarts, 1, "restart callback should fire once");
    assert_eq!(
        solver.num_restarts(),
        1,
        "solver restart counter should advance"
    );
    assert_eq!(
        solver.conflicts_since_restart, 0,
        "restart should reset the conflict-since-restart counter",
    );
}

#[test]
fn test_maybe_run_restart_does_not_attribute_callback_blocked_restart() {
    struct BlockingRestartProbe {
        restarts: u32,
    }

    impl super::theory_callback::TheoryCallback for BlockingRestartProbe {
        fn propagate(&mut self, _solver: &mut Solver) -> TheoryPropResult {
            TheoryPropResult::Continue
        }

        fn on_restart(&mut self) -> Vec<Variable> {
            self.restarts += 1;
            Vec::new()
        }

        fn should_block_restart(&self, _num_assigned: u32, _total_vars: u32) -> bool {
            true
        }
    }

    let mut solver = Solver::new(1);
    let mut callback = BlockingRestartProbe { restarts: 0 };

    solver.num_conflicts = solver.cold.restart_min_conflicts;
    solver.conflicts_since_restart = 1;
    solver.stable_mode = true;
    solver.cold.reluctant_countdown = 1;
    solver.cold.reluctant_ticked_at = solver.num_conflicts - 1;

    assert!(
        !solver.maybe_run_restart(&mut callback),
        "callback should block the pending restart",
    );
    assert_eq!(
        callback.restarts, 0,
        "blocked restart must not notify callback"
    );
    assert_eq!(solver.num_restarts(), 0, "blocked restart must not execute");

    let stats = solver.restart_attribution_stats();
    assert_eq!(stats.stable_reluctant, 0);
    assert_eq!(stats.focused_mode + stats.stable_mode, 0);
}

// ---------------------------------------------------------------------------
// Retired JIT BCP integration tests were removed with the production BCP JIT
// path in #8517. This marker remains to make the absence explicit.
// ---------------------------------------------------------------------------
