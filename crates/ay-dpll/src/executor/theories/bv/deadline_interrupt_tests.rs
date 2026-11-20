// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use super::*;
use ay_sat::BranchSelectorMode;

#[test]
fn bv_unknown_fallback_prefers_expired_deadline_to_interrupt() {
    let mut executor = Executor::new();
    executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), Some(Instant::now()));

    executor.propagate_bv_unknown_reason(true);

    assert_eq!(executor.get_reason_unknown(), Some(UnknownReason::Timeout));
}

#[test]
fn a_bitblast_cut_by_the_memory_ceiling_is_memout_after_the_reading_drops() {
    // `bitblast_all` stopped on the memory ceiling and left a partial CNF;
    // by the time it returns the reading is back under the ceiling. Reading
    // memory again let the partial CNF reach SAT, whose model then failed
    // validation as an `incomplete`-class unknown instead of `memout`.
    let script = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (bvult x y))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut executor = Executor::new();
    forced_blast_cut::force(Some(BlastCut::MemoryCeiling));
    let output = executor.execute_all(&commands).expect("fixture runs");
    forced_blast_cut::force(None);
    assert!(!ay_sys::process_memory_exceeded());
    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.get_reason_unknown(),
        Some(UnknownReason::MemoryLimit)
    );
    assert_eq!(executor.unknown_origin(), Some(UnknownOrigin::MemoryBudget));
    assert_eq!(
        executor.bv_encodings_stopped_before_search(),
        1,
        "a cut bit-blast is an encoding stopped before its SAT search"
    );

    // The same query with no cut is sat: only the cut stopped it.
    let mut executor = Executor::new();
    let output = executor.execute_all(&commands).expect("fixture runs");
    assert_eq!(output, vec!["sat"]);
    assert_eq!(executor.bv_encodings_stopped_before_search(), 0);
}

#[test]
fn a_bitblast_cut_by_the_interrupt_is_interrupted() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (bvult x #x10))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut executor = Executor::new();
    forced_blast_cut::force(Some(BlastCut::Interrupt));
    let output = executor.execute_all(&commands).expect("fixture runs");
    forced_blast_cut::force(None);
    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.get_reason_unknown(),
        Some(UnknownReason::Interrupted)
    );
    assert_eq!(executor.bv_encodings_stopped_before_search(), 1);
}

/// A stop that lands during the eager clause load (one unpolled call per
/// clause; ~10M on a deep BMC unrolling) is an encoding cut, not a search:
/// the solve answers `unknown` without entering its SAT search, and the
/// counters say so. Before the post-load poll the solve reported a search,
/// so a bounded model checker kept sweeping deeper.
#[test]
fn a_stop_during_the_clause_load_is_an_encoding_cut() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (bvult x #x10))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let flag = Arc::new(AtomicBool::new(false));
    let mut executor = Executor::new();
    executor.set_interrupt(flag.clone());
    stop_during_clause_load::arm(Some(flag));
    let output = executor.execute_all(&commands).expect("fixture runs");
    stop_during_clause_load::arm(None);
    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        executor.get_reason_unknown(),
        Some(UnknownReason::Interrupted)
    );
    assert_eq!(executor.bv_encodings_stopped_before_search(), 1);
    assert_eq!(executor.bv_sat_searches_entered(), 0);

    // Unstopped, the same query searches and answers.
    let mut executor = Executor::new();
    let output = executor.execute_all(&commands).expect("fixture runs");
    assert_eq!(output, vec!["sat"]);
    assert_eq!(executor.bv_encodings_stopped_before_search(), 0);
    assert_eq!(executor.bv_sat_searches_entered(), 1);
}

#[test]
fn ephemeral_bv_sat_solver_disables_restart_inprocessing_11936() {
    let mut solver = SatSolver::new(100_000);
    configure_ephemeral_bv_sat_solver(&mut solver, 100_000, 100_000, false);
    let profile = solver.inprocessing_feature_profile();

    assert!(!profile.preprocess);
    assert!(!profile.shrink);
    assert!(!profile.probe);
    assert!(!profile.vivify);
    assert!(!profile.subsume);
    assert!(!profile.condition);
    assert!(!profile.congruence);
    assert!(!profile.reorder);
    assert_eq!(solver.active_branch_heuristic(), BranchHeuristic::Vmtf);
    assert_eq!(
        solver.branch_selector_mode(),
        BranchSelectorMode::Fixed(BranchHeuristic::Vmtf)
    );
}

#[test]
fn large_abv_stable_restart_phase_requires_large_array_bitblast_8140() {
    assert!(should_extend_large_abv_stable_restart_phase(
        ABV_LARGE_STABLE_RESTART_MIN_VARS,
        ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
        true,
    ));
    assert!(!should_extend_large_abv_stable_restart_phase(
        ABV_LARGE_STABLE_RESTART_MIN_VARS - 1,
        ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
        true,
    ));
    assert!(!should_extend_large_abv_stable_restart_phase(
        ABV_LARGE_STABLE_RESTART_MIN_VARS,
        ABV_LARGE_STABLE_RESTART_MIN_CLAUSES - 1,
        true,
    ));
    assert!(!should_extend_large_abv_stable_restart_phase(
        ABV_LARGE_STABLE_RESTART_MIN_VARS,
        ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
        false,
    ));
}

#[test]
fn large_abv_ephemeral_solver_keeps_stable_focused_branch_coupling_8140() {
    let mut solver = SatSolver::new(ABV_LARGE_STABLE_RESTART_MIN_VARS);

    configure_ephemeral_bv_sat_solver(
        &mut solver,
        ABV_LARGE_STABLE_RESTART_MIN_VARS,
        ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
        true,
    );

    assert_eq!(
        solver.branch_selector_mode(),
        BranchSelectorMode::LegacyCoupled
    );
}
