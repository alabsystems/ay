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

    // The same query with no cut is sat: only the cut stopped it.
    let mut executor = Executor::new();
    let output = executor.execute_all(&commands).expect("fixture runs");
    assert_eq!(output, vec!["sat"]);
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
