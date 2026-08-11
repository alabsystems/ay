// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_sat::BranchSelectorMode;

#[test]
fn bv_sat_deadline_does_not_poison_external_interrupt_8961() {
    let external_interrupt = Arc::new(AtomicBool::new(false));
    let mut solver = SatSolver::new(1);

    let _guard = install_bv_sat_interrupt(
        &mut solver,
        Some(external_interrupt.clone()),
        Some(Instant::now()),
    );

    assert!(
        !external_interrupt.load(Ordering::Relaxed),
        "BV SAT deadline timer must not set the reusable API interrupt flag"
    );
}

#[test]
fn expired_bv_sat_deadline_keeps_timeout_provenance() {
    let external_interrupt = Arc::new(AtomicBool::new(true));
    let mut solver = SatSolver::new(1);
    let _guard =
        install_bv_sat_interrupt(&mut solver, Some(external_interrupt), Some(Instant::now()));

    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(ay_sat::SatUnknownReason::DeadlineExceeded)
    );
}

#[test]
fn reused_bv_sat_solver_rebinds_query_controls() {
    let old_interrupt = Arc::new(AtomicBool::new(true));
    let mut solver = SatSolver::new(1);
    {
        let _guard = install_bv_sat_interrupt(&mut solver, Some(old_interrupt), None);
        assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(ay_sat::SatUnknownReason::Interrupted)
        );
    }

    {
        let _guard = install_bv_sat_interrupt(&mut solver, None, None);
        assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
    }
}

#[test]
fn bv_unknown_fallback_prefers_expired_deadline_to_interrupt() {
    let mut executor = Executor::new();
    executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), Some(Instant::now()));

    executor.propagate_bv_unknown_reason(true);

    assert_eq!(executor.get_reason_unknown(), Some(UnknownReason::Timeout));
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
