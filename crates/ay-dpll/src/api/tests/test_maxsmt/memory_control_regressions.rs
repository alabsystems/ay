// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `test_maxsmt.rs` to preserve the existing test fully
// qualified names and inherited API imports.

// A control-restoration sentinel, not a memory-limit assertion. `:max-memory`
// is enforced against the live process footprint, so a reachable 2 GiB value
// lets parallel lib-test allocation select `MemoryLimit` before these tests'
// intended error/interrupt boundaries. Match the established 256 GiB sentinel
// in `test_solving_controls`: it remains an exact parsed value for restoration
// assertions while staying unreachable by the test harness.
const PARSED_MEMORY_SENTINEL_MIB: usize = 262_144;
const PARSED_MEMORY_SENTINEL_BYTES: usize = PARSED_MEMORY_SENTINEL_MIB * 1024 * 1024;

/// An executor error can occur after internal MaxSMT probes have populated
/// state. It must retire all probe/prior witness state before reaching the
/// caller.
#[test]
fn test_maxsmt_executor_error_revokes_model() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    solver.assert_soft(a, 1, None).unwrap();
    let seeded = solver.check_sat_max().unwrap();
    assert!(
        seeded.is_optimal(),
        "result={seeded}, reason={:?}, error={:?}",
        solver.unknown_reason(),
        solver.executor_error()
    );
    assert!(solver.model_for_consumer().is_some());

    solver
        .parse_smtlib2(&format!(
            "(set-option :timeout 60000) (set-option :max-memory {PARSED_MEMORY_SENTINEL_MIB})"
        ))
        .unwrap();
    solver.set_option(":ay-maxsmt-engine", "invalid");
    let assertions_before = solver.assertions();
    let scopes_before = solver.num_scopes();
    let error = solver
        .check_sat_max()
        .expect_err("unknown MaxSMT engine must be rejected");
    assert!(error.to_string().contains("ay-maxsmt-engine"));
    assert_eq!(solver.assertions(), assertions_before);
    assert_eq!(solver.num_scopes(), scopes_before);
    assert_eq!(solver.num_parsed_soft_constraints(), 0);
    assert!(solver.model().is_none());
    assert!(solver.model_for_consumer().is_none());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::InternalError)
    );
    assert_eq!(solver.executor.timeout(), Some(Duration::from_mins(1)));
    assert_eq!(
        solver.executor.memory_limit(),
        Some(PARSED_MEMORY_SENTINEL_BYTES),
        "error cleanup must restore the parsed executor ceiling"
    );
    assert_eq!(solver.executor.current_solve_deadline(), None);
}

/// A native MaxSMT result is richer than the internal text verdict: objective
/// accounting and the restored soft-owner transaction are authenticated after
/// the executor returns. An interrupt in that window must revoke both an
/// apparent optimum and an apparent hard-UNSAT result before either reaches the
/// caller.
#[test]
fn test_maxsmt_late_interrupt_revokes_all_definite_native_results() {
    let mut optimal = Solver::try_new(Logic::QfUf).unwrap();
    optimal
        .parse_smtlib2(&format!(
            "(set-option :timeout 60000) (set-option :max-memory {PARSED_MEMORY_SENTINEL_MIB})"
        ))
        .unwrap();
    let a = optimal.declare_const("a", Sort::Bool);
    optimal.assert_soft(a, 1, None).unwrap();
    optimal.interrupt_native_maxsmt_after_execution_for_test();

    let optimal_result = optimal.check_sat_max().unwrap();
    assert!(optimal_result.is_unknown());
    assert_eq!(
        optimal.unknown_reason(),
        Some(crate::UnknownReason::Interrupted)
    );
    assert_eq!(
        optimal.executor.unknown_origin(),
        Some(crate::UnknownOrigin::InterruptFlag)
    );
    assert!(optimal.model_for_consumer().is_none());
    assert!(optimal.executor.last_maxsmt_outcome().is_none());
    assert_eq!(optimal.executor.timeout(), Some(Duration::from_mins(1)));
    assert_eq!(
        optimal.executor.memory_limit(),
        Some(PARSED_MEMORY_SENTINEL_BYTES),
        "late-result cleanup must restore the parsed executor ceiling"
    );
    assert_eq!(optimal.executor.current_solve_deadline(), None);
    optimal.clear_interrupt();

    let mut hard_unsat = Solver::try_new(Logic::QfUf).unwrap();
    let b = hard_unsat.declare_const("b", Sort::Bool);
    hard_unsat.try_assert_term(b).unwrap();
    let not_b = hard_unsat.try_not(b).unwrap();
    hard_unsat.try_assert_term(not_b).unwrap();
    hard_unsat.assert_soft(b, 1, None).unwrap();
    hard_unsat.interrupt_native_maxsmt_after_execution_for_test();

    let hard_unsat_result = hard_unsat.check_sat_max().unwrap();
    assert!(hard_unsat_result.is_unknown());
    assert_eq!(
        hard_unsat.unknown_reason(),
        Some(crate::UnknownReason::Interrupted)
    );
    assert_eq!(
        hard_unsat.executor.unknown_origin(),
        Some(crate::UnknownOrigin::InterruptFlag)
    );
    assert!(hard_unsat.executor.last_result_is_unknown());
    assert!(hard_unsat.last_proof().is_none());
    hard_unsat.clear_interrupt();
}
