// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::{Logic, ModelValue, Sort};

fn arm_post_result_panic(solver: &Solver) {
    PANIC_AFTER_SOLVE.with(|armed| armed.set(Some(solver as *const Solver as usize)));
}

fn assert_caught_panic<T>(result: Result<T, SolverError>) {
    assert!(matches!(result, Err(SolverError::SolverPanic(_))));
}

#[test]
fn caught_plain_solve_panic_revokes_sat_model_and_value_in_every_wrapper() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);

    for variant in 0..3 {
        assert!(solver.check_sat().is_sat());
        assert_eq!(solver.try_get_value(p).unwrap(), ModelValue::Bool(true));
        assert!(solver.try_get_model_str().is_ok());
        arm_post_result_panic(&solver);
        match variant {
            0 => assert_caught_panic(solver.try_check_sat()),
            1 => assert_caught_panic(solver.try_check_sat_with_details()),
            _ => assert_caught_panic(solver.try_check_sat_with_timeout(Duration::from_secs(1))),
        }
        assert!(solver.executor.last_result_is_unknown());
        assert_eq!(solver.unknown_reason(), Some(UnknownReason::InternalError));
        assert!(solver.try_get_model_str().is_err());
        assert!(solver.try_get_value(p).is_err());
        assert!(solver.model_for_consumer().is_none());
        assert!(solver.last_proof().is_none());
        assert!(solver.try_get_unsat_core().is_err());
        assert!(solver.unsat_assumptions().is_none());
        // This injection occurs after a completed solve and its normal frame
        // restoration. It does not claim recovery from arbitrary mid-solve
        // internal corruption.
        assert!(solver.check_sat().is_sat());
    }
}

#[test]
fn caught_plain_solve_panic_revokes_unsat_proof_and_core() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    let contradiction = solver.bool_const(false);
    solver.assert_term(contradiction);
    assert!(solver.check_sat().is_unsat());
    assert!(solver.last_proof().is_some());
    assert!(solver.try_get_unsat_core().is_ok());

    arm_post_result_panic(&solver);
    assert_caught_panic(solver.try_check_sat());
    assert!(solver.executor.last_result_is_unknown());
    assert!(solver.last_proof().is_none());
    assert!(solver.try_get_unsat_core().is_err());
    assert!(solver.unsat_assumptions().is_none());
    assert!(solver.check_sat().is_unsat());
}

#[test]
fn caught_assumption_solve_panic_revokes_unsat_assumptions_in_both_wrappers() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.set_produce_unsat_cores(true);

    for variant in 0..2 {
        assert!(solver.check_sat_assuming(&[not_p]).is_unsat());
        assert_eq!(solver.unsat_assumptions(), Some(vec![not_p]));
        assert!(solver.try_get_unsat_core().is_ok());
        arm_post_result_panic(&solver);
        if variant == 0 {
            assert_caught_panic(solver.try_check_sat_assuming(&[not_p]));
        } else {
            assert_caught_panic(solver.try_check_sat_assuming_with_details(&[not_p]));
        }
        assert!(solver.executor.last_result_is_unknown());
        assert!(solver.unsat_assumptions().is_none());
        assert!(solver.last_proof().is_none());
        assert!(solver.try_get_unsat_core().is_err());
        assert!(solver.try_get_model_str().is_err());
        assert!(solver.check_sat_assuming(&[not_p]).is_unsat());
    }
}
