// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::{Logic, Sort};

fn native_sat() -> (Solver, Term) {
    let mut solver = Solver::new(Logic::QfUf);
    let term = solver.declare_const("p", Sort::Bool);
    solver.assert_term(term);
    assert!(solver.check_sat().is_sat());
    assert_eq!(solver.try_get_value(term).unwrap(), ModelValue::Bool(true));
    (solver, term)
}

#[test]
fn cancelled_native_getters_preserve_sat_and_allow_fresh_reads() {
    let (solver, term) = native_sat();
    let validated = solver.executor.was_model_validated();
    solver.interrupt();
    assert!(solver.try_get_value(term).is_err());
    assert!(solver.try_get_values(&[term]).is_err());
    assert!(solver.try_get_model_str().is_err());
    assert!(solver.try_get_model().is_err());
    assert!(solver.try_get_model_map().is_err());
    assert!(solver.values_smtlib(&[term]).is_none());
    assert!(solver.executor.last_result().unwrap().is_sat());
    assert_eq!(solver.executor.was_model_validated(), validated);
    solver.clear_interrupt();
    assert_eq!(solver.try_get_value(term).unwrap(), ModelValue::Bool(true));
    assert!(solver.try_get_model_str().is_ok());
    assert!(solver.try_get_model().is_ok());
    assert_eq!(
        solver.try_get_model_map().unwrap().get("p"),
        Some(&ModelValue::Bool(true))
    );
}

#[test]
fn nested_native_getter_cannot_rearm_a_cancelled_outer_read() {
    let (solver, term) = native_sat();
    let result = solver.with_model_evaluation_read(|| {
        solver.interrupt();
        assert!(solver.executor.check_evaluation_read().is_err());
        solver.clear_interrupt();
        assert!(solver.try_get_values(&[term]).is_err());
        assert!(solver.try_get_model_map().is_err());
        // A caller-owned fallback still cannot turn this read into success.
        Ok(ModelValue::Bool(true))
    });
    assert!(matches!(result, Err(SolverError::ModelGenerationFailed(_))));
    assert_eq!(solver.try_get_value(term).unwrap(), ModelValue::Bool(true));
}

#[test]
fn empty_native_batches_do_not_return_success_after_cancellation() {
    let (solver, _) = native_sat();
    solver.interrupt();
    assert!(solver.try_get_values(&[]).is_err());
    assert!(solver.try_get_named_values(&[]).is_err());
    assert!(solver.values_smtlib(&[]).is_none());
    solver.clear_interrupt();
    assert_eq!(solver.try_get_values(&[]).unwrap(), [] as [ModelValue; 0]);
    assert_eq!(
        solver.try_get_named_values(&[]).unwrap(),
        [] as [ModelValue; 0]
    );
    assert_eq!(solver.values_smtlib(&[]), Some("()".into()));
}

#[test]
fn native_post_sat_reads_use_current_timeout_and_term_memory_limits() {
    let (mut solver, term) = native_sat();
    solver.set_timeout(Some(std::time::Duration::ZERO));
    assert!(solver.try_get_value(term).is_err());
    assert!(solver.executor.last_result().unwrap().is_sat());
    solver.set_timeout(None);
    assert_eq!(solver.try_get_value(term).unwrap(), ModelValue::Bool(true));
    solver.set_term_memory_limit(Some(0));
    assert!(solver.try_get_value(term).is_err());
    assert!(solver.executor.last_result().unwrap().is_sat());
    solver.set_term_memory_limit(None);
    assert_eq!(solver.try_get_value(term).unwrap(), ModelValue::Bool(true));
}
