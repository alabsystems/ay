// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for model and value extraction: declared_variables, get_model_map,
//! try_get_model*, try_get_value*, backward-compatible option-returning getters.

use num_bigint::BigInt;

use crate::api::*;

#[test]
fn test_declared_variables_excludes_fresh_vars() {
    let mut solver = Solver::new(Logic::QfLia);
    let _x = solver.declare_const("x", Sort::Int);
    let _y = solver.declare_const("y", Sort::Bool);
    let _fresh = solver.fresh_var("tmp", Sort::Int);

    let mut names: Vec<_> = solver
        .declared_variables()
        .map(|(name, _)| name.to_string())
        .collect();
    names.sort_unstable();
    assert_eq!(names, vec!["x".to_string(), "y".to_string()]);
}

#[test]
fn test_get_model_map_returns_structured_assignments() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let seven = solver.int_const(7);
    let nine = solver.int_const(9);
    let x_eq_7 = solver.eq(x, seven);
    let y_eq_9 = solver.eq(y, nine);
    solver.assert_term(x_eq_7);
    solver.assert_term(y_eq_9);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model_map = solver.model_map().expect("SAT should provide model map");
    assert_eq!(
        model_map.get("x"),
        Some(&ModelValue::Int(BigInt::from(7))),
        "x should be assigned"
    );
    assert_eq!(
        model_map.get("y"),
        Some(&ModelValue::Int(BigInt::from(9))),
        "y should be assigned"
    );
}

#[test]
fn test_get_model_map_returns_none_when_last_result_not_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert!(solver.check_sat().is_unsat());
    assert!(solver.model_map().is_none());
}

#[test]
fn test_try_get_model_no_result() {
    let solver = Solver::new(Logic::QfLia);
    let err = solver.try_get_model().unwrap_err();
    assert!(
        matches!(err, SolverError::NoResult),
        "expected NoResult, got {err:?}"
    );
}

#[test]
fn test_try_get_model_str_no_result() {
    let solver = Solver::new(Logic::QfLia);
    let err = solver.try_get_model_str().unwrap_err();
    assert!(
        matches!(err, SolverError::NoResult),
        "expected NoResult, got {err:?}"
    );
}

#[test]
fn test_try_get_model_map_no_result() {
    let solver = Solver::new(Logic::QfLia);
    let err = solver.try_get_model_map().unwrap_err();
    assert!(
        matches!(err, SolverError::NoResult),
        "expected NoResult, got {err:?}"
    );
}

#[test]
fn test_try_get_model_after_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert!(solver.check_sat().is_unsat());

    let err = solver.try_get_model().unwrap_err();
    assert!(
        matches!(err, SolverError::NotSat),
        "expected NotSat, got {err:?}"
    );
}

#[test]
fn test_try_get_model_str_after_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert!(solver.check_sat().is_unsat());

    let err = solver.try_get_model_str().unwrap_err();
    assert!(
        matches!(err, SolverError::NotSat),
        "expected NotSat, got {err:?}"
    );
}

#[test]
fn test_try_get_model_map_after_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    solver.assert_term(x_gt_0);
    solver.assert_term(x_lt_0);
    assert!(solver.check_sat().is_unsat());

    let err = solver.try_get_model_map().unwrap_err();
    assert!(
        matches!(err, SolverError::NotSat),
        "expected NotSat, got {err:?}"
    );
}

#[test]
fn test_try_get_model_after_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver.try_get_model().expect("should succeed after SAT");
    assert!(!model.model().is_empty());
}

#[test]
fn test_try_get_model_for_consumer_after_validated_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .try_get_model_for_consumer()
        .expect("validated SAT should provide consumer model");
    assert_eq!(model.model().int_val_i64("x"), Some(5));
}

#[test]
fn test_try_model_blocking_clause_for_consumer_blocks_validated_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let blocking = solver
        .try_model_blocking_clause_for_consumer(&[x])
        .expect("validated SAT should produce model-blocking clause");
    assert_eq!(blocking.schema, AY_MODEL_BLOCKING_CLAUSE_SCHEMA);
    assert_eq!(
        blocking.schema_version,
        AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION
    );
    assert_eq!(blocking.assignment_count(), 1);
    assert!(blocking.accepted_for_consumer);
    assert!(!blocking.fail_closed);
    assert_eq!(blocking.assignments[0].term, x);
    assert_eq!(
        blocking.assignments[0].value,
        ModelValue::Int(BigInt::from(5))
    );
    assert_eq!(blocking.assignments[0].value_kind, "Int");
    assert_eq!(blocking.assignments[0].value_smtlib, "5");
    let json = blocking.to_json_value();
    assert_eq!(json["schema"], AY_MODEL_BLOCKING_CLAUSE_SCHEMA);
    assert_eq!(json["assignment_count"], 1);
    assert_eq!(json["accepted_for_consumer"], true);
    let evidence = blocking.evidence_descriptor();
    assert_eq!(evidence.schema, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA);
    assert_eq!(
        evidence.schema_version,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION
    );
    assert_eq!(evidence.clause_schema, AY_MODEL_BLOCKING_CLAUSE_SCHEMA);
    assert_eq!(
        evidence.status_code,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS
    );
    assert_eq!(
        evidence.reason_code,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON
    );
    assert_eq!(evidence.assignment_count, 1);
    assert_eq!(evidence.value_kinds, vec!["Int"]);
    assert!(evidence.accepted_for_consumer);
    assert!(!evidence.fail_closed);
    let evidence_json = evidence.to_json_value();
    assert_eq!(
        evidence_json["schema"],
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA
    );
    assert_eq!(evidence_json["assignment_count"], 1);
    assert_eq!(evidence_json["value_kinds"], serde_json::json!(["Int"]));
    assert!(
        evidence_json.get("clause").is_none(),
        "compact evidence should not expose raw clause internals"
    );
    assert!(
        evidence_json.get("assignments").is_none(),
        "compact evidence should not expose assignment internals"
    );
    let evidence_pairs = blocking.evidence_key_value_pairs();
    assert_eq!(evidence_pairs[0], ("schema", evidence.schema.to_string()));
    assert!(evidence_pairs.contains(&(
        "status",
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS.to_string()
    )));
    assert!(evidence_pairs.contains(&("assignment_count", "1".to_string())));
    assert!(evidence_pairs.contains(&("value_kinds", "Int".to_string())));

    solver
        .try_assert_term(blocking.clause)
        .expect("blocking clause is Bool");
    assert!(
        solver.check_sat().is_unsat(),
        "x = 5 plus AY-owned blocking clause should be UNSAT"
    );
}

#[test]
fn test_try_assert_model_blocking_clause_for_consumer_blocks_boolean_projection() {
    let mut solver = Solver::new(Logic::QfUf);
    let b = solver.declare_const("b", Sort::Bool);
    let b_true = solver.bool_const(true);
    let eq = solver.eq(b, b_true);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let blocking = solver
        .try_assert_model_blocking_clause_for_consumer(&[b])
        .expect("validated SAT should assert model-blocking clause");
    assert_eq!(blocking.assignment_count(), 1);
    assert_eq!(blocking.assignments[0].value, ModelValue::Bool(true));
    assert!(
        solver.check_sat().is_unsat(),
        "asserted blocking clause should exclude the only Boolean model"
    );
}

#[test]
fn test_try_model_blocking_clause_for_consumer_rejects_empty_projection() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let err = solver
        .try_model_blocking_clause_for_consumer(&[])
        .unwrap_err();
    assert!(
        matches!(err, SolverError::ModelBlockingEmptyProjection),
        "expected ModelBlockingEmptyProjection, got {err:?}"
    );
}

#[test]
fn test_try_get_model_for_consumer_rejects_unvalidated_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver.executor.set_model_validated_for_testing(false);

    let err = solver.try_get_model_for_consumer().unwrap_err();
    assert!(
        matches!(err, SolverError::SatModelNotValidated),
        "expected SatModelNotValidated, got {err:?}"
    );
    assert!(
        solver.model_for_consumer().is_none(),
        "option-returning consumer model helper must fail closed"
    );
}

#[test]
fn test_try_model_blocking_clause_for_consumer_rejects_unvalidated_sat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let eq = solver.eq(x, five);
    solver.assert_term(eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    solver.executor.set_model_validated_for_testing(false);

    let err = solver
        .try_model_blocking_clause_for_consumer(&[x])
        .unwrap_err();
    assert!(
        matches!(err, SolverError::SatModelNotValidated),
        "expected SatModelNotValidated, got {err:?}"
    );
}

#[test]
fn test_consumer_acceptance_error_maps_to_solver_error() {
    let err: SolverError = ConsumerAcceptanceError::SatModelNotValidated.into();
    assert!(
        matches!(err, SolverError::SatModelNotValidated),
        "expected SatModelNotValidated, got {err:?}"
    );
}

mod post_solve_access;
