// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate regressions for `ground_derivation::tests::lambda_source`.
//! These describe native replay of actual lambda reads, including its refusals.

use super::*;

fn lambda_read(extra_additions: usize) -> ChcExpr {
    let index = ChcVar::new("i", ChcSort::Int);
    let mut body = ChcExpr::add(ChcExpr::Var(index.clone()), var("bias"));
    for _ in 0..extra_additions {
        body = ChcExpr::add(body, ChcExpr::Int(1));
    }
    let array = ChcExpr::array_lambda(index, body).expect("typed closed template");
    ChcExpr::Op(
        crate::ChcOp::Select,
        vec![Arc::new(array), Arc::new(var("x"))],
    )
}

fn lambda_query(extra_additions: usize) -> ChcProblem {
    let expression = ChcExpr::Op(
        crate::ChcOp::Eq,
        vec![
            Arc::new(lambda_read(extra_additions)),
            Arc::new(var("expect")),
        ],
    );
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    // Retain the original source expression, without construction-time folding.
    problem.clauses_mut()[0].body.constraint = Some(expression);
    problem
}

fn lambda_derivation(expected: i128) -> GroundDerivation {
    GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: env(&[("bias", 5), ("x", 7), ("expect", expected)]),
            premises: vec![],
        }],
        query_step: 0,
    }
}

#[test]
fn native_ground_replays_a_captured_lambda_read() {
    let problem = lambda_query(0);
    assert!(problem_admits_native_ground_validation(&problem));
    assert_eq!(
        validate_ground_derivation(&problem, &lambda_derivation(12)),
        Ok(())
    );
    assert_eq!(
        validate_ground_derivation(&problem, &lambda_derivation(11)),
        Err(GroundDerivationError::ConstraintFalse { step: 0 }),
    );
}

#[test]
fn native_lambda_source_exposes_captures_without_private_formals() {
    let problem = lambda_query(0);
    let mut cache = GroundSourceSurfaceCache::new(&problem);
    let surface = cache
        .surface(0)
        .expect("small lambda source fits the native envelope");
    let names: Vec<_> = surface
        .variables
        .iter()
        .map(|variable| variable.name.as_str())
        .collect();
    assert_eq!(names, ["bias", "expect", "x"]);

    let mut missing = lambda_derivation(12);
    missing.steps[0].env.remove("bias");
    assert!(matches!(
        validate_ground_derivation(&problem, &missing),
        Err(GroundDerivationError::VariableBindingMissing { step: 0, .. }),
    ));
}

#[test]
fn native_lambda_source_charges_closed_body_work() {
    let small = lambda_query(0);
    let large = lambda_query(64);
    let mut small_cache = GroundSourceSurfaceCache::new(&small);
    small_cache.surface(0).expect("small lambda");
    let small_work = small_cache.work_used_for_test();
    let mut large_cache = GroundSourceSurfaceCache::new(&large);
    large_cache
        .surface(0)
        .expect("larger lambda still fits the normal envelope");
    assert!(large_cache.work_used_for_test() > small_work);
    let mut bounded = GroundSourceSurfaceCache::with_work_limit_for_test(&large, small_work);
    assert!(matches!(
        bounded.surface(0),
        Err(GroundSourceSurfaceError::SourceWorkLimitExceeded),
    ));
    assert_eq!(
        validate_ground_derivation(&large, &lambda_derivation(76)),
        Ok(())
    );
}

#[test]
fn native_lambda_replay_rejects_sort_changing_captures() {
    let mut problem = lambda_query(0);
    let original = problem.clauses()[0].body.constraint.as_ref().unwrap();
    let malformed =
        original.substitute(&[(ChcVar::new("bias", ChcSort::Int), ChcExpr::Bool(true))]);
    problem.clauses_mut()[0].body.constraint = Some(malformed);
    assert!(validate_ground_derivation(&problem, &lambda_derivation(12)).is_err());
}

#[test]
fn native_lambda_replay_keeps_cooperative_cancellation_terminal() {
    let problem = lambda_query(64);
    let derivation = lambda_derivation(76);
    let mut polls = 0;
    assert_eq!(
        validate_ground_derivation_with_progress(&problem, &derivation, &mut || {
            polls += 1;
            true
        }),
        Ok(()),
    );
    assert!(polls > 3);
    for stop in [1, polls / 2, polls] {
        let mut seen = 0;
        assert_eq!(
            validate_ground_derivation_with_progress(&problem, &derivation, &mut || {
                seen += 1;
                seen < stop
            }),
            Err(GroundDerivationError::Interrupted),
        );
    }
}
