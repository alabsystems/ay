// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn select(array: ChcExpr, index: ChcExpr) -> ChcExpr {
    ChcExpr::Op(crate::ChcOp::Select, vec![Arc::new(array), Arc::new(index)])
}

fn query(expression: ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    problem.clauses_mut()[0].body.constraint = Some(expression);
    problem
}

fn derivation(values: FxHashMap<String, SmtValue>) -> GroundDerivation {
    GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: values,
            premises: vec![],
        }],
        query_step: 0,
    }
}

fn equals_expected(read: ChcExpr) -> ChcProblem {
    query(ChcExpr::Op(
        crate::ChcOp::Eq,
        vec![Arc::new(read), Arc::new(var("expect"))],
    ))
}

#[test]
fn nested_lambda_reads_preserve_both_lexical_indices() {
    let outer = ChcVar::new("outer", ChcSort::Int);
    let inner = ChcVar::new("inner", ChcSort::Int);
    let inner_array = ChcExpr::array_lambda(
        inner.clone(),
        ChcExpr::add(ChcExpr::Var(outer.clone()), ChcExpr::Var(inner)),
    )
    .unwrap();
    let array = ChcExpr::array_lambda(outer, select(inner_array, ChcExpr::Int(3))).unwrap();
    let problem = equals_expected(select(array, ChcExpr::Int(2)));
    assert!(problem_admits_native_ground_validation(&problem));
    assert_eq!(
        validate_ground_derivation(&problem, &derivation(env(&[("expect", 5)]))),
        Ok(())
    );
    assert_eq!(
        validate_ground_derivation(&problem, &derivation(env(&[("expect", 6)]))),
        Err(GroundDerivationError::ConstraintFalse { step: 0 })
    );
    let mut cache = GroundSourceSurfaceCache::new(&problem);
    assert_eq!(
        cache.surface(0).unwrap().variables,
        vec![ChcVar::new("expect", ChcSort::Int)]
    );
}

#[test]
fn lambda_store_ite_reads_preserve_the_selected_value() {
    let index = ChcVar::new("i", ChcSort::Int);
    let array = ChcExpr::array_lambda(
        index.clone(),
        ChcExpr::add(ChcExpr::Var(index), var("bias")),
    )
    .unwrap();
    let store = ChcExpr::Op(
        crate::ChcOp::Store,
        vec![
            Arc::new(array.clone()),
            Arc::new(ChcExpr::Int(4)),
            Arc::new(ChcExpr::Int(99)),
        ],
    );
    let choice = ChcExpr::Op(
        crate::ChcOp::Ite,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("choice", ChcSort::Bool))),
            Arc::new(store),
            Arc::new(array),
        ],
    );
    for (choice_value, key, expected) in [(true, 4, 99), (false, 4, 9), (true, 8, 13)] {
        let problem = equals_expected(select(choice.clone(), ChcExpr::Int(key)));
        let mut values = env(&[("bias", 5), ("expect", expected)]);
        values.insert("choice".into(), SmtValue::Bool(choice_value));
        assert_eq!(
            validate_ground_derivation(&problem, &derivation(values.clone())),
            Ok(())
        );
        values.insert("expect".into(), SmtValue::Int(expected + 1));
        assert_eq!(
            validate_ground_derivation(&problem, &derivation(values)),
            Err(GroundDerivationError::ConstraintFalse { step: 0 })
        );
    }
}

fn repeated_capture(repetitions: usize) -> ChcProblem {
    let index = ChcVar::new("i", ChcSort::Int);
    let mut body = ChcExpr::Var(index.clone());
    for _ in 0..repetitions {
        body = ChcExpr::add(body, var("capture"));
    }
    let array = ChcExpr::array_lambda(index, body).unwrap();
    let mut capture = var("input");
    for _ in 0..8 {
        capture = ChcExpr::add(capture, ChcExpr::Int(1));
    }
    let array = array.substitute(&[(ChcVar::new("capture", ChcSort::Int), capture)]);
    equals_expected(select(array, ChcExpr::Int(2)))
}

#[test]
fn repeated_capture_expansion_has_an_exact_finite_budget_edge() {
    let small = repeated_capture(1);
    let large = repeated_capture(8);
    let cost = |problem: &ChcProblem| {
        let mut cache = GroundSourceSurfaceCache::new(problem);
        cache
            .reserve_lambda_replay(
                &problem.clauses()[0],
                &mut GroundValidationControl::new(&mut || true),
            )
            .unwrap()
            .work
    };
    let small_cost = cost(&small);
    let large_cost = cost(&large);
    assert!(
        large_cost > small_cost * 4,
        "repeated references must repeatedly price their capture"
    );
    let mut exact = GroundSourceSurfaceCache::with_work_limit_for_test(&large, large_cost);
    assert_eq!(
        exact
            .reserve_lambda_replay(
                &large.clauses()[0],
                &mut GroundValidationControl::new(&mut || true)
            )
            .map(|profile| profile.work),
        Ok(large_cost)
    );
    let mut short = GroundSourceSurfaceCache::with_work_limit_for_test(&large, large_cost - 1);
    assert!(matches!(
        short.reserve_lambda_replay(
            &large.clauses()[0],
            &mut GroundValidationControl::new(&mut || true)
        ),
        Err(GroundSourceSurfaceError::SourceWorkLimitExceeded)
    ));
    assert_eq!(
        validate_ground_derivation(&large, &derivation(env(&[("input", 3), ("expect", 90)]))),
        Ok(())
    );
    assert_eq!(
        validate_ground_derivation(&large, &derivation(env(&[("input", 3), ("expect", 89)]))),
        Err(GroundDerivationError::ConstraintFalse { step: 0 })
    );
}

#[test]
fn virtual_expansion_cancellation_is_terminal_at_every_poll() {
    let problem = repeated_capture(4);
    let mut count = 0;
    GroundSourceSurfaceCache::new(&problem)
        .reserve_lambda_replay(
            &problem.clauses()[0],
            &mut GroundValidationControl::new(&mut || {
                count += 1;
                true
            }),
        )
        .unwrap();
    for stop in 1..=count {
        let mut seen = 0;
        let result = GroundSourceSurfaceCache::new(&problem).reserve_lambda_replay(
            &problem.clauses()[0],
            &mut GroundValidationControl::new(&mut || {
                seen += 1;
                seen < stop
            }),
        );
        assert!(
            matches!(result, Err(GroundSourceSurfaceError::Interrupted)),
            "stop {stop} of {count}"
        );
        assert_eq!(seen, stop);
    }
}

#[test]
fn bound_code_uf_observations_are_explicitly_refused() {
    let index = ChcVar::new("i", ChcSort::Int);
    for argument in [ChcExpr::Var(index.clone()), ChcExpr::Int(0)] {
        let array = ChcExpr::array_lambda(index.clone(), int_uf("f", argument)).unwrap();
        let problem = equals_expected(select(array, ChcExpr::Int(3)));
        assert!(!problem_admits_native_ground_validation(&problem));
        assert_eq!(
            validate_ground_derivation(&problem, &derivation(env(&[("expect", 4)]))),
            Err(GroundDerivationError::InvalidSourceProblem)
        );
    }
}

#[test]
fn capture_uf_uses_the_existing_outer_observation_contract() {
    let index = ChcVar::new("i", ChcSort::Int);
    let array = ChcExpr::array_lambda(
        index.clone(),
        ChcExpr::add(ChcExpr::Var(index), var("bias")),
    )
    .unwrap();
    let fx = int_uf("f", var("x"));
    let array = array.substitute(&[(ChcVar::new("bias", ChcSort::Int), fx.clone())]);
    let problem = equals_expected(select(array, ChcExpr::Int(7)));
    let mut values = env(&[("x", 0), ("expect", 12)]);
    install_observation(&mut values, fx.clone(), 5);
    assert_eq!(
        validate_ground_derivation(&problem, &derivation(values)),
        Ok(())
    );
    assert!(
        validate_ground_derivation(&problem, &derivation(env(&[("x", 0), ("expect", 12)])))
            .is_err()
    );

    let conflict = int_uf("f", ChcExpr::Int(0));
    let constraint = ChcExpr::and(
        problem.clauses()[0].body.constraint.clone().unwrap(),
        ChcExpr::eq(conflict.clone(), ChcExpr::Int(6)),
    );
    let problem = query(constraint);
    let mut values = env(&[("x", 0), ("expect", 12)]);
    // The checked observation installer itself rejects conflicting concrete
    // keys. Supply the hostile syntactic observations directly, as the
    // existing ground-congruence negative controls do.
    use crate::expr::evaluate::{
        uf_application_model_key, UF_APPLICATION_MODEL_MARKER_KEY,
        UF_APPLICATION_MODEL_MARKER_VALUE,
    };
    values.insert(uf_application_model_key(&fx).unwrap(), SmtValue::Int(5));
    values.insert(
        uf_application_model_key(&conflict).unwrap(),
        SmtValue::Int(6),
    );
    values.insert(
        UF_APPLICATION_MODEL_MARKER_KEY.into(),
        SmtValue::Opaque(UF_APPLICATION_MODEL_MARKER_VALUE.into()),
    );
    assert!(matches!(
        validate_ground_derivation(&problem, &derivation(values)),
        Err(GroundDerivationError::UfCongruenceViolation { step: 0, .. })
    ));
}

#[test]
fn native_lambda_support_does_not_admit_wire_artifacts() {
    let problem = repeated_capture(1);
    let derivation = derivation(env(&[("input", 3), ("expect", 13)]));
    assert_eq!(validate_ground_derivation(&problem, &derivation), Ok(()));
    assert!(artifact::encode_ground_derivation_artifact(&problem, &derivation).is_err());
    assert!(artifact::encode_ground_derivation_artifact_v2(&problem, &derivation).is_err());
}

#[test]
fn scoped_surface_rejects_a_sort_changing_capture_before_replay() {
    let index = ChcVar::new("i", ChcSort::Int);
    let array = ChcExpr::array_lambda(
        index.clone(),
        ChcExpr::add(ChcExpr::Var(index), var("bias")),
    )
    .unwrap();
    let malformed = array.substitute(&[(ChcVar::new("bias", ChcSort::Int), ChcExpr::Bool(true))]);
    let problem = equals_expected(select(malformed, ChcExpr::Int(7)));
    assert!(matches!(
        GroundSourceSurfaceCache::new(&problem).surface(0),
        Err(GroundSourceSurfaceError::InvalidVariableSurface)
    ));
}

fn op(operator: crate::ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

#[test]
fn range_copy_lambda_replays_the_mc_memory_shape() {
    use crate::ChcOp;
    let word = ChcSort::BitVec(64);
    let byte = ChcSort::BitVec(8);
    let array_sort = ChcSort::Array(Box::new(word.clone()), Box::new(byte.clone()));
    let typed = |name: &str, sort: &ChcSort| ChcExpr::Var(ChcVar::new(name, sort.clone()));
    let index = ChcVar::new("i", word.clone());
    let i = ChcExpr::Var(index.clone());
    let lo = typed("lo", &word);
    let copied = select(
        typed("src", &array_sort),
        op(
            ChcOp::BvAdd,
            vec![
                op(ChcOp::BvSub, vec![i.clone(), lo.clone()]),
                typed("src_lo", &word),
            ],
        ),
    );
    let condition = op(
        ChcOp::And,
        vec![
            op(ChcOp::BvULe, vec![lo, i.clone()]),
            op(ChcOp::BvULt, vec![i.clone(), typed("hi", &word)]),
        ],
    );
    let body = op(
        ChcOp::Ite,
        vec![condition, copied, select(typed("dst", &array_sort), i)],
    );
    let lambda = ChcExpr::array_lambda(index, body).unwrap();
    let problem = query(op(
        ChcOp::Eq,
        vec![
            select(lambda, typed("key", &word)),
            typed("expected", &byte),
        ],
    ));
    let mut values = FxHashMap::default();
    for (name, value) in [("lo", 10), ("hi", 12), ("src_lo", 20)] {
        values.insert(name.into(), SmtValue::BitVec(value, 64));
    }
    values.insert(
        "src".into(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::BitVec(0, 8)),
            entries: vec![
                (SmtValue::BitVec(20, 64), SmtValue::BitVec(65, 8)),
                (SmtValue::BitVec(21, 64), SmtValue::BitVec(66, 8)),
            ],
        },
    );
    values.insert(
        "dst".into(),
        SmtValue::ConstArray(Box::new(SmtValue::BitVec(90, 8))),
    );
    for (key, expected) in [(9, 90), (10, 65), (11, 66), (12, 90)] {
        values.insert("key".into(), SmtValue::BitVec(key, 64));
        values.insert("expected".into(), SmtValue::BitVec(expected, 8));
        assert_eq!(
            validate_ground_derivation(&problem, &derivation(values.clone())),
            Ok(())
        );
        values.insert("expected".into(), SmtValue::BitVec(expected + 1, 8));
        assert_eq!(
            validate_ground_derivation(&problem, &derivation(values.clone())),
            Err(GroundDerivationError::ConstraintFalse { step: 0 })
        );
    }
}

#[test]
fn array_valued_lambda_result_remains_an_explicit_replay_gap() {
    let outer = ChcVar::new("outer", ChcSort::Int);
    let inner = ChcVar::new("inner", ChcSort::Int);
    let inner_array = ChcExpr::array_lambda(
        inner.clone(),
        ChcExpr::add(ChcExpr::Var(outer.clone()), ChcExpr::Var(inner)),
    )
    .unwrap();
    let array = ChcExpr::array_lambda(outer, inner_array).unwrap();
    let problem = equals_expected(select(select(array, ChcExpr::Int(2)), ChcExpr::Int(3)));
    assert!(problem_admits_native_ground_validation(&problem));
    // The mathematical result is 5, but native canonical evaluation cannot
    // materialize a functional array as the first read's intermediate value.
    for expected in [5, 6] {
        assert_eq!(
            validate_ground_derivation(&problem, &derivation(env(&[("expect", expected)]))),
            Err(GroundDerivationError::ConstraintNotGround { step: 0 })
        );
    }
}
