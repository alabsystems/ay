// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn array_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(8)))
}

fn lambda_with_capture(name: &str) -> ChcExpr {
    let index = ChcVar::new("i", ChcSort::BitVec(8));
    ChcExpr::array_lambda(
        index.clone(),
        ChcExpr::Op(
            ChcOp::BvAdd,
            vec![
                Arc::new(ChcExpr::Var(index)),
                Arc::new(ChcExpr::Var(ChcVar::new(name, ChcSort::BitVec(8)))),
            ],
        ),
    )
    .expect("typed scalar lambda")
}

fn problem_with_array(value: ChcExpr, constraint: Option<ChcExpr>) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("inv", vec![array_sort()]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], constraint),
        ClauseHead::Predicate(predicate, vec![value]),
    ));
    let array = ChcExpr::Var(ChcVar::new("a", array_sort()));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(predicate, vec![array.clone()])],
            Some(ChcExpr::not(ChcExpr::eq(
                ChcExpr::select(array, ChcExpr::BitVec(3, 8)),
                ChcExpr::BitVec(10, 8),
            ))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn first_argument(problem: &ChcProblem) -> ChcExpr {
    match &problem.clauses()[0].head {
        ClauseHead::Predicate(_, args) => args[0].clone(),
        _ => panic!("expected initializer"),
    }
}

#[test]
fn lambda_observation_beta_reduces_captured_scalar() {
    let capture = ChcVar::new("x", ChcSort::BitVec(8));
    let mut problem = problem_with_array(lambda_with_capture("x"), None);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_some());
    assert!(!problem.has_array_lambda());
    assert_eq!(
        first_argument(&problem)
            .substitute(&[(capture, ChcExpr::BitVec(7, 8))])
            .simplify_constants(),
        ChcExpr::BitVec(10, 8)
    );
}

#[test]
fn lambda_observation_keeps_capture_with_private_binder_spelling_external() {
    let capture = ChcVar::new("ay!lambda!index", ChcSort::BitVec(8));
    let mut problem = problem_with_array(lambda_with_capture(&capture.name), None);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_some());
    assert_eq!(
        first_argument(&problem)
            .substitute(&[(capture, ChcExpr::BitVec(254, 8))])
            .simplify_constants(),
        ChcExpr::BitVec(1, 8)
    );
}

#[test]
fn lambda_observation_projects_array_assignment() {
    let array = ChcExpr::Var(ChcVar::new("a", array_sort()));
    let mut problem = problem_with_array(
        array.clone(),
        Some(ChcExpr::eq(array, lambda_with_capture("x"))),
    );
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_some());
    assert!(!problem.has_array_lambda());
    let constraint = problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("projected equality");
    let value = first_argument(&problem);
    let ChcExpr::Var(cell) = &value else {
        panic!("expected observed cell")
    };
    assert_eq!(
        constraint
            .substitute(&[
                (cell.clone(), ChcExpr::BitVec(10, 8)),
                (ChcVar::new("x", ChcSort::BitVec(8)), ChcExpr::BitVec(7, 8))
            ])
            .simplify_constants(),
        ChcExpr::Bool(true)
    );
}

#[test]
fn lambda_observation_keeps_store_overwrite_order() {
    let value = ChcExpr::store(
        lambda_with_capture("x"),
        ChcExpr::BitVec(3, 8),
        ChcExpr::BitVec(42, 8),
    );
    let mut problem = problem_with_array(value, None);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_some());
    assert_eq!(first_argument(&problem), ChcExpr::BitVec(42, 8));
}

#[test]
fn lambda_observation_preserves_parallel_capture_order() {
    let index = ChcVar::new("i", ChcSort::BitVec(8));
    let left = ChcVar::new("ay!lambda!capture1", ChcSort::BitVec(8));
    let right = ChcVar::new("ay!lambda!capture0", ChcSort::BitVec(8));
    let body = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::Var(index.clone())),
            Arc::new(ChcExpr::Op(
                ChcOp::BvSub,
                vec![
                    Arc::new(ChcExpr::Var(left.clone())),
                    Arc::new(ChcExpr::Var(right.clone())),
                ],
            )),
        ],
    );
    let value = ChcExpr::array_lambda(index, body).expect("typed two-capture lambda");
    let mut problem = problem_with_array(value, None);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_some());
    assert_eq!(
        first_argument(&problem)
            .substitute(&[
                (left, ChcExpr::BitVec(4, 8)),
                (right, ChcExpr::BitVec(2, 8))
            ])
            .simplify_constants(),
        ChcExpr::BitVec(5, 8)
    );
}

#[test]
fn lambda_observation_refuses_wrong_index_domain_without_mutation() {
    let mut problem = problem_with_array(lambda_with_capture("x"), None);
    let array = ChcExpr::Var(ChcVar::new("a", array_sort()));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::select(array, ChcExpr::BitVec(3, 16)),
            ChcExpr::BitVec(10, 8),
        )),
        ClauseHead::False,
    ));
    let before = format!("{:?}", problem);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_none());
    assert_eq!(format!("{:?}", problem), before);
}

#[test]
fn lambda_observation_refuses_extensional_disequality_without_mutation() {
    let lambda = lambda_with_capture("x");
    let other = lambda_with_capture("y");
    let mut problem = problem_with_array(
        ChcExpr::Var(ChcVar::new("a", array_sort())),
        Some(ChcExpr::not(ChcExpr::eq(lambda, other))),
    );
    let before = problem.clone();
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_none());
    assert_eq!(
        format!("{:?}", problem.clauses()),
        format!("{:?}", before.clauses())
    );
    assert_eq!(
        format!("{:?}", problem.predicates()),
        format!("{:?}", before.predicates())
    );
}

#[test]
fn lambda_observation_refuses_nested_array_result() {
    let inner = lambda_with_capture("x");
    let outer = ChcExpr::array_lambda(ChcVar::new("j", ChcSort::BitVec(8)), inner)
        .expect("typed nested array");
    let mut problem = problem_with_array(outer, None);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_none());
}

#[test]
fn lambda_observation_repeated_capture_has_exact_work_boundary() {
    let index = ChcVar::new("i", ChcSort::BitVec(8));
    let captured = ChcVar::new("x", ChcSort::BitVec(8));
    let body = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::Var(index.clone())),
            Arc::new(ChcExpr::Op(
                ChcOp::BvAdd,
                vec![
                    Arc::new(ChcExpr::Var(captured.clone())),
                    Arc::new(ChcExpr::Var(captured)),
                ],
            )),
        ],
    );
    let expression = ChcExpr::array_lambda(index, body).expect("typed lambda");
    let ChcExpr::ArrayLambda(lambda) = &expression else {
        panic!("lambda")
    };
    let expanded_capture = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::BitVec(2, 8)),
            Arc::new(ChcExpr::BitVec(3, 8)),
        ],
    );
    let lambda = lambda.with_captures(vec![Arc::new(expanded_capture)]);
    let work = ChcProblem::lambda_observation_work(&lambda, 1000, 8000, 256, || false)
        .expect("bounded observation");
    assert!(
        work.0 > 10,
        "both occurrences must charge the expanded capture"
    );
    assert_eq!(
        ChcProblem::lambda_observation_work(&lambda, work.0, work.1, 256, || false),
        Some(work)
    );
    assert_eq!(
        ChcProblem::lambda_observation_work(&lambda, work.0 - 1, work.1, 256, || false),
        None
    );
    assert!(work.1 > 0);
    assert!(
        ChcProblem::lambda_observation_work(&lambda, work.0, work.1 - 1, 256, || false).is_none()
    );
}

#[test]
fn lambda_observation_rejects_changed_capture_sort() {
    let expression = lambda_with_capture("x");
    let ChcExpr::ArrayLambda(lambda) = &expression else {
        panic!("lambda")
    };
    let invalid = ChcExpr::ArrayLambda(lambda.with_captures(vec![Arc::new(ChcExpr::Int(7))]));
    let mut problem = problem_with_array(invalid, None);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_none());
}

#[test]
fn lambda_observation_depth_includes_capture_substitution_site() {
    let mut body = ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)));
    let mut capture = ChcExpr::BitVec(7, 8);
    for _ in 0..9 {
        body = ChcExpr::Op(ChcOp::BvNot, vec![Arc::new(body)]);
        capture = ChcExpr::Op(ChcOp::BvNot, vec![Arc::new(capture)]);
    }
    let expression =
        ChcExpr::array_lambda(ChcVar::new("i", ChcSort::BitVec(8)), body).expect("typed lambda");
    let ChcExpr::ArrayLambda(lambda) = &expression else {
        panic!("lambda")
    };
    let lambda = lambda.with_captures(vec![Arc::new(capture)]);
    assert!(ChcProblem::lambda_observation_work(&lambda, 1000, 8000, 12, || false).is_none());
    assert!(ChcProblem::lambda_observation_work(&lambda, 1000, 8000, 25, || false).is_some());
}

#[test]
fn lambda_observation_cancellation_discards_preflight() {
    let problem = problem_with_array(lambda_with_capture("x"), None);
    let mut keys = FxHashMap::default();
    keys.insert(
        ChcSort::BitVec(8),
        [ConstIndex::BitVec(3, 8)].into_iter().collect(),
    );
    let mut polls = 0;
    let work = problem
        .admit_lambda_observations(&keys, 1000, || {
            polls += 1;
            false
        })
        .expect("complete preflight");
    assert!(work > 0 && polls > 0);
    for stop in 1..=polls {
        let mut count = 0;
        assert!(
            problem
                .admit_lambda_observations(&keys, 1000, || {
                    count += 1;
                    count == stop
                })
                .is_none(),
            "stop at poll {stop}"
        );
    }
}

#[test]
fn lambda_observation_expired_scope_leaves_problem_unchanged() {
    let mut problem = problem_with_array(lambda_with_capture("x"), None);
    let before = format!("{problem:?}");
    let _deadline = crate::smt::ScopedSmtDeadline::install(std::time::Duration::ZERO);
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_none());
    assert_eq!(format!("{problem:?}"), before);
}

#[test]
fn lambda_observation_folds_offset_before_projecting_capture_read() {
    let index = ChcVar::new("i", ChcSort::BitVec(8));
    let source = ChcExpr::Var(ChcVar::new("src", array_sort()));
    let body = ChcExpr::select(
        source.clone(),
        ChcExpr::Op(
            ChcOp::BvAdd,
            vec![
                Arc::new(ChcExpr::Var(index.clone())),
                Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
    );
    let lambda = ChcExpr::array_lambda(index, body).expect("typed offset lambda");
    let mut problem = problem_with_array(
        lambda,
        Some(ChcExpr::eq(
            ChcExpr::select(source, ChcExpr::BitVec(4, 8)),
            ChcExpr::BitVec(42, 8),
        )),
    );
    assert!(problem
        .try_scalarize_const_array_selects_allow_symbolic_keys_with_map(&[])
        .is_some());
    let constraint = problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("observed source equality");
    let ChcExpr::Op(ChcOp::Eq, args) = constraint else {
        panic!("expected source equality")
    };
    assert!(matches!(args[0].as_ref(), ChcExpr::Var(_)));
    assert_eq!(first_argument(&problem), *args[0]);
}
