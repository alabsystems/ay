// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::pdr::{PdrConfig, PdrSolver};
use crate::{ChcParser, PredicateId, SmtValue};
use ay_core::kani_compat::DetHashMap;
use std::time::Duration;

fn finite_problem() -> ChcProblem {
    ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel P ((_ BitVec 2) Bool))
        (declare-var x (_ BitVec 2))
        (declare-var b Bool)
        (rule (=> (and (= x #b00) b) (P x b)))
        (rule (=> (and (= x #b01) b) (P x b)))
        (rule (=> (and (P x b) (not b)) false))
        (check-sat)
    "#,
    )
    .unwrap()
}

fn descriptor(problem: &ChcProblem) -> AcyclicSurvivor {
    ClauseInliner::capture_acyclic_survivor_until(
        problem,
        Instant::now() + Duration::from_secs(10),
        &CancellationToken::new(),
    )
    .unwrap()
    .expect("eligible single acyclic predicate")
}

fn candidate(problem: &ChcProblem) -> InvariantModel {
    descriptor(problem)
        .materialize_until(
            Instant::now() + Duration::from_secs(10),
            &CancellationToken::new(),
        )
        .unwrap()
        .expect("closed candidate")
}

fn verifies(problem: &ChcProblem, model: &InvariantModel) -> bool {
    let mut verifier = PdrSolver::new(
        problem.clone(),
        PdrConfig {
            strict_proofs: true,
            preserve_original_clauses: true,
            disable_array_scalarization: true,
            solve_timeout: Some(Duration::from_secs(5)),
            ..PdrConfig::default()
        },
    );
    verifier.verify_model_per_rule(model, Duration::from_secs(5))
}

fn apply(interpretation: &PredicateInterpretation, values: &[SmtValue]) -> bool {
    let bindings: DetHashMap<_, _> = interpretation
        .vars
        .iter()
        .zip(values)
        .map(|(var, value)| (var.name.clone(), value.clone()))
        .collect();
    match crate::expr::evaluate_expr(&interpretation.formula, &bindings) {
        Some(SmtValue::Bool(value)) => value,
        other => panic!("closed finite candidate must evaluate: {other:?}"),
    }
}

#[test]
fn all_definitions_are_retained_and_original_rules_are_authority() {
    let problem = finite_problem();
    let model = candidate(&problem);
    assert!(!model.convergence_proven && !model.individually_inductive);
    assert!(verifies(&problem, &model));
    let interpretation = model.get(&PredicateId::new(0)).unwrap();
    for value in 0..4 {
        for flag in [false, true] {
            assert_eq!(
                apply(
                    interpretation,
                    &[SmtValue::BitVec(value, 2), SmtValue::Bool(flag)]
                ),
                value < 2 && flag
            );
        }
    }
    let mut incomplete = descriptor(&problem);
    incomplete.definitions.pop();
    let omitted = incomplete.materialize(&|| true).unwrap();
    assert!(
        !verifies(&problem, &omitted),
        "omitted incoming definition must be rejected"
    );
    let formals = interpretation.vars.clone();
    let mut corrupted = model;
    corrupted.set(
        PredicateId::new(0),
        PredicateInterpretation::new(formals, ChcExpr::Bool(true)),
    );
    assert!(!verifies(&problem, &corrupted));
}

#[test]
fn unsafe_second_definition_is_not_hidden_by_projection() {
    let mut problem = finite_problem();
    let clause = &mut problem.clauses_mut()[1];
    let ClauseHead::Predicate(_, args) = &clause.head else {
        panic!("fact");
    };
    clause.body.constraint = Some(ChcExpr::and(
        ChcExpr::eq(args[0].clone(), ChcExpr::BitVec(1, 2)),
        ChcExpr::not(args[1].clone()),
    ));
    let model = candidate(&problem);
    assert!(apply(
        model.get(&PredicateId::new(0)).unwrap(),
        &[SmtValue::BitVec(1, 2), SmtValue::Bool(false)]
    ));
    assert!(!verifies(&problem, &model));
}

#[test]
fn repeated_and_compound_heads_preserve_positions_and_close_locals() {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-rel P (Int Int))
        (declare-var x Int)
        (declare-var y Int)
        (declare-var local Int)
        (rule (=> (= x 0) (P x x)))
        (rule (=> (and (= local 1) (= x local)) (P (+ x 1) x)))
        (rule (=> (and (P x y) (< x y)) false))
        (check-sat)
    "#,
    )
    .unwrap();
    let model = candidate(&problem);
    assert!(verifies(&problem, &model));
    let interpretation = model.get(&PredicateId::new(0)).unwrap();
    assert_ne!(interpretation.vars[0].name, interpretation.vars[1].name);
    for x in 0..3 {
        for y in 0..3 {
            assert_eq!(
                apply(interpretation, &[SmtValue::Int(x), SmtValue::Int(y)]),
                (x, y) == (0, 0) || (x, y) == (2, 1)
            );
        }
    }
}

#[test]
fn malformed_missing_recursive_and_multi_predicate_shapes_decline() {
    let base = finite_problem();
    for mutation in 0..6 {
        let mut problem = base.clone();
        let clause = &mut problem.clauses_mut()[0];
        let ClauseHead::Predicate(id, args) = &mut clause.head else {
            panic!("fact");
        };
        match mutation {
            0 => {
                args.pop();
            }
            1 => {
                args[0] = ChcExpr::Bool(true);
            }
            2 => {
                *id = PredicateId::new(99);
            }
            3 => {
                clause.body.predicates.push((*id, args.clone()));
            }
            4 => {
                clause.body.constraint = Some(ChcExpr::PredicateApp(
                    "P".into(),
                    *id,
                    args.iter().cloned().map(std::sync::Arc::new).collect(),
                ));
            }
            _ => {
                problem.declare_predicate("Extra", vec![]);
            }
        }
        assert!(capture(&problem, &|| true).is_none(), "mutation {mutation}");
    }
    let mut missing = ChcProblem::new();
    let p = missing.declare_predicate("Missing", vec![]);
    missing.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![],
    )])));
    assert!(capture(&missing, &|| true).is_none());
    let mut query = base;
    query.clauses_mut()[2].body.predicates[0].0 = PredicateId::new(99);
    assert!(capture(&query, &|| true).is_none());
}

#[test]
fn exact_census_declines_deep_open_ill_typed_and_unsupported_outputs() {
    let source = descriptor(&finite_problem());
    let mut interpretation = candidate(&finite_problem())
        .get(&source.predicate.id)
        .unwrap()
        .clone();
    interpretation.formula = ChcExpr::var(ChcVar::new("unbound", ChcSort::Bool));
    assert!(!closed_and_typed(
        &interpretation,
        &source.predicate,
        &|| true
    ));
    interpretation.formula = ChcExpr::eq(ChcExpr::Int(1), ChcExpr::Bool(true));
    assert!(!closed_and_typed(
        &interpretation,
        &source.predicate,
        &|| true
    ));
    let mut deep = ChcExpr::Bool(true);
    for _ in 0..=MAX_DEPTH {
        deep = ChcExpr::Op(crate::ChcOp::Not, vec![std::sync::Arc::new(deep)]);
    }
    let mut remaining = MAX_NODES;
    assert!(census(&deep, &mut remaining, None, &|| true).is_none());
    assert!(census(&ChcExpr::Bool(true), &mut 0, None, &|| true).is_none());
    for sort in [
        ChcSort::BitVec(0),
        ChcSort::BitVec(257),
        ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Bool)),
    ] {
        let mut remaining = MAX_NODES;
        assert!(census(
            &ChcExpr::var(ChcVar::new("unsupported", sort)),
            &mut remaining,
            None,
            &|| true
        )
        .is_none());
    }
}

#[test]
fn every_capture_and_synthesis_poll_can_stop_without_a_partial_candidate() {
    let problem = finite_problem();
    let descriptor = descriptor(&problem);
    for materialize in [false, true] {
        let count = Cell::new(0usize);
        let count_poll = || {
            count.set(count.get() + 1);
            true
        };
        if materialize {
            assert!(descriptor.materialize(&count_poll).is_some());
        } else {
            assert!(capture(&problem, &count_poll).is_some());
        }
        for stop_at in 1..=count.get() {
            let calls = Cell::new(0usize);
            let poll = || {
                calls.set(calls.get() + 1);
                calls.get() != stop_at
            };
            if materialize {
                assert!(descriptor.materialize(&poll).is_none(), "poll {stop_at}");
            } else {
                assert!(capture(&problem, &poll).is_none(), "poll {stop_at}");
            }
            assert_eq!(
                calls.get(),
                stop_at,
                "no work may resume after a refused callback"
            );
        }
    }
}

#[test]
fn cancellation_deadline_and_memory_stops_are_terminal() {
    let problem = finite_problem();
    let descriptor = descriptor(&problem);
    let token = CancellationToken::new();
    let deadline = Instant::now() + Duration::from_secs(10);
    let boundary = Boundary::new(deadline, &token);
    token.cancel();
    assert!(!boundary.open());
    token.reset();
    assert!(
        boundary.finish(Some(())).is_err(),
        "an observed reset cannot revive the attempt"
    );
    assert!(descriptor
        .materialize_until(Instant::now(), &token)
        .is_err());
    {
        let _memory = Budget::capture(Some(0), None).install();
        assert!(descriptor.materialize_until(deadline, &token).is_err());
    }
    {
        let outer = CancellationToken::new();
        let _lane = crate::smt::ScopedLaneCancellation::install(outer.clone(), None);
        outer.cancel();
        assert!(descriptor.materialize_until(deadline, &token).is_err());
        outer.reset();
    }
    assert!(descriptor
        .materialize_until(deadline, &token)
        .unwrap()
        .is_some());
}

fn malformed_scalar_expressions() -> Vec<ChcExpr> {
    use crate::ChcOp;
    let raw = |op, arguments: Vec<ChcExpr>| {
        ChcExpr::Op(op, arguments.into_iter().map(std::sync::Arc::new).collect())
    };
    vec![
        raw(ChcOp::BvAdd, vec![]),
        raw(ChcOp::BvConcat, vec![ChcExpr::BitVec(0, 2)]),
        raw(
            ChcOp::BvConcat,
            vec![ChcExpr::Bool(true), ChcExpr::BitVec(0, 2)],
        ),
        raw(ChcOp::BvZeroExtend(1), vec![ChcExpr::Bool(true)]),
        raw(ChcOp::BvSignExtend(1), vec![]),
        raw(ChcOp::BvRepeat(2), vec![ChcExpr::Bool(true)]),
        raw(ChcOp::BvRepeat(0), vec![ChcExpr::BitVec(0, 2)]),
        raw(ChcOp::BvRotateLeft(1), vec![]),
        raw(ChcOp::BvExtract(0, 1), vec![ChcExpr::BitVec(0, 2)]),
        raw(ChcOp::Int2Bv(0), vec![ChcExpr::Int(0)]),
        ChcExpr::Real(1, 0),
    ]
}

#[test]
fn malformed_scalar_operators_decline_before_sorting_in_every_position() {
    let base = finite_problem();
    let source = descriptor(&base);
    let formals = candidate(&base)
        .get(&source.predicate.id)
        .unwrap()
        .vars
        .clone();
    for expression in malformed_scalar_expressions() {
        for position in 0..3 {
            let mut problem = base.clone();
            match position {
                0 => {
                    problem.clauses_mut()[0].body.constraint =
                        Some(ChcExpr::eq(expression.clone(), expression.clone()))
                }
                1 => {
                    let ClauseHead::Predicate(_, args) = &mut problem.clauses_mut()[0].head else {
                        panic!("fact");
                    };
                    args[0] = expression.clone();
                }
                _ => problem.clauses_mut()[2].body.predicates[0].1[0] = expression.clone(),
            }
            // This same ordered checker also checks normalized definitions.
            assert!(
                bounded_live_scalar_types(&problem, &|| true).is_none(),
                "{expression:?} at position {position}"
            );
            assert!(capture(&problem, &|| true).is_none());
        }
        let interpretation = PredicateInterpretation::new(
            formals.clone(),
            ChcExpr::eq(expression.clone(), expression),
        );
        assert!(!closed_and_typed(
            &interpretation,
            &source.predicate,
            &|| true
        ));
    }
}

#[test]
fn strict_typing_precedes_scalar_width_cap_without_losing_boundary_values() {
    for (width, accepted) in [(256, true), (257, false)] {
        let mut problem = finite_problem();
        let wide = ChcExpr::Op(
            crate::ChcOp::BvZeroExtend(width - 2),
            vec![std::sync::Arc::new(ChcExpr::BitVec(0, 2))],
        );
        problem.clauses_mut()[0].body.constraint = Some(ChcExpr::eq(wide.clone(), wide));
        assert!(problem
            .validate_live_background_theory_expressions()
            .is_ok());
        assert_eq!(capture(&problem, &|| true).is_some(), accepted);
    }
    let mut real = finite_problem();
    real.clauses_mut()[0].body.constraint =
        Some(ChcExpr::eq(ChcExpr::Real(1, 2), ChcExpr::Real(1, 2)));
    assert!(capture(&real, &|| true).is_some());
}

#[test]
fn structural_census_bounds_already_pending_siblings() {
    let leaf = std::sync::Arc::new(ChcExpr::Bool(true));
    let inner = std::sync::Arc::new(ChcExpr::Op(crate::ChcOp::And, vec![leaf.clone(); 4]));
    let root = ChcExpr::Op(crate::ChcOp::And, vec![leaf.clone(), leaf, inner]);
    let calls = Cell::new(0usize);
    let poll = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(census(&root, &mut 6, None, &poll).is_none());
    assert_eq!(
        calls.get(),
        2,
        "reject before pushing children alongside pending siblings"
    );
    assert!(census(&root, &mut 8, None, &|| true).is_some());
}

#[test]
fn unused_datatype_declarations_decline_without_traversing_metadata() {
    let mut problem = finite_problem();
    problem.add_datatype_def("Unused".into(), vec![("unused".into(), vec![])]);
    assert!(bounded_live_scalar_types(&problem, &|| true).is_none());
    assert!(capture(&problem, &|| true).is_none());
}
