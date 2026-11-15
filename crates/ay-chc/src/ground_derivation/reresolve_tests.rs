// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ground_derivation::linear_trace::{LinearTrace, TraceEdgeHint};
use crate::{CancellationToken, ChcSort, ChcVar, ClauseBody};

/// `P(0)`, `P(x) ∧ (y = x + 1 ∨ y = x + 2) ⇒ P(y)`, `P(x) ∧ x ≥ 3 ⇒ false`;
/// `step_two: false` drops the `x + 2` disjunct.
fn problem(step_two: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let step = |k: i64| {
        ChcExpr::eq(
            ChcExpr::var(y.clone()),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(k)),
        )
    };
    let transition = if step_two {
        ChcExpr::or(step(1), step(2))
    } else {
        step(1)
    };
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], Some(transition)),
        ClauseHead::Predicate(p, vec![ChcExpr::var(y)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// A derivation over the OR-split problem that takes the `x + 2` branch twice
/// (`P(0) → P(2) → P(4) → false`).
fn split_derivation() -> (ChcProblem, GroundDerivation) {
    let mut split = problem(true);
    split.try_split_ors_in_clauses(8, false);
    assert!(split.clauses().len() > 3, "the transition is split");
    let states = [0, 2, 4]
        .iter()
        .map(|v| vec![Some(SmtValue::Int(*v))])
        .collect::<Vec<_>>();
    let trace = LinearTrace {
        predicate: split.predicates()[0].id,
        edges: vec![TraceEdgeHint::default(); states.len() + 1],
        states,
    };
    let derivation = super::super::linear_trace::ground_derivation_from_linear_trace(
        &split,
        &trace,
        None,
        &CancellationToken::new(),
    )
    .expect("the trace validates on the split problem");
    (split, derivation)
}

#[test]
fn a_split_derivation_is_reattributed_to_the_source_clauses() {
    let (split, derivation) = split_derivation();
    let original = problem(true);
    let reresolved = reresolve_ground_derivation(&derivation, &split, &original)
        .expect("each split instance is an instance of its source clause");
    assert_eq!(reresolved.steps.len(), derivation.steps.len());
    assert!(reresolved
        .steps
        .iter()
        .all(|step| step.clause_index < original.clauses().len()));
}

#[test]
fn a_step_the_target_clauses_do_not_admit_is_refused() {
    let (split, derivation) = split_derivation();
    // Without the `x + 2` disjunct no target clause derives `P(2)` from `P(0)`.
    assert!(reresolve_ground_derivation(&derivation, &split, &problem(false)).is_none());
}

#[test]
fn accepting_original_progress_preserves_the_reattributed_derivation() {
    let (split, derivation) = split_derivation();
    let original = problem(true);
    let mut calls = 0;
    let mapped =
        reresolve_ground_derivation_with_progress(&derivation, &split, &original, &mut || {
            calls += 1;
            true
        })
        .unwrap()
        .unwrap();
    assert!(calls > derivation.steps.len());
    assert_eq!(mapped.query_step, derivation.query_step);
    assert_eq!(
        mapped
            .steps
            .iter()
            .map(|step| step.clause_index)
            .collect::<Vec<_>>(),
        vec![0, 1, 1, 2]
    );
    for (source, target) in derivation.steps.iter().zip(&mapped.steps) {
        assert_eq!(source.premises, target.premises);
    }
    assert_eq!(
        crate::ground_derivation::validate_ground_derivation(&original, &mapped),
        Ok(())
    );
}

#[test]
fn every_original_progress_refusal_is_terminal_not_a_missing_mapping() {
    let (split, derivation) = split_derivation();
    let original = problem(true);
    let mut total = 0;
    assert!(
        reresolve_ground_derivation_with_progress(&derivation, &split, &original, &mut || {
            total += 1;
            true
        },)
        .unwrap()
        .is_some()
    );
    for stop in 1..=total {
        let mut calls = 0;
        let result =
            reresolve_ground_derivation_with_progress(&derivation, &split, &original, &mut || {
                calls += 1;
                calls != stop
            });
        assert!(
            matches!(result, Err(GroundDerivationError::Interrupted)),
            "stop={stop}"
        );
        assert_eq!(calls, stop, "a refused owner must not be asked to resume");
    }
}

#[test]
fn rejected_mapping_keeps_semantic_none_but_still_observes_terminal_refusal() {
    let (split, derivation) = split_derivation();
    let rejecting = problem(false);
    let mut total = 0;
    assert!(reresolve_ground_derivation_with_progress(
        &derivation,
        &split,
        &rejecting,
        &mut || {
            total += 1;
            true
        },
    )
    .unwrap()
    .is_none());
    let mut calls = 0;
    let result =
        reresolve_ground_derivation_with_progress(&derivation, &split, &rejecting, &mut || {
            calls += 1;
            calls < total
        });
    assert!(matches!(result, Err(GroundDerivationError::Interrupted)));
    assert_eq!(calls, total);
}
