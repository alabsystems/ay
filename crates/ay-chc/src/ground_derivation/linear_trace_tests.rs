// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcVar;
use crate::{ChcSort, ClauseBody, HornClause};

/// `P(0)`, `P(x) ∧ y = x + 1 ⇒ P(y)`, `P(x) ∧ x ≥ 3 ⇒ false`.
fn counter_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(y.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
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

/// Real system with a nondeterministic step `d ∈ [0, 1/2]` that only an
/// inequality constrains: `P(0)`, `P(x) ∧ 0 ≤ d ≤ 1/2 ∧ y = x + d ⇒ P(y)`,
/// `P(x) ∧ x ≥ 1 ⇒ false`.
fn real_drift_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Real]);
    let x = ChcVar::new("x", ChcSort::Real);
    let y = ChcVar::new("y", ChcSort::Real);
    let d = ChcVar::new("d", ChcSort::Real);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::Real(0, 1)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and_all(vec![
                ChcExpr::le(ChcExpr::Real(0, 1), ChcExpr::var(d.clone())),
                ChcExpr::le(ChcExpr::var(d.clone()), ChcExpr::Real(1, 2)),
                ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(d)),
                ),
            ])),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(y)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::Real(1, 1))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn int_states(values: &[Option<i128>]) -> Vec<Vec<Option<SmtValue>>> {
    values
        .iter()
        .map(|value| vec![value.map(SmtValue::Int)])
        .collect()
}

fn real(n: i64, d: i64) -> SmtValue {
    SmtValue::Real(BigRational::new(n.into(), d.into()))
}

fn trace(problem: &ChcProblem, states: Vec<Vec<Option<SmtValue>>>) -> LinearTrace {
    LinearTrace {
        predicate: problem.predicates()[0].id,
        edges: vec![TraceEdgeHint::default(); states.len() + 1],
        states,
    }
}

#[test]
fn full_int_trace_yields_a_validated_derivation_and_witness() {
    let problem = counter_problem();
    let trace = trace(&problem, int_states(&[Some(0), Some(1), Some(2), Some(3)]));
    let cex = counterexample_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
        .expect("a genuine trace must ground-validate");
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("ground derivation attached");
    assert_eq!(derivation.len(), 5, "fact + 3 transitions + query");
    assert_eq!(derivation.steps[0].clause_index, 0);
    assert_eq!(derivation.steps[4].clause_index, 2);
    validate_ground_derivation(&problem, derivation).expect("re-validates");
    assert_eq!(cex.steps.len(), 4);
    let witness = cex.witness.as_ref().expect("Int states give a witness");
    assert_eq!(witness.entries.len(), 4);
    assert_eq!(witness.query_clause, Some(2));
    assert_eq!(witness.entries[0].level, 3);
    assert_eq!(witness.entries[3].incoming_clause, Some(0));
}

#[test]
fn silent_model_values_are_recovered_by_forward_chaining() {
    let problem = counter_problem();
    let trace = trace(&problem, int_states(&[None, None, Some(2), None]));
    assert!(
        ground_derivation_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
            .is_some()
    );
}

#[test]
fn trace_that_does_not_reach_the_query_is_refused() {
    let problem = counter_problem();
    let trace = trace(&problem, int_states(&[Some(0), Some(1), Some(2)]));
    assert!(
        ground_derivation_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
            .is_none()
    );
}

#[test]
fn wrong_state_claims_cannot_forge_a_derivation() {
    // The model claims 0 -> 5 -> 6: not a path of `y = x + 1`. Forward
    // chaining follows the clauses (0 -> 1 -> 2) and the query `x >= 3`
    // then fails on the true final state.
    let problem = counter_problem();
    let trace = trace(&problem, int_states(&[Some(0), Some(5), Some(6)]));
    assert!(
        ground_derivation_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
            .is_none()
    );
}

#[test]
fn real_trace_with_model_locals_validates() {
    let problem = real_drift_problem();
    let mut trace = trace(
        &problem,
        vec![
            vec![Some(real(0, 1))],
            vec![Some(real(1, 2))],
            vec![Some(real(1, 1))],
        ],
    );
    for edge in 1..=2 {
        trace.edges[edge].clause = Some(1);
        trace.edges[edge]
            .clause_values
            .insert("d".to_string(), real(1, 2));
    }
    let cex = counterexample_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
        .expect("Real trace with its locals validates");
    let derivation = cex.ground_derivation.as_ref().expect("derivation");
    assert_eq!(derivation.steps[1].env.get("d"), Some(&real(1, 2)));
    assert!(cex.witness.is_some(), "i64 rationals are spellable");
}

#[test]
fn real_trace_without_locals_is_completed_from_the_states() {
    // `y = x + d` determines `d` once both states are pinned.
    let problem = real_drift_problem();
    let trace = trace(
        &problem,
        vec![
            vec![Some(real(0, 1))],
            vec![Some(real(1, 2))],
            vec![Some(real(1, 1))],
        ],
    );
    assert!(
        ground_derivation_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
            .is_some()
    );
}

#[test]
fn a_hint_for_the_wrong_role_is_ignored() {
    let problem = counter_problem();
    let mut trace = trace(&problem, int_states(&[Some(0), Some(1), Some(2), Some(3)]));
    // Edge 0 is the fact edge; clause 1 is a transition.
    trace.edges[0].clause = Some(1);
    assert!(
        ground_derivation_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
            .is_some()
    );
}

#[test]
fn cancellation_stops_the_build() {
    let problem = counter_problem();
    let trace = trace(&problem, int_states(&[Some(0), Some(1), Some(2), Some(3)]));
    let token = CancellationToken::new();
    token.cancel();
    assert!(ground_derivation_from_linear_trace(&problem, &trace, None, &token).is_none());
}

#[test]
fn real_head_term_evaluates_along_the_trace() {
    // `P(0)`, `P(x) ⇒ P(x + 1/2)`, `P(x) ∧ x ≥ 1 ⇒ false`: the head argument
    // is a Real arithmetic term, not a variable.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Real]);
    let x = ChcVar::new("x", ChcSort::Real);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::Real(0, 1)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::add(ChcExpr::Real(1, 2), ChcExpr::var(x.clone()))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::Real(1, 1))),
        ),
        ClauseHead::False,
    ));
    let states = vec![vec![Some(real(0, 1))], vec![Some(real(1, 2))], vec![None]];
    let trace = trace(&problem, states);
    let derivation =
        ground_derivation_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
            .expect("the Real head term evaluates at every step");
    assert_eq!(derivation.steps.len(), 4);
}

#[test]
fn recursive_datatype_values_nested_past_the_sort_snapshot_validate() {
    // The parser cuts `Nat`'s recursion after one unfolding, so `zero` inside
    // `succ(succ(zero))` is checked against an uninterpreted `Nat` placeholder.
    let problem = crate::ChcParser::parse(
        "(set-logic HORN)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun P (Nat) Bool)
(assert (forall ((n Nat)) (=> (= n zero) (P n))))
(assert (forall ((n Nat) (m Nat)) (=> (and (P n) (= m (succ n))) (P m))))
(assert (forall ((n Nat)) (=> (and (P n) (= n (succ (succ zero)))) false)))
(check-sat)",
    )
    .expect("fixture parses");
    let nat = |depth: usize| {
        (0..depth).fold(
            SmtValue::Datatype("zero".to_string(), Vec::new()),
            |inner, _| SmtValue::Datatype("succ".to_string(), vec![inner]),
        )
    };
    let states = (0..3).map(|depth| vec![Some(nat(depth))]).collect();
    let trace = trace(&problem, states);
    assert!(
        ground_derivation_from_linear_trace(&problem, &trace, None, &CancellationToken::new())
            .is_some(),
        "succ(succ(zero)) is a Nat"
    );
}
