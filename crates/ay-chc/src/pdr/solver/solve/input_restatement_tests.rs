// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

//! PDR rewrites its input (case splits, nullary-fail expansion) and must hand
//! back counterexamples whose clause indices name the INPUT problem's clauses.
//! Each problem below orders its clauses so that a rewritten index either
//! runs past the input's clause list or names a different input clause.

use super::*;
use crate::pdr::config::PdrConfig;
use crate::pdr::{CexVerificationResult, PdrResult};
use crate::{ChcParser, ChcProblem, ClauseHead};

fn solve(problem: &ChcProblem) -> (PdrSolver, Counterexample) {
    let mut solver = PdrSolver::new(problem.clone(), PdrConfig::default());
    match solver.solve() {
        PdrResult::Unsafe(cex) => (solver, cex),
        other => panic!("expected Unsafe, got {other:?}"),
    }
}

/// Every clause index `cex` carries names a clause of `problem` that fits:
/// a fact's clause derives its predicate from its premises' predicates, the
/// query consumes the root, and steps stay in range. A validator built on
/// `problem` accepts it.
fn assert_names_clauses_of(problem: &ChcProblem, cex: &Counterexample) {
    let clauses = problem.clauses();
    let witness = cex
        .witness
        .as_ref()
        .expect("PDR's counterexample carries its derivation witness");
    for (position, entry) in witness.entries.iter().enumerate() {
        let Some(index) = entry.incoming_clause else {
            continue;
        };
        let clause = clauses.get(index).unwrap_or_else(|| {
            panic!(
                "entry {position}: clause {index} of a {}-clause problem",
                clauses.len()
            )
        });
        assert!(
            matches!(&clause.head, ClauseHead::Predicate(head, _) if *head == entry.predicate),
            "entry {position}: clause {index} does not derive {:?}",
            entry.predicate
        );
        let premises: Vec<_> = entry
            .premises
            .iter()
            .map(|&premise| witness.entries[premise].predicate)
            .collect();
        let body: Vec<_> = clause.body.predicates.iter().map(|(p, _)| *p).collect();
        assert_eq!(premises, body, "entry {position}: clause {index}'s body");
    }
    let query = witness.query_clause.expect("the witness names its query");
    let clause = clauses
        .get(query)
        .unwrap_or_else(|| panic!("query {query} of a {}-clause problem", clauses.len()));
    assert!(clause.is_query(), "clause {query} is not a query");
    let body: Vec<_> = clause.body.predicates.iter().map(|(p, _)| *p).collect();
    assert_eq!(body, vec![witness.entries[witness.root].predicate]);
    for step in &cex.steps {
        if let Some(index) = step.clause_index {
            assert!(index < clauses.len(), "step clause {index}");
        }
    }
    let validation = PdrConfig {
        preserve_original_clauses: true,
        ..PdrConfig::default()
    };
    assert_eq!(
        PdrSolver::new(problem.clone(), validation).verify_counterexample(cex),
        CexVerificationResult::Valid
    );
}

#[test]
fn or_split_counterexample_names_the_input_clauses() {
    // Split: query, step+2, step+1, fact (the OR driver pops its cases). The
    // fact's split index (3) is past the input's three clauses, and step+1's
    // (2) names the input's fact.
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (and (inv x) (>= x 5)) false)))
(assert (forall ((x Int) (y Int)) (=> (and (inv x) (or (= y (+ x 1)) (= y (+ x 2)))) (inv y))))
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(check-sat)
"#,
    )
    .unwrap();
    let (solver, cex) = solve(&problem);
    assert!(
        solver.case_split_origins.is_some(),
        "the problem must be case split"
    );
    assert_names_clauses_of(&problem, &cex);
}

#[test]
fn ite_split_counterexample_names_the_input_clauses() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (and (inv x) (>= x 7)) false)))
(assert (forall ((x Int) (y Int)) (=> (and (inv x) (= y (ite (< x 3) (+ x 1) (+ x 2)))) (inv y))))
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(check-sat)
"#,
    )
    .unwrap();
    let (solver, cex) = solve(&problem);
    assert!(
        solver.case_split_origins.is_some(),
        "the problem must be case split"
    );
    assert_names_clauses_of(&problem, &cex);
}

#[test]
fn nullary_fail_counterexample_routes_through_fail() {
    // The expansion drops `inv ∧ x ≥ 5 ⇒ fail` and `fail ⇒ false` (input
    // clauses 0 and 1) and appends the query `inv ∧ x ≥ 5 ⇒ false`: every
    // kept clause moves down two, and the query has no input counterpart.
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(declare-fun fail () Bool)
(assert (forall ((x Int)) (=> (and (inv x) (>= x 5)) fail)))
(assert (=> fail false))
(assert (forall ((x Int) (y Int)) (=> (and (inv x) (= y (+ x 1))) (inv y))))
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(check-sat)
"#,
    )
    .unwrap();
    let (solver, cex) = solve(&problem);
    assert!(
        solver.nullary_expansion.is_some(),
        "the problem must be nullary-expanded"
    );
    assert_names_clauses_of(&problem, &cex);
    let witness = cex.witness.as_ref().unwrap();
    assert_eq!(witness.query_clause, Some(1));
    assert_eq!(witness.entries[witness.root].incoming_clause, Some(0));
}

/// `fail` is reachable, but `fail ∧ 2z = 1 ⇒ false` never fires: no integer
/// has 2z = 1, so the problem is SAFE. Expanding the query into
/// `inv ∧ x ≥ 5 ⇒ false` drops that constraint and makes it unsafe.
fn constrained_nullary_fail_problem() -> ChcProblem {
    ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(declare-fun fail () Bool)
(assert (forall ((x Int)) (=> (and (inv x) (>= x 5)) fail)))
(assert (forall ((z Int)) (=> (and fail (= (* 2 z) 1)) false)))
(assert (forall ((x Int) (y Int)) (=> (and (inv x) (= y (+ x 1))) (inv y))))
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(check-sat)
"#,
    )
    .unwrap()
}

#[test]
fn a_constrained_nullary_fail_query_is_not_expanded_away() {
    let mut solver = PdrSolver::new(constrained_nullary_fail_problem(), PdrConfig::default());
    let result = solver.solve();
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "a safe problem answered Unsafe"
    );
    assert!(solver.nullary_expansion.is_none());
}

#[test]
fn split_origins_compose_and_drop_the_identity() {
    // ORs then ites: [0, 0, 1, 2] after [0, 1, 1] is [0, 0, 1, 1].
    assert_eq!(
        PdrSolver::compose_case_split_origins(Some(vec![0, 1, 1]), vec![0, 0, 1, 2]),
        Some(vec![0, 0, 1, 1])
    );
    assert_eq!(
        PdrSolver::compose_case_split_origins(None, vec![0, 1, 2]),
        None
    );
    assert_eq!(
        PdrSolver::compose_case_split_origins(Some(vec![0, 0, 1]), vec![0, 1, 2]),
        Some(vec![0, 0, 1])
    );
}
