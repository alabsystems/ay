// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use std::cell::Cell;

fn named_expansion(problem: &ChcProblem, progress: &mut dyn FnMut() -> bool) -> Option<ChcExpr> {
    let mut names = AcyclicNames::new(problem, progress)?;
    let clause = &problem.clauses()[0];
    let substitutions = names.instance_vars(clause)?;
    names.substitute(clause.body.constraint.as_ref()?, &substitutions)
}

#[test]
fn every_naming_and_substitution_poll_refuses_then_fresh_retry_succeeds() {
    let (problem, _) = collision_problem("__bmc_dag_e0_v0");
    let mut total = 0;
    let expected = named_expansion(&problem, &mut || {
        total += 1;
        true
    })
    .unwrap();
    assert!((10..2000).contains(&total));
    for ordinal in 1..=total {
        let mut calls = 0;
        let actual = named_expansion(&problem, &mut || {
            calls += 1;
            calls != ordinal
        });
        assert!(actual.is_none(), "refusal at {ordinal}/{total}");
        assert_eq!(calls, ordinal);
    }
    assert_eq!(named_expansion(&problem, &mut || true), Some(expected));
}

#[test]
fn once_false_or_caught_callback_panic_cannot_resume_same_names() {
    let (problem, _) = collision_problem("z");
    let should_stop = Cell::new(false);
    let calls = Cell::new(0);
    let mut progress = || {
        calls.set(calls.get() + 1);
        !should_stop.get()
    };
    let mut names = AcyclicNames::new(&problem, &mut progress).unwrap();
    should_stop.set(true);
    assert!(names.instance().is_none());
    let stopped_calls = calls.get();
    should_stop.set(false);
    assert!(names.poll().is_none());
    assert_eq!(calls.get(), stopped_calls);

    let panic_now = Cell::new(false);
    let mut progress = || {
        assert!(!panic_now.get(), "naming callback panic");
        true
    };
    let mut names = AcyclicNames::new(&problem, &mut progress).unwrap();
    panic_now.set(true);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| names.poll())).is_err());
    panic_now.set(false);
    assert!(names.poll().is_none());
}

fn nested(mut expression: ChcExpr, edges: usize) -> ChcExpr {
    for _ in 0..edges {
        expression = ChcExpr::Op(ChcOp::Not, vec![Arc::new(expression)]);
    }
    expression
}

#[test]
fn exact_depth_limit_refuses_input_and_expanded_output_without_partial_substitution() {
    let problem = ChcProblem::new();
    let mut live = || true;
    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    let expression = nested(
        ChcExpr::Var(ChcVar::new("b", ChcSort::Bool)),
        crate::expr::MAX_EXPR_RECURSION_DEPTH - 1,
    );
    let mut substitutions = DetHashMap::default();
    substitutions.insert("b".to_owned(), ChcExpr::Bool(true));
    let accepted = names.substitute(&expression, &substitutions).unwrap();
    assert_eq!(accepted.vars(), [] as [ChcVar; 0]);
    substitutions.insert("b".to_owned(), nested(ChcExpr::Bool(true), 1));
    assert!(names.substitute(&expression, &substitutions).is_none());
    assert!(names.stopped());
    ChcExpr::iterative_drop(accepted);
    ChcExpr::iterative_drop(expression);

    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    let too_deep = nested(ChcExpr::Bool(false), crate::expr::MAX_EXPR_RECURSION_DEPTH);
    assert!(names
        .substitute(&too_deep, &DetHashMap::default())
        .is_none());
    assert!(names.stopped());
    ChcExpr::iterative_drop(too_deep);
}

#[test]
fn occurrence_budget_counts_shared_edges_and_all_clause_roots() {
    let shared = Arc::new(variable("x"));
    let expression = ChcExpr::Op(ChcOp::And, vec![Arc::clone(&shared), shared]);
    // Both EDGES to the shared variable are still pushed, polled and charged,
    // so the budget still counts occurrences rather than distinct nodes. What
    // the shared node no longer does is EXPAND twice: its name and sort are
    // enqueued once, not once per incoming edge. Five charges, not seven.
    for (limit, accepted) in [(4, false), (5, true)] {
        let mut live = || true;
        let mut control = Control {
            keep_going: &mut live,
            stopped: false,
        };
        let result =
            Scan::with_limit(&mut control, limit).expression(&expression, &mut |_| Some(()));
        assert_eq!(result.is_some(), accepted);
        assert_eq!(control.stopped, !accepted);
    }
    let clause = HornClause::new(
        ClauseBody::constraint(variable("x")),
        ClauseHead::Predicate(PredicateId::new(0), vec![variable("x")]),
    );
    let mut live = || true;
    let mut control = Control {
        keep_going: &mut live,
        stopped: false,
    };
    assert!(Scan::with_limit(&mut control, 5)
        .clause(&clause, &mut |_| Some(()))
        .is_none());
    assert!(control.stopped);
}

#[test]
fn instance_overflow_and_recursive_expansion_depth_are_terminal() {
    let problem = ChcProblem::new();
    let mut live = || true;
    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    names.next_instance = usize::MAX;
    assert!(names.instance().is_none());
    assert!(names.stopped());
    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    assert!(names
        .recursion(crate::expr::MAX_EXPR_RECURSION_DEPTH - 1)
        .is_some());
    assert!(names
        .recursion(crate::expr::MAX_EXPR_RECURSION_DEPTH)
        .is_none());
    assert!(names.instance().is_none());
}

#[test]
fn a_shared_dag_is_expanded_once_per_node_not_once_per_path() {
    // Thirty shared conjunctions: 31 distinct nodes, but 2^30 paths from the
    // root to the leaf. Expanding per path would charge past the million-node
    // budget and refuse, and `ExactExpansionRefused` is terminal — it returns
    // Unknown from solve() without the legacy fallback the sibling arm takes.
    // So this admission must SUCCEED, and it must do so in work linear in the
    // DAG rather than in its tree unfolding.
    let mut expression = variable("x");
    for _ in 0..30 {
        let shared = Arc::new(expression);
        expression = ChcExpr::Op(ChcOp::And, vec![Arc::clone(&shared), shared]);
    }
    let mut polls = 0usize;
    let mut live = || {
        polls += 1;
        true
    };
    let mut control = Control {
        keep_going: &mut live,
        stopped: false,
    };
    let admitted = Scan::new(&mut control).expression(&expression, &mut |_| Some(()));
    assert!(
        admitted.is_some(),
        "a shared DAG must not exhaust the budget"
    );
    assert!(!control.stopped);
    // Two pushes and one pop per level, plus the leaf's name/sort, is a few
    // hundred polls. The tree unfolding is 2^30 nodes, so any per-path walk
    // cannot land near this bound.
    assert!(
        polls < 1_000,
        "expected DAG-linear admission, polled {polls}"
    );
    ChcExpr::iterative_drop(expression);
}
