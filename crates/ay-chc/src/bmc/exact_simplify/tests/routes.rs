// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::bmc::BmcConfig;
use crate::{CancellationToken, ChcEngineResult, ClauseBody, ClauseHead, HornClause};
use std::time::Duration;

#[derive(Clone, Copy)]
enum Route {
    Symbolic,
    Direct,
    Streaming,
}

fn problem(nonlinear: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, Vec::new()),
    ));
    let mut premises = vec![(p, Vec::new())];
    if nonlinear {
        let q = problem.declare_predicate("Q", Vec::new());
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(q, Vec::new()),
        ));
        premises.push((q, Vec::new()));
    }
    problem.add_clause(HornClause::new(
        ClauseBody::new(premises, Some(ChcExpr::and_all(contradictory_bounds()))),
        ClauseHead::False,
    ));
    problem
}

fn run(route: Route, refusal: usize) -> (bool, usize) {
    let problem = problem(matches!(route, Route::Direct));
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let armed = Cell::new(false);
    let calls = Cell::new(0usize);
    let mut keep_going = || {
        if !armed.get() {
            return true;
        }
        calls.set(calls.get() + 1);
        calls.get() != refusal
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut keep_going).unwrap();
    let start = ay_core::time::Instant::now();
    let deadline = start + Duration::from_secs(60);
    armed.set(true);
    let definitive = encode(&solver, route, start, deadline, &mut names).is_some();
    assert_eq!(names.stopped(), !definitive);
    (definitive, calls.get())
}

fn encode(
    solver: &BmcSolver,
    route: Route,
    start: ay_core::time::Instant,
    deadline: ay_core::time::Instant,
    names: &mut AcyclicNames<'_>,
) -> Option<String> {
    let queries: Vec<_> = solver.problem.queries().collect();
    assert_eq!(queries.len(), 1);
    match route {
        Route::Symbolic => match solver.acyclic_symbolic_query(&queries, names) {
            Some(expression) => {
                assert_eq!(expression, ChcExpr::Bool(false));
                Some(format!("{expression:?}"))
            }
            None => None,
        },
        Route::Direct => {
            match solver.solve_acyclic_safe_first_named(&queries, 2, start, deadline, names) {
                ChcEngineResult::Safe(model) => Some(format!("{model:?}")),
                ChcEngineResult::Unknown => None,
                ChcEngineResult::Unsafe(_) => panic!("contradictory source cannot be Unsafe"),
                ChcEngineResult::NotApplicable => panic!("bounded exact route is applicable"),
            }
        }
        Route::Streaming => match solver.solve_acyclic_safe_first_streaming_once(
            &queries,
            2,
            &solver.defs_by_head(),
            deadline,
            start,
            names,
        ) {
            Some(ChcEngineResult::Safe(model)) => Some(format!("{model:?}")),
            None | Some(ChcEngineResult::Unknown) => None,
            Some(ChcEngineResult::Unsafe(_)) => panic!("contradictory source cannot be Unsafe"),
            Some(ChcEngineResult::NotApplicable) => panic!("linear exact route is applicable"),
        },
    }
}

fn token_attempt(route: Route, cancel_at: usize) -> (Option<String>, usize) {
    let parent = CancellationToken::new();
    let solver = BmcSolver::new(
        problem(matches!(route, Route::Direct)),
        BmcConfig::default().with_cancellation(parent.child()),
    );
    let original = format!("{:?}", solver.problem);
    let start = ay_core::time::Instant::now();
    let deadline = start + Duration::from_secs(60);
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut keep_going = || {
        if armed.get() {
            calls.set(calls.get() + 1);
            if calls.get() == cancel_at {
                parent.cancel();
            }
        }
        // The actual production predicate observes the configured child.
        !solver.dag_deadline_expired(deadline)
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut keep_going).unwrap();
    assert!(!parent.is_cancelled());
    armed.set(true); // Do not cancel the initial source census.
    let result = encode(&solver, route, start, deadline, &mut names);
    if result.is_none() {
        assert!(parent.is_cancelled());
        assert!(solver.config.base.is_cancelled());
        assert!(names.stopped());
        assert_eq!(calls.get(), cancel_at);
        assert!(!solver.stats().exhausted_search);
        parent.reset();
        assert!(names.poll().is_none());
        assert!(encode(&solver, route, start, deadline, &mut names).is_none());
        assert_eq!(calls.get(), cancel_at, "the old attempt cannot resume");
    } else {
        assert!(!parent.is_cancelled());
        assert!(!names.stopped());
    }
    assert_eq!(format!("{:?}", solver.problem), original);
    (result, calls.get())
}

#[test]
fn configured_parent_cancellation_drains_real_encoding_polls_and_retry_is_fresh() {
    // These source contradictions finish before SMT. Count cooperative work,
    // not elapsed time or uninterruptible per-expression clone/render work.
    for route in [Route::Symbolic, Route::Direct, Route::Streaming] {
        let baseline = token_attempt(route, usize::MAX);
        assert!(baseline.0.is_some());
        assert!((2..5_000).contains(&baseline.1));
        for cancel_at in 1..=baseline.1 {
            let (result, calls) = token_attempt(route, cancel_at);
            assert!(result.is_none(), "encoding poll {cancel_at}/{}", baseline.1);
            assert_eq!(calls, cancel_at);
        }
        assert_eq!(token_attempt(route, usize::MAX), baseline);
    }
}

#[test]
fn actual_symbolic_direct_and_streaming_false_paths_refuse_every_cancelled_prefix() {
    // Interval contradiction is established before any SMT context/check call.
    for route in [Route::Symbolic, Route::Direct, Route::Streaming] {
        let (definitive, calls) = run(route, usize::MAX);
        assert!(definitive);
        assert!(calls > 0);
        for refusal in 1..=calls {
            let (definitive, observed) = run(route, refusal);
            assert!(!definitive, "refusal {refusal}/{calls}");
            assert_eq!(observed, refusal);
        }
        assert!(run(route, usize::MAX).0);
    }
}

#[test]
fn nonlinear_fixture_cannot_be_discharged_by_the_streaming_route() {
    let solver = BmcSolver::new(problem(true), BmcConfig::default());
    let queries: Vec<_> = solver.problem.queries().collect();
    let mut keep_going = || true;
    let mut names = AcyclicNames::new(&solver.problem, &mut keep_going).unwrap();
    let start = ay_core::time::Instant::now();
    assert!(solver
        .solve_acyclic_safe_first_streaming_once(
            &queries,
            2,
            &solver.defs_by_head(),
            start + Duration::from_secs(60),
            start,
            &mut names,
        )
        .is_none());
    assert!(!names.stopped());
}
