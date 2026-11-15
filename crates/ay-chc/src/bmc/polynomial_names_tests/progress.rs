// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::CancellationToken;

fn compile_with_parent_cancellation(cancel_at: usize) -> (Option<ChcExpr>, usize) {
    let parent = CancellationToken::new();
    let mut solver = fixture(Some(STEMS[4]));
    solver.config.base.cancellation_token = Some(parent.child());
    let original = format!("{:?}", solver.problem);
    let deadline = ay_core::time::Instant::now() + Duration::from_secs(60);
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut keep_going = || {
        if armed.get() {
            calls.set(calls.get() + 1);
            if calls.get() == cancel_at {
                parent.cancel();
            }
        }
        !solver.dag_deadline_expired(deadline)
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut keep_going).unwrap();
    assert!(!parent.is_cancelled());
    armed.set(true);
    // This helper invokes both actual polynomial definition/query compilers.
    let result = compile(&solver, &mut names);
    if result.is_none() {
        assert!(parent.is_cancelled());
        assert!(solver.config.base.is_cancelled());
        assert!(names.stopped());
        assert_eq!(calls.get(), cancel_at);
        assert!(!solver.stats().exhausted_search);
        parent.reset();
        assert!(names.poll().is_none());
        assert!(compile(&solver, &mut names).is_none());
        assert_eq!(calls.get(), cancel_at, "no resumed or partial formula");
    } else {
        assert!(!parent.is_cancelled());
        assert!(!names.stopped());
    }
    assert_eq!(format!("{:?}", solver.problem), original);
    (result, calls.get())
}

#[test]
fn configured_parent_cancellation_drains_polynomial_encoding_and_retry_is_exact() {
    // Token cancellation occurs inside compilation, after source admission.
    // This measures cooperative polls, not a wall-time drain guarantee.
    let baseline = compile_with_parent_cancellation(usize::MAX);
    assert!(baseline.0.is_some());
    assert!((20..5_000).contains(&baseline.1));
    for cancel_at in 1..=baseline.1 {
        let (result, calls) = compile_with_parent_cancellation(cancel_at);
        assert!(result.is_none(), "encoding poll {cancel_at}/{}", baseline.1);
        assert_eq!(calls, cancel_at);
    }
    assert_eq!(compile_with_parent_cancellation(usize::MAX), baseline);
}

fn count_witness_polls(solver: &BmcSolver) -> usize {
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut live = || {
        if armed.get() {
            calls.set(calls.get() + 1);
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let _ = compile(solver, &mut names).unwrap();
    let model = model(solver, &mut names);
    armed.set(true);
    assert!(witness(solver, &model, &mut names).is_some());
    calls.get()
}

#[test]
fn every_witness_poll_including_final_publication_is_terminal_and_retry_is_fresh() {
    let mut solver = fixture(None);
    solver.problem.declare_predicate(STEMS[2], Vec::new());
    let before = format!("{:?}", solver.problem.clauses());
    let total = count_witness_polls(&solver);
    assert!(total > 20 && total < 2_000);
    for stop in 1..=total {
        let armed = Cell::new(false);
        let calls = Cell::new(0);
        let mut live = || {
            if !armed.get() {
                return true;
            }
            calls.set(calls.get() + 1);
            calls.get() != stop
        };
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        let _ = compile(&solver, &mut names).unwrap();
        let model = model(&solver, &mut names);
        armed.set(true);
        assert!(
            witness(&solver, &model, &mut names).is_none(),
            "poll {stop}"
        );
        assert!(names.stopped());
        assert_eq!(calls.get(), stop);
        assert!(witness(&solver, &model, &mut names).is_none());
        assert!(solver
            .dag_predicate(PredicateId::new(0), &mut names)
            .is_none());
        assert_eq!(calls.get(), stop);
    }
    assert_eq!(count_witness_polls(&solver), total);
    assert_eq!(before, format!("{:?}", solver.problem.clauses()));
}

#[test]
fn every_compiler_naming_poll_refuses_without_a_partial_formula() {
    let solver = fixture(Some(STEMS[4]));
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut live = || {
        if armed.get() {
            calls.set(calls.get() + 1);
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    armed.set(true);
    assert!(compile(&solver, &mut names).is_some());
    let total = calls.get();
    assert!(total > 20 && total < 5_000);
    drop(names);
    for stop in 1..=total {
        armed.set(false);
        calls.set(0);
        let mut live = || {
            if !armed.get() {
                return true;
            }
            calls.set(calls.get() + 1);
            calls.get() != stop
        };
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        armed.set(true);
        assert!(compile(&solver, &mut names).is_none(), "poll {stop}");
        assert!(names.stopped());
        assert_eq!(calls.get(), stop);
        assert!(compile(&solver, &mut names).is_none());
        assert_eq!(calls.get(), stop);
    }
}

#[test]
fn a_caught_witness_callback_panic_cannot_resume_via_the_query_fallback() {
    let solver = fixture(None);
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut live = || {
        if armed.get() {
            calls.set(calls.get() + 1);
            panic!("witness poll");
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
    let model = model(&solver, &mut names);
    armed.set(true);
    let panic = std::panic::catch_unwind(AssertUnwindSafe(|| witness(&solver, &model, &mut names)));
    assert!(panic.is_err());
    assert!(names.stopped());
    armed.set(false);
    assert!(witness(&solver, &model, &mut names).is_none());
    assert_eq!(calls.get(), 1);
}

#[test]
fn refusal_inside_a_recursive_premise_cannot_retry_an_alternative_rule() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", Vec::new());
    let q = problem.declare_predicate("Q", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), None),
        ClauseHead::Predicate(p, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, Vec::new())]),
        ClauseHead::Predicate(q, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), None),
        ClauseHead::Predicate(q, Vec::new()),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        q,
        Vec::new(),
    )])));
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let model = [
        "__bmc_poly_p0_reach",
        "__bmc_poly_p0_r0",
        "__bmc_poly_p1_reach",
        "__bmc_poly_p1_r1",
        "__bmc_poly_p1_r2",
    ]
    .into_iter()
    .map(|name| (name.to_owned(), SmtValue::Bool(true)))
    .collect();
    let run = |stop| {
        let armed = Cell::new(false);
        let calls = Cell::new(0);
        let mut live = || {
            if !armed.get() {
                return true;
            }
            calls.set(calls.get() + 1);
            calls.get() != stop
        };
        let mut names = AcyclicNames::new(&solver.problem, &mut live).unwrap();
        armed.set(true);
        let result = witness(&solver, &model, &mut names);
        if stop == 0 {
            let result = result.unwrap();
            assert_eq!(result.entries.len(), 2);
            let root = &result.entries[result.root];
            assert_eq!(root.incoming_clause, Some(1));
            assert_eq!(root.premises.len(), 1);
            assert_eq!(result.entries[root.premises[0]].incoming_clause, Some(0));
        } else {
            assert!(result.is_none(), "recursive poll {stop}");
            assert!(names.stopped());
            assert_eq!(calls.get(), stop);
            assert!(witness(&solver, &model, &mut names).is_none());
            assert_eq!(calls.get(), stop);
        }
        calls.get()
    };
    let total = run(0);
    assert!(total > 20 && total < 2_000);
    for stop in 1..=total {
        run(stop);
    }
    assert_eq!(run(0), total);
}
