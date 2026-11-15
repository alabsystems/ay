// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

fn controlled_compile(solver: &BmcSolver, refusal: usize) -> (Option<Compiled>, usize) {
    let calls = Cell::new(0usize);
    let armed = Cell::new(false);
    let mut progress = || {
        if !armed.get() {
            return true;
        }
        calls.set(calls.get() + 1);
        calls.get() != refusal
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut progress).unwrap();
    armed.set(true);
    let result = compile(solver, &mut names);
    assert_eq!(names.stopped(), result.is_none());
    if result.is_none() {
        let stopped_at = calls.get();
        // Even after earlier rules were compiled, the real polynomial worker
        // cannot turn this refusal into an executor or level-flat retry.
        let queries: Vec<_> = solver.problem.queries().collect();
        assert!(matches!(
            solver.solve_acyclic_polynomial_dag_once(
                &queries,
                2,
                &solver.defs_by_head(),
                &mut names,
            ),
            ChcEngineResult::Unknown,
        ));
        assert!(!solver.stats.borrow().exhausted_search);
        assert!(!solver.stats.borrow().used_legacy_fallback);
        assert!(!solver.stats.borrow().budget_exhausted);
        assert_eq!(calls.get(), stopped_at);
    }
    (result, calls.get())
}

#[test]
fn every_compiler_square_callback_refusal_is_terminal_and_fresh_retry_is_identical() {
    for site in [SecondSquare::Rule, SecondSquare::Query] {
        let solver = fixture(site, 4);
        let source = format!("{:?}", solver.problem.clauses());
        let (expected, calls) = controlled_compile(&solver, usize::MAX);
        let expected = expected.unwrap();
        assert!((10..20_000).contains(&calls));
        for ordinal in 1..=calls {
            let (result, observed) = controlled_compile(&solver, ordinal);
            assert!(result.is_none(), "refusal {ordinal}/{calls}");
            assert_eq!(observed, ordinal);
        }
        assert_eq!(format!("{:?}", solver.problem.clauses()), source);
        let (retry, _) = controlled_compile(&solver, usize::MAX);
        assert_eq!(retry.unwrap().expression, expected.expression);
    }
}

#[test]
fn cancelled_polynomial_entry_neither_runs_solver_work_nor_reports_infeasibility() {
    let solver = fixture(SecondSquare::Rule, 4);
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut progress = || {
        calls.set(calls.get() + 1);
        !armed.replace(false)
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut progress).unwrap();
    let queries: Vec<_> = solver.problem.queries().collect();
    let definitions = solver.defs_by_head();
    armed.set(true);
    assert!(matches!(
        solver.solve_acyclic_polynomial_dag_once(&queries, 2, &definitions, &mut names,),
        ChcEngineResult::Unknown
    ));
    let stopped_at = calls.get();
    assert!(matches!(
        solver.solve_acyclic_polynomial_dag_once(&queries, 2, &definitions, &mut names,),
        ChcEngineResult::Unknown
    ));
    assert_eq!(calls.get(), stopped_at);
    assert!(names.stopped());
    assert!(!solver.stats.borrow().exhausted_search);
    assert!(!solver.stats.borrow().used_legacy_fallback);
    assert!(!solver.stats.borrow().budget_exhausted);
}
