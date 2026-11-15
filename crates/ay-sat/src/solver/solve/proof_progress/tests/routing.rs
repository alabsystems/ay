// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::tla_traceable::TlaTraceable;
use std::rc::Rc;

#[derive(Clone, Copy)]
enum Route {
    Startup,
    Search,
}

struct Fixture {
    solver: Solver,
    clauses: Vec<Vec<Literal>>,
    num_vars: usize,
    trace_dir: Option<tempfile::TempDir>,
}

fn fixture(route: Route, tla: bool) -> Fixture {
    let p = |var| Literal::positive(Variable(var));
    let n = |var| Literal::negative(Variable(var));
    let (num_vars, clauses) = match route {
        // Put both nonunit clauses first: the final units do not contradict
        // each other until startup BCP follows the two-edge implication chain.
        Route::Startup => (
            3,
            vec![vec![n(0), p(1)], vec![n(1), p(2)], vec![p(0)], vec![n(2)]],
        ),
        Route::Search => (
            2,
            vec![
                vec![p(0), p(1)],
                vec![p(0), n(1)],
                vec![n(0), p(1)],
                vec![n(0), n(1)],
            ],
        ),
    };
    let output = ProofOutput::lrat_binary(Vec::new(), clauses.len() as u64);
    let mut solver = Solver::with_proof_output(num_vars, output);
    solver.set_bounded_in_memory_proof_posture();
    let deadline = ay_core::time::Instant::now() + Duration::from_secs(30);
    solver.set_backward_proof_limits(BackwardProofLimits {
        deadline: Some(deadline),
        max_steps: 1_000,
        max_literals: 10_000,
        max_hints: 10_000,
        max_bytes: 1024 * 1024,
    });
    solver.set_solve_deadline(Some(deadline));
    solver.set_conflict_budget(Some(1_000));
    solver.set_decision_budget(Some(1_000));
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    let trace_dir = tla.then(|| tempfile::tempdir().unwrap());
    if let Some(dir) = &trace_dir {
        let path = dir.path().join("proof-routing.jsonl");
        solver.enable_tla_trace(
            path.to_str().unwrap(),
            Solver::tla_module(),
            Solver::tla_variables(),
        );
    }
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    assert!(
        !solver.has_empty_clause,
        "fixture must reach actual startup/search finalization"
    );
    Fixture {
        solver,
        clauses,
        num_vars,
        trace_dir,
    }
}

fn run(fixture: &mut Fixture, route: Route, progress: ProofProgress<'_>) -> SatResult {
    let initial = match progress {
        Some(_) => fixture.solver.init_solve_with_proof_progress(progress),
        None => fixture.solver.init_solve(),
    };
    match route {
        Route::Startup => initial.expect("startup BCP must discover this contradiction"),
        Route::Search => {
            assert!(initial.is_none(), "grid must require a decision");
            match progress {
                Some(_) => fixture
                    .solver
                    .cdcl_loop_pure_with_proof_progress(|| false, progress),
                None => fixture.solver.cdcl_loop_pure(|| false),
            }
        }
    }
}

fn checked_bytes(fixture: &mut Fixture, route: Route) -> Vec<u8> {
    if matches!(route, Route::Search) {
        assert!(fixture.solver.num_decisions() > 0);
    }
    fixture.solver.finish_tla_trace();
    if let Some(dir) = &fixture.trace_dir {
        let trace = std::fs::read_to_string(dir.path().join("proof-routing.jsonl")).unwrap();
        assert!(trace.contains("DeclareUnsat"));
        if matches!(route, Route::Search) {
            assert!(trace.contains("Decide"));
        }
    }
    let bytes = fixture
        .solver
        .take_proof_writer_without_artifact()
        .unwrap()
        .into_inner()
        .unwrap()
        .into_vec()
        .unwrap();
    let steps = ay_lrat_check::lrat_parser::parse_binary_lrat(&bytes).unwrap();
    let mut checker = ay_lrat_check::checker::LratChecker::new(fixture.num_vars);
    for (index, clause) in fixture.clauses.iter().enumerate() {
        let literals: Vec<_> = clause
            .iter()
            .map(|literal| ay_lrat_check::dimacs::Literal::from_dimacs(literal.to_dimacs()))
            .collect();
        assert!(checker.add_original(index as u64 + 1, &literals));
    }
    assert!(checker.verify_proof(&steps), "{}", checker.stats_summary());
    bytes
}

fn every_phase_poll(route: Route, tla: bool) {
    let mut legacy = fixture(route, tla);
    assert!(matches!(run(&mut legacy, route, None), SatResult::Unsat(_)));
    let expected = checked_bytes(&mut legacy, route);
    let count = Rc::new(Cell::new(0));
    let mut live = fixture(route, tla);
    assert!(matches!(
        run(
            &mut live,
            route,
            Some(&|| {
                count.set(count.get() + 1);
                true
            })
        ),
        SatResult::Unsat(_)
    ));
    assert_eq!(checked_bytes(&mut live, route), expected);
    assert!(count.get() > 10 && count.get() < 10_000);
    for stop in 1..=count.get() {
        let mut cancelled = fixture(route, tla);
        let calls = Cell::new(0);
        assert!(matches!(
            run(
                &mut cancelled,
                route,
                Some(&|| {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                })
            ),
            SatResult::Unknown
        ));
        assert_eq!(calls.get(), stop);
        assert_eq!(
            cancelled.solver.cold.backward_proof_failure,
            Some(BackwardProofFailure::Cancelled)
        );
        assert_eq!(
            cancelled.solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
        assert!(!cancelled.solver.cold.empty_clause_in_proof);
        assert_eq!(cancelled.solver.cold.empty_clause_lrat_id, None);
    }
    let mut retry = fixture(route, tla);
    assert!(matches!(
        run(&mut retry, route, Some(&|| true)),
        SatResult::Unsat(_)
    ));
    assert_eq!(checked_bytes(&mut retry, route), expected);
}

#[test]
fn startup_bcp_proof_callbacks_are_reached_with_and_without_tla() {
    for tla in [false, true] {
        every_phase_poll(Route::Startup, tla);
    }
}

#[test]
fn searched_grid_proof_callbacks_are_reached_with_and_without_tla() {
    for tla in [false, true] {
        every_phase_poll(Route::Search, tla);
    }
}
