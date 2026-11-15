// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sweep honours the solve's own stop: a raised interrupt or an expired
//! deadline ends it before any kitten work. Preprocessing polls them only
//! before and after the pass, so a sweep that ignored them ran on past the
//! caller's budget (a Trust verification query, 2026-10-02).

use super::*;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// A solver holding the FP lane's CNF for a Float(2,3) division miter
/// (`tests/data/fp_div_miter_cone.cnf`), its units propagated and its sweep
/// budget funded.
fn fp_division_miter_solver() -> Solver {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/fp_div_miter_cone.cnf");
    let text = std::fs::read_to_string(&path).expect("read fp_div_miter_cone.cnf");
    let formula = crate::parse_dimacs(&text).expect("parse fp_div_miter_cone.cnf");
    let num_vars = crate::dimacs::max_variable_count(&formula.clauses);
    let mut solver = Solver::new(num_vars);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver.search_ticks = [100_000_000, 0];
    solver
}

fn kitten_environments(solver: &Solver) -> u64 {
    solver.inproc.sweeper.stats().kitten_environments
}

#[test]
fn sweep_honours_a_raised_interrupt() {
    let mut solver = fp_division_miter_solver();
    solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert!(!solver.sweep());
    assert_eq!(kitten_environments(&solver), 0);
    assert_eq!(solver.inproc.sweeper.stats().kitten_solves, 0);

    // Lowered, the same sweep builds environments.
    solver.set_interrupt_handle(None);
    solver.sweep();
    assert!(kitten_environments(&solver) > 0);
}

#[test]
fn sweep_honours_an_expired_solve_deadline() {
    let mut solver = fp_division_miter_solver();
    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));
    assert!(!solver.sweep());
    assert_eq!(kitten_environments(&solver), 0);
    assert_eq!(solver.inproc.sweeper.stats().kitten_solves, 0);
}
