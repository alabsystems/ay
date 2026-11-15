// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The orbitope route honors the solve's stop (2026-09-15, owner): on
//! latin_square_10.15 its detection runs about 130 s, and a stop it cannot see
//! turns a timeout into the watchdog's hard exit. A stop that fires inside the
//! route leaves the formula as it was and records why.

use super::*;
use std::cell::Cell;

/// A 6-colouring of a 40%-dense graph on 120 vertices: an orbitope matrix
/// whose column ordering takes dozens of stop samples.
fn add_dense_colouring(solver: &mut Solver) {
    let var = |vertex: u32, colour: u32| Variable(6 * vertex + colour);
    for vertex in 0..120 {
        assert!(solver.add_clause((0..6).map(|c| Literal::positive(var(vertex, c))).collect()));
        for c in 0..6 {
            for d in (c + 1)..6 {
                assert!(solver.add_clause(vec![
                    Literal::negative(var(vertex, c)),
                    Literal::negative(var(vertex, d)),
                ]));
            }
        }
    }
    for u in 0..120u32 {
        for v in (u + 1)..120 {
            if (u * 7 + v * 13) % 5 < 2 {
                for c in 0..6 {
                    assert!(solver.add_clause(vec![
                        Literal::negative(var(u, c)),
                        Literal::negative(var(v, c)),
                    ]));
                }
            }
        }
    }
}

/// Run the symmetry pass with a stop that fires from its `fire_at`-th sample
/// on (`u32::MAX`: never). Returns the result and the clause-count change.
fn run_pass(fire_at: u32) -> (Solver, (bool, bool), usize) {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());
    let mut solver = Solver::new(720);
    solver.set_symmetry_oneshot(true);
    add_dense_colouring(&mut solver);
    let before = solver.arena.active_clause_count();
    let samples = Cell::new(0u32);
    let stop = || {
        samples.set(samples.get().saturating_add(1));
        samples.get() >= fire_at
    };
    let result = solver.preprocess_symmetry_interruptible(&stop);
    let added = solver.arena.active_clause_count() - before;
    (solver, result, added)
}

#[test]
fn the_orbitope_route_breaks_the_dense_colouring_without_a_stop() {
    let (solver, (_, changed), _) = run_pass(u32::MAX);
    assert!(changed);
    assert!(solver.cold.symmetry_stats.sb_clauses_added > 0);
}

#[test]
fn a_stop_inside_the_orbitope_route_adds_nothing_and_says_why() {
    // The first sample is the pass's own entry check; the second lands inside
    // detection (the formula is below every per-clause poll stride).
    let (solver, result, added) = run_pass(2);
    assert_eq!(result, (false, false));
    assert_eq!(added, 0);
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 0);
    assert!(
        solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .any(|(route, outcome)| *route == "orbitope" && outcome == "stopped: Interrupted"),
        "routes: {:?}",
        solver.cold.symmetry_stats.routes
    );
}
