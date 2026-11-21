// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Who branches: the annotated heuristic, or the SAT core's activity
//! heuristic on every other restart of an optimisation search (AY-N8).

use super::extension::{branching, Branching};

#[test]
fn satisfaction_always_follows_the_annotated_search() {
    for restarts in 0..6 {
        assert_eq!(branching(false, restarts), Branching::Annotated);
    }
}

#[test]
fn optimisation_alternates_at_each_restart_starting_annotated() {
    let seen: Vec<Branching> = (0..4).map(|restarts| branching(true, restarts)).collect();
    assert_eq!(
        seen,
        [
            Branching::Annotated,
            Branching::Activity,
            Branching::Annotated,
            Branching::Activity
        ]
    );
}

// The engine in `Branching::Activity`: every search starts at restart 1
// (the test hook), so an optimisation search leaves every decision to the
// SAT core's activity heuristic from its first decision on. Tiny models
// finish before their first restart, so without the hook the brute-force
// harness never reaches this mode.

use super::extension::branching_test_hooks::{ACTIVITY_DECISIONS, FIRST_RESTART};
use super::tests_brute_force::{check_family, MODELS};
use super::CpSatEngine;
use crate::domain::Domain;
use crate::engine::CpSolveResult;
use crate::propagator::Constraint;

/// Run `f` with every search starting at restart `first`; return the
/// number of activity decisions it made.
fn with_first_restart(first: u64, f: impl FnOnce()) -> u64 {
    FIRST_RESTART.with(|c| c.set(first));
    ACTIVITY_DECISIONS.with(|c| c.set(0));
    f();
    FIRST_RESTART.with(|c| c.set(0));
    ACTIVITY_DECISIONS.with(std::cell::Cell::get)
}

/// Minimize `x0 + 2 x1 + 3 x2` over a permutation of 1..=3: the optimum
/// is 10 (x = [3, 2, 1]).
fn optimum_of_weighted_permutation() -> i64 {
    let mut engine = CpSatEngine::new();
    let x: Vec<_> = (0..3)
        .map(|_| engine.new_int_var(Domain::new(1, 3), None))
        .collect();
    engine.add_constraint(Constraint::AllDifferent(x.clone()));
    let obj = engine.new_int_var(Domain::new(0, 20), None);
    let mut vars = x;
    vars.push(obj);
    engine.add_constraint(Constraint::LinearEq {
        coeffs: vec![1, 2, 3, -1],
        vars,
        rhs: 0,
    });
    engine.set_objective(obj, true);
    let mut best = None;
    loop {
        match engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let value = assignment
                    .iter()
                    .find(|(v, _)| *v == obj)
                    .expect("objective assigned")
                    .1;
                best = Some(value);
                engine.add_upper_bound(obj, value - 1);
            }
            CpSolveResult::Unsat => return best.expect("a solution exists"),
            CpSolveResult::Unknown => panic!("unknown on a tiny model"),
        }
    }
}

#[test]
fn activity_mode_is_reached_and_finds_the_optimum() {
    let mut optimum = 0;
    let decisions = with_first_restart(1, || optimum = optimum_of_weighted_permutation());
    assert_eq!(optimum, 10);
    assert!(
        decisions > 0,
        "no decision was left to the activity heuristic"
    );
}

#[test]
fn annotated_mode_makes_no_activity_decision() {
    let mut optimum = 0;
    let decisions = with_first_restart(0, || optimum = optimum_of_weighted_permutation());
    assert_eq!(optimum, 10);
    assert_eq!(
        decisions, 0,
        "a tiny model finishes before its first restart"
    );
}

/// The brute-force harness (enumeration, then optimisation with a probed
/// bound) for every constraint, with the optimisation in activity mode.
#[test]
fn every_constraint_optimises_like_brute_force_in_activity_mode() {
    let decisions = with_first_restart(1, || {
        for &(name, generate) in MODELS {
            check_family(name, generate, 60);
        }
    });
    assert!(
        decisions > 0,
        "no decision was left to the activity heuristic"
    );
}
