// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `prove_unsat_resolution_dag_until` stops when its caller's stop fires, and
//! otherwise finds exactly the refutation `prove_unsat_resolution_dag` finds;
//! `prove_unsat_resolution_dag_within` does the same inside a counted work
//! envelope, and tells the envelope running out apart from a stop.

use std::cell::Cell;

use ay_sat::{
    prove_unsat_resolution_dag, prove_unsat_resolution_dag_until,
    prove_unsat_resolution_dag_within, Literal, ResolutionDagError, ResolutionDagWork, Variable,
};

/// The pigeonhole principle: `holes + 1` pigeons in `holes` holes, a formula
/// resolution refutes only after many conflicts.
fn pigeonhole(holes: u32) -> (usize, Vec<Vec<Literal>>) {
    let pigeons = holes + 1;
    let var = |pigeon: u32, hole: u32| Variable::new(pigeon * holes + hole);
    let mut clauses: Vec<Vec<Literal>> = (0..pigeons)
        .map(|pigeon| {
            (0..holes)
                .map(|hole| Literal::positive(var(pigeon, hole)))
                .collect()
        })
        .collect();
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in first + 1..pigeons {
                clauses.push(vec![
                    Literal::negative(var(first, hole)),
                    Literal::negative(var(second, hole)),
                ]);
            }
        }
    }
    ((pigeons * holes) as usize, clauses)
}

#[test]
fn a_stop_that_never_fires_leaves_the_refutation_as_it_was() {
    let (vars, clauses) = pigeonhole(4);
    let polls = Cell::new(0_u32);
    let idle = || {
        polls.set(polls.get() + 1);
        false
    };
    let polled = prove_unsat_resolution_dag_until(vars, &clauses, &idle).expect("unsat");
    let unpolled = prove_unsat_resolution_dag(vars, &clauses).expect("unsat");
    assert_eq!(polled, unpolled);
    assert!(polls.get() >= 1, "the solve polled its stop");

    let satisfiable = vec![vec![Literal::positive(Variable::new(0))]];
    let error = prove_unsat_resolution_dag_until(1, &satisfiable, &|| false).expect_err("sat");
    assert_eq!(error, ResolutionDagError::Satisfiable);
}

/// `pad` satisfiable binary clauses over fresh variables, then `x` and `!x`:
/// a CNF that loads `2 * pad + 2` literals and refutes at once.
fn padded_contradiction(pad: u32) -> (usize, Vec<Vec<Literal>>) {
    let x = Variable::new(2 * pad);
    let mut clauses: Vec<Vec<Literal>> = (0..pad)
        .map(|i| {
            vec![
                Literal::positive(Variable::new(2 * i)),
                Literal::positive(Variable::new(2 * i + 1)),
            ]
        })
        .collect();
    clauses.push(vec![Literal::positive(x)]);
    clauses.push(vec![Literal::negative(x)]);
    ((2 * pad + 1) as usize, clauses)
}

/// Loading is polled after every 4,096 literals. Before, the first poll was
/// the solver's entry poll after the whole CNF was in: 3-4.4 s for a
/// 1.6M-clause complete blast in the test profile. This CNF loads 100,002
/// literals, so an idle stop is polled at least 24 times while it loads (the
/// solve itself refutes it within a few polls) and leaves the refutation as
/// it was; a stop that fires on its tenth poll is seen while the CNF loads
/// and ends it Unknown, where unpolled loading let it refute.
#[test]
fn a_stop_is_polled_while_the_clauses_load() {
    let (vars, clauses) = padded_contradiction(50_000);
    let idle_polls = Cell::new(0_u32);
    let idle = || {
        idle_polls.set(idle_polls.get() + 1);
        false
    };
    let polled = prove_unsat_resolution_dag_until(vars, &clauses, &idle).expect("unsat");
    assert_eq!(
        polled,
        prove_unsat_resolution_dag(vars, &clauses).expect("unsat")
    );
    assert!(idle_polls.get() >= 24, "{} polls", idle_polls.get());

    let polls = Cell::new(0_u32);
    let tenth_poll = || {
        polls.set(polls.get() + 1);
        polls.get() >= 10
    };
    let stopped = prove_unsat_resolution_dag_until(vars, &clauses, &tenth_poll);
    assert_eq!(stopped.expect_err("stopped"), ResolutionDagError::Unknown);
    assert_eq!(
        polls.get(),
        10,
        "seen at its tenth poll, while the clauses load"
    );
}

/// A stop is neither a refutation nor a satisfiable verdict, whether it has
/// fired before the solve or fires during its search.
#[test]
fn a_stop_ends_the_solve_without_a_verdict() {
    let (vars, clauses) = pigeonhole(4);
    let fired = prove_unsat_resolution_dag_until(vars, &clauses, &|| true);
    assert_eq!(fired.expect_err("stopped"), ResolutionDagError::Unknown);

    let (vars, clauses) = pigeonhole(8);
    let polls = Cell::new(0_u32);
    let second_poll = || {
        polls.set(polls.get() + 1);
        polls.get() >= 2
    };
    let stopped = prove_unsat_resolution_dag_until(vars, &clauses, &second_poll);
    assert_eq!(stopped.expect_err("stopped"), ResolutionDagError::Unknown);
    assert!(
        polls.get() >= 2,
        "the search polled its stop and ended there"
    );
}

/// An envelope wider than the search changes nothing: the refutation is the
/// unbounded one, and a satisfiable formula is still satisfiable.
#[test]
fn an_envelope_that_holds_leaves_the_refutation_as_it_was() {
    let wide = ResolutionDagWork {
        max_conflicts: 1_000_000,
        max_decisions: 1_000_000,
    };
    let (vars, clauses) = pigeonhole(4);
    let enveloped = prove_unsat_resolution_dag_within(vars, &clauses, wide, None).expect("unsat");
    let unbounded = prove_unsat_resolution_dag(vars, &clauses).expect("unsat");
    assert_eq!(enveloped, unbounded);

    let satisfiable = vec![vec![Literal::positive(Variable::new(0))]];
    let error = prove_unsat_resolution_dag_within(1, &satisfiable, wide, None).expect_err("sat");
    assert_eq!(error, ResolutionDagError::Satisfiable);
}

/// A search that outruns its envelope, in conflicts or in decisions, ends as
/// `OverEnvelope`: neither a refutation nor a satisfiable verdict, the same
/// at every ask, and never confused with a caller's stop (`Unknown`).
#[test]
fn an_exhausted_envelope_is_refused_without_a_verdict() {
    let (vars, clauses) = pigeonhole(8);
    for work in [
        ResolutionDagWork {
            max_conflicts: 100,
            max_decisions: u64::MAX,
        },
        ResolutionDagWork {
            max_conflicts: u64::MAX,
            max_decisions: 10,
        },
    ] {
        for _ in 0..2 {
            let refused = prove_unsat_resolution_dag_within(vars, &clauses, work, None);
            assert_eq!(refused.expect_err("over"), ResolutionDagError::OverEnvelope);
        }
        let stopped = prove_unsat_resolution_dag_within(vars, &clauses, work, Some(&|| true));
        assert_eq!(stopped.expect_err("stopped"), ResolutionDagError::Unknown);
    }
}
