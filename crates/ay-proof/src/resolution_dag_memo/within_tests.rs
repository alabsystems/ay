// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The enveloped refutation shares the success memo, and only a counted
//! envelope's refusal is retained beside it: under its CNF and its envelope.
//!
//! Each test runs on one thread (the record is thread-local) and resets it
//! first.

use super::super::{prove_unsat_resolution_dag_memoized, reset_resolution_dag_memo};
use super::{prove_unsat_resolution_dag_memoized_within, resolution_dag_refusals_served};
use crate::resolution_dag_memo::resolution_dag_memo_counters;
use ay_sat::{Literal, ResolutionDagError, ResolutionDagWork, Variable};

/// `holes + 1` pigeons in `holes` holes: resolution refutes it only after
/// many conflicts.
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

const TIGHT: ResolutionDagWork = ResolutionDagWork {
    max_conflicts: 50,
    max_decisions: 1_000_000,
};

const WIDE: ResolutionDagWork = ResolutionDagWork {
    max_conflicts: 1_000_000,
    max_decisions: 10_000_000,
};

#[test]
fn every_retained_envelope_refusal_observation_respects_the_original_stop() {
    use std::cell::Cell;
    let (vars, cnf) = pigeonhole(3);
    let refusal = super::Refusal::of(vars, &cnf, TIGHT);
    reset_resolution_dag_memo();
    super::REFUSALS.with(|record| {
        record.borrow_mut().refused.insert(refusal);
    });
    let calls = Cell::new(0usize);
    assert_eq!(
        prove_unsat_resolution_dag_memoized_within(
            vars,
            &cnf,
            TIGHT,
            Some(&|| {
                calls.set(calls.get() + 1);
                false
            })
        ),
        Err(ResolutionDagError::OverEnvelope),
    );
    let total = calls.get();
    assert!(
        total > 1,
        "key, lookup and terminal admission poll the owner"
    );
    for stop_at in 1..=total {
        let calls = Cell::new(0usize);
        assert_eq!(
            prove_unsat_resolution_dag_memoized_within(
                vars,
                &cnf,
                TIGHT,
                Some(&|| {
                    calls.set(calls.get() + 1);
                    calls.get() == stop_at
                })
            ),
            Err(ResolutionDagError::Unknown),
            "original observation {stop_at}/{total}",
        );
        assert_eq!(calls.get(), stop_at, "no retry revives a refused owner");
    }
    reset_resolution_dag_memo();
}

/// An envelope's refusal is answered from the record at the next ask under
/// the same envelope; another envelope, or another CNF, is asked for real.
#[test]
fn an_envelope_refusal_is_retained_under_its_cnf_and_envelope() {
    reset_resolution_dag_memo();
    let (vars, cnf) = pigeonhole(8);
    for served in 0..3 {
        let refused = prove_unsat_resolution_dag_memoized_within(vars, &cnf, TIGHT, None);
        assert_eq!(refused, Err(ResolutionDagError::OverEnvelope));
        assert_eq!(resolution_dag_refusals_served(), served);
    }
    let tighter = ResolutionDagWork {
        max_conflicts: 49,
        ..TIGHT
    };
    let refused = prove_unsat_resolution_dag_memoized_within(vars, &cnf, tighter, None);
    assert_eq!(refused, Err(ResolutionDagError::OverEnvelope));
    assert_eq!(
        resolution_dag_refusals_served(),
        2,
        "another envelope is asked"
    );
    let (vars, other) = pigeonhole(7);
    let refused = prove_unsat_resolution_dag_memoized_within(vars, &other, TIGHT, None);
    assert_eq!(refused, Err(ResolutionDagError::OverEnvelope));
    assert_eq!(resolution_dag_refusals_served(), 2, "another CNF is asked");
}

/// The negative twins: a stop and a satisfiable formula are never retained,
/// and a refutation found inside an envelope is the success memo's entry, so
/// the unbounded ask is served it; a stopped caller still observes its stop.
#[test]
fn only_a_counted_refusal_is_retained_and_a_refutation_is_shared() {
    reset_resolution_dag_memo();
    let (vars, cnf) = pigeonhole(4);
    let stopped = prove_unsat_resolution_dag_memoized_within(vars, &cnf, WIDE, Some(&|| true));
    assert_eq!(stopped, Err(ResolutionDagError::Unknown));
    let satisfiable = vec![vec![Literal::positive(Variable::new(0))]];
    for _ in 0..2 {
        let sat = prove_unsat_resolution_dag_memoized_within(1, &satisfiable, WIDE, None);
        assert_eq!(sat, Err(ResolutionDagError::Satisfiable));
    }
    let enveloped =
        prove_unsat_resolution_dag_memoized_within(vars, &cnf, WIDE, None).expect("UNSAT");
    assert_eq!(resolution_dag_refusals_served(), 0);
    assert_eq!(resolution_dag_memo_counters().0, 0);
    let unbounded = prove_unsat_resolution_dag_memoized(vars, &cnf).expect("UNSAT");
    assert_eq!(
        resolution_dag_memo_counters().0,
        1,
        "served the enveloped refutation"
    );
    assert_eq!(enveloped, unbounded);
    let stopped = prove_unsat_resolution_dag_memoized_within(vars, &cnf, WIDE, Some(&|| true));
    assert_eq!(stopped, Err(ResolutionDagError::Unknown));
}
