// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::AlethePrinter;
use super::monolithic::MONOLITHIC_WORK;
use super::*;
use crate::resolution_dag_memo::{
    prove_unsat_resolution_dag_memoized_within, reset_resolution_dag_memo,
};
use ay_core::{ProofId, TermStore};
use std::cell::Cell;

fn grid() -> Vec<Vec<Literal>> {
    [(1, 2), (1, -2), (-1, 2), (-1, -2)]
        .into_iter()
        .map(|(a, b)| vec![Literal::from_dimacs(a), Literal::from_dimacs(b)])
        .collect()
}

fn blaster<'a, 'p>(printer: &'p AlethePrinter<'a>) -> Blaster<'a, 'p> {
    let mut blaster = Blaster::new(printer, ProofId(1), "@ay_ordinary_owner_".to_string());
    blaster.circuit.atom("p".to_string());
    blaster.circuit.atom("q".to_string());
    blaster
}

#[test]
fn monolithic_transport_inherits_the_actual_ordinary_memo_and_child_trace() {
    reset_resolution_dag_memo();
    let cnf = grid();
    let direct_polls = Cell::new(0);
    let expected = prove_unsat_resolution_dag_memoized_within(
        2,
        &cnf,
        MONOLITHIC_WORK,
        Some(&|| {
            direct_polls.set(direct_polls.get() + 1);
            false
        }),
    )
    .expect("ordinary child and memo");
    reset_resolution_dag_memo();
    let terms = TermStore::new();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let actual = blaster(&printer)
        .monolithic_refutation(&cnf)
        .expect("same ordinary algorithm under printer owner");
    actual.validate().expect("independent RUP replay");
    assert_eq!(actual, expected);
    assert_eq!(calls.get(), 4 + 2 * direct_polls.get());
}

#[test]
fn every_monolithic_transport_observation_refuses_without_a_fresh_owner() {
    reset_resolution_dag_memo();
    let cnf = grid();
    let terms = TermStore::new();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    blaster(&printer)
        .monolithic_refutation(&cnf)
        .expect("baseline ordinary proof");
    let total = calls.get();
    drop(printer);
    for stop in 1..=total {
        reset_resolution_dag_memo();
        let calls = Cell::new(0usize);
        let mut callback = || {
            calls.set(calls.get() + 1);
            calls.get() != stop
        };
        let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
        let blaster = blaster(&printer);
        assert_eq!(
            blaster.monolithic_refutation(&cnf),
            Err(false),
            "poll {stop}/{total}"
        );
        assert_eq!(calls.get(), stop);
        assert_eq!(blaster.monolithic_refutation(&cnf), Err(false));
        assert_eq!(calls.get(), stop);
    }
}
