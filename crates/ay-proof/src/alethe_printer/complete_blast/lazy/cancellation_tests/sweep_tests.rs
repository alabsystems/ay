// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::sat_sweep::{Gate, SweepLimits};
use ay_sat::ResolutionDag;

fn contradiction() -> (Circuit, Vec<Vec<Literal>>) {
    let mut circuit = Circuit::new("@ay_owner_sweep_".to_string());
    circuit.constant(false);
    (
        circuit,
        vec![
            vec![crate::sat_sweep::literal(0, true)],
            vec![crate::sat_sweep::literal(0, false)],
        ],
    )
}

fn reference(direct: bool, cnf: &[Vec<Literal>], polls: &mut usize) -> ResolutionDag {
    let limits = if direct {
        SweepLimits {
            total_conflicts: crate::sat_sweep::LEMMA_CONFLICTS,
            ..SweepLimits::standalone()
        }
    } else {
        SweepLimits::standalone()
    };
    let mut callback = || {
        *polls += 1;
        true
    };
    let dag = if direct {
        match crate::sat_sweep::refute_directly(
            vec![Gate::Const(false)],
            cnf,
            &[1],
            true,
            limits,
            sweep::DIRECT_PROOF_BYTES,
            &mut callback,
        ) {
            crate::sat_sweep::Direct::Refuted(dag) => Some(dag),
            crate::sat_sweep::Direct::Satisfiable | crate::sat_sweep::Direct::Undecided => None,
        }
    } else {
        crate::sat_sweep::refute(
            vec![Gate::Const(false)],
            cnf,
            &[1],
            true,
            limits,
            &mut callback,
        )
    }
    .expect("tiny root refutes");
    dag.validate().expect("independent DAG replay");
    dag
}

fn wrapper(
    direct: bool,
    printer: &AlethePrinter<'_>,
    circuit: &Circuit,
    cnf: &[Vec<Literal>],
) -> Option<ResolutionDag> {
    if direct {
        sweep::refute_directly(printer, circuit, &[], cnf, 2)
    } else {
        sweep::refute(printer, circuit, &[], cnf, 2)
    }
}

fn actual_child_polls(direct: bool) {
    let (circuit, cnf) = contradiction();
    let terms = TermStore::new();
    let mut child_polls = 0;
    let expected = reference(direct, &cnf, &mut child_polls);
    assert!(child_polls > 0);
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let actual = wrapper(direct, &printer, &circuit, &cnf).expect("same refutation under owner");
    actual.validate().expect("independent DAG replay");
    assert_eq!(actual, expected);
    assert_eq!(calls.get(), 8 + 2 * child_polls);
}

fn every_child_poll_refuses(direct: bool) {
    let (circuit, cnf) = contradiction();
    let terms = TermStore::new();
    let mut child_polls = 0;
    reference(direct, &cnf, &mut child_polls);
    for stop in 7..=(6 + 2 * child_polls) {
        let calls = Cell::new(0usize);
        let mut callback = || {
            calls.set(calls.get() + 1);
            calls.get() != stop
        };
        let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
        assert!(wrapper(direct, &printer, &circuit, &cnf).is_none());
        assert_eq!(calls.get(), stop);
        assert!(
            wrapper(!direct, &printer, &circuit, &cnf).is_none(),
            "a later strategy cannot reset the owner"
        );
        assert_eq!(calls.get(), stop);
    }
}

#[test]
fn direct_refutation_inherits_every_actual_child_observation() {
    actual_child_polls(true);
}

#[test]
fn swept_refutation_inherits_every_actual_child_observation() {
    actual_child_polls(false);
}

#[test]
fn a_stop_inside_direct_refutation_is_not_recovered_by_sweeping() {
    every_child_poll_refuses(true);
}

#[test]
fn a_stop_inside_sweeping_is_not_recovered_by_direct_refutation() {
    every_child_poll_refuses(false);
}
