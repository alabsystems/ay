// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::proof::{is_bounded_emission_cancelled, ProofOutput};
use crate::resolution_dag::{ResolutionDag, RupStep};
use crate::test_util::lit;
use std::cell::Cell;

mod errors;

fn originals() -> Vec<(u64, Vec<Literal>)> {
    vec![
        (1, vec![lit(0, true)]),
        (2, vec![lit(0, false), lit(1, true)]),
        (3, vec![lit(1, false)]),
    ]
}

fn manager() -> ProofManager {
    manager_with_output(ProofOutput::lrat_binary(Vec::new(), 3))
}

fn manager_with_output(output: ProofOutput) -> ProofManager {
    let mut manager = ProofManager::new(output, 2);
    for (id, clause) in originals() {
        manager.register_original_clause(&clause);
        manager.register_clause_id(id);
    }
    manager
}

fn emit(manager: &mut ProofManager, keep: &dyn Fn() -> bool) -> io::Result<u64> {
    let used = manager.reserve_lrat_id_for_backward();
    let unused = manager.reserve_lrat_id_for_backward();
    assert_eq!((used, unused), (4, 5));
    manager.emit_bounded_backward_rup_step_with_cancellation(
        used,
        &[lit(1, true)],
        &[1, 2],
        None,
        keep,
    )?;
    manager.finish_bounded_backward_emission_with_cancellation(None, keep)?;
    assert!(!manager.lrat_id_usable_as_hint(unused));
    let terminal = manager.emit_bounded_empty_rup_step_with_cancellation(&[used, 3], None, keep)?;
    manager.flush_with_cancellation(keep)?;
    Ok(terminal)
}

#[test]
fn accepting_control_preserves_ids_bytes_and_independent_rup_replay() {
    let mut manager = manager();
    let terminal = emit(&mut manager, &|| true).unwrap();
    assert_eq!(terminal, 6);
    assert_eq!(manager.next_lrat_id, 7);
    assert_eq!(manager.added_count(), 2);
    assert!(manager.has_file_visible_terminal_empty());
    assert!(!manager.has_backward_reserved_ids());
    let bytes = manager
        .into_output()
        .into_inner_with_cancellation(&|| true)
        .unwrap()
        .into_vec()
        .unwrap();
    assert_eq!(bytes, [b'a', 8, 4, 0, 2, 4, 0, b'a', 12, 0, 8, 6, 0]);
    assert_eq!(
        ay_lrat_check::lrat_parser::parse_binary_lrat(&bytes)
            .unwrap()
            .len(),
        2
    );
    ResolutionDag {
        num_vars: 2,
        original_clauses: originals(),
        derived: vec![
            RupStep {
                id: 4,
                clause: vec![lit(1, true)],
                rup_hints: vec![1, 2],
            },
            RupStep {
                id: terminal,
                clause: Vec::new(),
                rup_hints: vec![4, 3],
            },
        ],
        empty_clause_id: terminal,
    }
    .validate()
    .unwrap();
}

#[test]
fn every_pipeline_poll_refusal_closes_terminal_authority_and_extraction() {
    let polls = Cell::new(0usize);
    emit(&mut manager(), &|| {
        polls.set(polls.get() + 1);
        true
    })
    .unwrap();
    assert!(polls.get() > 20);
    for stop in 1..=polls.get() {
        let mut manager = manager();
        let visits = Cell::new(0usize);
        let error = emit(&mut manager, &|| {
            visits.set(visits.get() + 1);
            visits.get() != stop
        })
        .unwrap_err();
        assert!(
            is_bounded_emission_cancelled(&error),
            "poll {stop}: {error}"
        );
        assert_eq!(visits.get(), stop);
        assert!(manager.has_io_error());
        assert!(!manager.has_file_visible_terminal_empty());
        let retry = manager
            .emit_bounded_empty_rup_step_with_cancellation(&[1, 2, 3], None, &|| {
                panic!("poisoned manager must not poll again")
            })
            .unwrap_err();
        assert!(is_bounded_emission_cancelled(&retry));
        let extracted = manager
            .into_output()
            .into_inner_with_cancellation(&|| panic!("poisoned output must not poll again"));
        assert!(is_bounded_emission_cancelled(&extracted.err().unwrap()));
    }
    assert!(
        emit(&mut manager(), &|| true).is_ok(),
        "fresh retry is independent"
    );
}

#[test]
fn retirement_polls_each_live_reservation_and_keeps_unemitted_ids_unusable() {
    const RESERVATIONS: usize = 2049;
    let make = || {
        let mut manager = manager();
        for _ in 0..RESERVATIONS {
            manager.reserve_lrat_id_for_backward();
        }
        manager
    };
    let mut accepted = make();
    let polls = Cell::new(0usize);
    accepted
        .finish_bounded_backward_emission_with_cancellation(None, &|| {
            polls.set(polls.get() + 1);
            true
        })
        .unwrap();
    assert_eq!(polls.get(), RESERVATIONS + 1);
    assert!(!accepted.has_backward_reserved_ids());
    for id in 4..4 + RESERVATIONS as u64 {
        assert!(!accepted.lrat_id_usable_as_hint(id));
    }

    let mut refused = make();
    let visits = Cell::new(0usize);
    let error = refused
        .finish_bounded_backward_emission_with_cancellation(None, &|| {
            visits.set(visits.get() + 1);
            visits.get() != 1025
        })
        .unwrap_err();
    assert!(is_bounded_emission_cancelled(&error));
    assert_eq!(visits.get(), 1025);
    assert!(refused.has_backward_reserved_ids());
    for id in 4..4 + RESERVATIONS as u64 {
        assert!(!refused.lrat_id_usable_as_hint(id));
    }
    assert!(!refused.has_file_visible_terminal_empty());
    assert!(refused.into_output().into_inner().is_err());
}

#[test]
fn hint_preflight_is_controlled_before_any_record_bytes() {
    let mut manager = manager();
    let reserved = manager.reserve_lrat_id_for_backward();
    let hints = vec![1i64; 4096];
    let polls = Cell::new(0usize);
    let error = manager
        .emit_bounded_backward_rup_step_with_cancellation(
            reserved,
            &[lit(0, true)],
            &hints,
            None,
            &|| {
                polls.set(polls.get() + 1);
                polls.get() < 1500
            },
        )
        .unwrap_err();
    assert!(is_bounded_emission_cancelled(&error));
    assert_eq!(polls.get(), 1500);
    assert_eq!(manager.added_count(), 0);
    assert!(manager.is_backward_reserved_id(reserved));
    assert!(!manager.has_file_visible_terminal_empty());
}
