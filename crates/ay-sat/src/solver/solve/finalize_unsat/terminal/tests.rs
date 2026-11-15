// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use crate::counted_storage::test_owner;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

mod controls;
mod replay;
mod resources;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    pos(v).negated()
}

fn fixture() -> (Solver, ClauseRef, Vec<Vec<Literal>>) {
    let mut s = Solver::new(3);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    assert!(!s.veripb_hints_active());
    assert!(s.cold.retain_unsat_certificate);
    let cnf = vec![
        vec![pos(0)],
        vec![neg(0), pos(1)],
        vec![neg(1), pos(2)],
        vec![neg(2)],
    ];
    for clause in &cnf {
        assert!(s.add_clause(clause.clone()));
    }
    // Exact ordinary init_solve support layout, before the owned continuation.
    let n = s.cold.issued_original_clause_id_max;
    s.cold.streaming_core_num_originals = n;
    s.cold.streaming_core = Some(vec![false; n as usize]);
    s.initialize_watches();
    let conflict = s
        .process_initial_clauses()
        .or_else(|| s.search_propagate())
        .unwrap();
    assert_eq!(s.decision_level, 0);
    assert!(!s.has_empty_clause);
    assert!(s
        .arena
        .literals(conflict.0 as usize)
        .iter()
        .all(|lit| s.lit_val(*lit) < 0));
    (s, conflict, cnf)
}

fn run(
    s: &mut Solver,
    conflict: ClauseRef,
    owner: &CountedAdmission,
) -> Result<SatResult, SatUnknownReason> {
    s.declare_counted_root_unsat(Some(conflict), owner, None)
}
fn rows(s: &Solver) -> Vec<(u64, Vec<Literal>, bool, Vec<u64>)> {
    s.cold
        .clause_trace
        .as_ref()
        .unwrap()
        .entries()
        .iter()
        .map(|e| {
            (
                e.id,
                e.clause.to_vec(),
                e.is_original,
                e.resolution_hints.to_vec(),
            )
        })
        .collect()
}
fn core(result: SatResult) -> Vec<u64> {
    let SatResult::Unsat(certificate) = result else {
        panic!("expected actual UNSAT")
    };
    assert!(certificate.has_streaming_support());
    certificate.tracked_original_clause_ids()
}
fn clean(s: &Solver) {
    assert!(s.min.lrat_to_clear.is_empty());
    assert!(s.min.minimize_flags.iter().all(|f| f & LRAT_A == 0));
    assert!(s.cold.lrat_materialize_hints_buf.is_empty());
}
fn pending_writer(s: &mut Solver, path: &std::path::Path) {
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&crate::decision_trace::TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}
fn quiet(s: &Solver, path: &std::path::Path) {
    clean(s);
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn actual_root_unsat_matches_ordinary_trace_ids_support_and_strict_original_cnf_replay() {
    let (mut ordinary, conflict, cnf) = fixture();
    let (mut counted, actual, _) = fixture();
    let owner = test_owner(1_000_000, 1_000_000);
    counted.attach_counted_admission(owner.clone()).unwrap();
    ordinary.record_level0_conflict_chain(conflict);
    let expected = core(ordinary.declare_unsat());
    assert_eq!(core(run(&mut counted, actual, &owner).unwrap()), expected);
    assert!(!expected.is_empty());
    assert_eq!(rows(&counted), rows(&ordinary));
    assert_eq!(
        replay::serialized(&rows(&counted), None),
        replay::serialized(&rows(&ordinary), None)
    );
    assert!(replay::strict(
        &cnf,
        &replay::serialized(&rows(&counted), None)
    ));
    assert_eq!(counted.cold.next_clause_id, ordinary.cold.next_clause_id);
    assert_eq!(counted.cold.streaming_core, ordinary.cold.streaming_core);
    assert_eq!(
        counted.lrat_materialization_stats(),
        ordinary.lrat_materialization_stats()
    );
    let trace = counted.cold.clause_trace.as_ref().unwrap();
    let originals: Vec<_> = trace
        .entries()
        .iter()
        .filter(|e| e.is_original)
        .map(|e| e.clause.to_vec())
        .collect();
    assert_eq!(originals, cnf);
    assert!(crate::validate_clause_trace_resolution(
        trace,
        3,
        &crate::ResolutionValidationLimits::unbounded()
    )
    .is_ok());
    assert!((0..8).all(
        |bits| !cnf.iter().all(|clause| clause.iter().any(|lit| ((bits
            >> lit.variable().index())
            & 1
            != 0)
            == lit.is_positive()))
    ));
    assert!(owner.usage().unwrap().storage_admitted > 0);
    clean(&counted);
}

#[test]
fn omitting_a_real_root_antecedent_fails_strict_replay() {
    let (mut s, conflict, cnf) = fixture();
    let owner = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(owner.clone()).unwrap();
    run(&mut s, conflict, &owner).unwrap();
    let all = rows(&s);
    let last = all.last().unwrap();
    assert!(last.1.is_empty() && last.3.len() >= 3);
    assert!(replay::strict(&cnf, &replay::serialized(&all, None)));
    for omit in 0..last.3.len() {
        // Use the standalone strict checker, not ClauseTrace conversion:
        // conversion is allowed to reconstruct a missing antecedent.
        assert!(
            !replay::strict(&cnf, &replay::serialized(&all, Some(omit))),
            "omitted {omit}"
        );
    }
}

#[test]
fn already_emitted_terminal_empty_has_no_duplicate_row_or_new_id() {
    let (mut s, conflict, _) = fixture();
    s.record_level0_conflict_chain(conflict);
    let before = rows(&s);
    let next = s.cold.next_clause_id;
    let owner = test_owner(1_000_000, 1_000_000);
    s.attach_counted_admission(owner.clone()).unwrap();
    core(s.declare_counted_root_unsat(None, &owner, None).unwrap());
    assert_eq!(rows(&s), before);
    assert_eq!(s.cold.next_clause_id, next);
    clean(&s);
}
