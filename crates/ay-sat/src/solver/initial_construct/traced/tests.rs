// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmissionError};
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};

mod namespaces;
mod replay;
mod resources;
mod unwind;

fn owner(work: u64, storage: usize) -> CountedAdmission {
    let _ = ay_core::misc_cli_flags();
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}
fn ample() -> CountedAdmission {
    owner(100_000_000, 100_000_000)
}
fn p(v: u32) -> Literal {
    Literal(v * 2)
}
fn n(v: u32) -> Literal {
    Literal(v * 2 + 1)
}
fn build(
    vars: usize,
    rows: &[&[Literal]],
    assumptions: &[Literal],
    owner: CountedAdmission,
) -> Result<CountedInitialSolver> {
    CountedInitialCnf::try_new(vars, rows, owner)?.construct_traced(assumptions)
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
fn ordinary(vars: usize, clauses: &[&[Literal]]) -> (Solver, Option<ClauseRef>) {
    let mut s = Solver::with_clause_hint(vars, clauses.len());
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    for clause in clauses {
        s.add_clause(clause.to_vec());
    }
    s.initialize_watches();
    if s.has_empty_clause {
        // The ordinary entry (`Solver::solve`) declares UNSAT on an original
        // empty clause before any root unit or BCP step; so does the counted
        // bootstrap (`ingestion::propagate`).
        return (s, None);
    }
    let conflict = s.process_initial_clauses().or_else(|| s.search_propagate());
    (s, conflict)
}

#[test]
fn traced_bootstrap_matches_actual_original_ledger_trace_and_root_bcp() {
    let clauses = [
        &[p(0)][..],
        &[n(0), p(1)],
        &[n(0), n(1), p(2)],
        &[n(2), p(3)],
    ];
    let original = ample();
    let loaded = build(4, &clauses, &[], original.clone()).unwrap();
    let (expected, conflict) = ordinary(4, &clauses);
    assert!(conflict.is_none());
    assert_eq!(rows(&loaded.solver), rows(&expected));
    assert_eq!(loaded.solver.trail, expected.trail);
    assert_eq!(loaded.solver.vals, expected.vals);
    assert_eq!(loaded.solver.qhead, expected.qhead);
    assert_eq!(
        loaded.solver.cold.original_ledger.clause_ids(),
        expected.cold.original_ledger.clause_ids()
    );
    assert_eq!(
        loaded.solver.cold.next_clause_id,
        expected.cold.next_clause_id
    );
    assert_eq!(
        loaded.solver.cold.next_original_clause_id,
        expected.cold.next_original_clause_id
    );
    assert_eq!(
        loaded.solver.watches.heap_bytes(),
        expected.watches.heap_bytes()
    );
    for lit in (0..8).map(Literal) {
        assert_eq!(
            loaded.solver.watches.len_of(lit),
            expected.watches.len_of(lit)
        );
        for i in 0..expected.watches.len_of(lit) {
            assert_eq!(
                loaded.solver.watches.entry_raw(lit, i),
                expected.watches.entry_raw(lit, i)
            );
        }
    }
    assert!(loaded.solver.cold.retain_unsat_certificate);
    assert!(loaded.solver.cold.lrat_enabled);
    assert!(loaded.input.owner().shares_ledger_with(&original));
    assert!(loaded
        .solver
        .cold
        .counted_admission
        .as_ref()
        .unwrap()
        .shares_ledger_with(&original));
    assert_eq!(loaded.initial_conflict, InitialConflict::None);
}

#[test]
fn exact_assumptions_are_retained_in_order_never_inserted_as_units() {
    let clauses = [&[p(0), p(1)][..]];
    let assumptions = [n(0), n(1), n(0)];
    let loaded = build(2, &clauses, &assumptions, ample()).unwrap();
    assert_eq!(loaded.assumptions().unwrap(), assumptions);
    assert_eq!(loaded.solver.cold.original_ledger.num_clauses(), 1);
    assert_eq!(
        rows(&loaded.solver),
        vec![(1, clauses[0].to_vec(), true, vec![])]
    );
    assert_eq!(loaded.initial_assigned_variables().unwrap(), 0);
    assert!(!loaded.initial_conflict().unwrap());
    let alternate = build(2, &clauses, &[p(0)], ample()).unwrap();
    assert_eq!(rows(&alternate.solver), rows(&loaded.solver));
    // Independent truth table: these two immutable premise lists really differ.
    let satisfies = |bits: u32, premises: &[Literal]| {
        let value = |l: Literal| ((bits >> l.variable().index()) & 1 != 0) == l.is_positive();
        clauses.iter().all(|c| c.iter().copied().any(value)) && premises.iter().copied().all(value)
    };
    assert!(!(0..4).any(|bits| satisfies(bits, &assumptions)));
    assert!((0..4).any(|bits| satisfies(bits, alternate.assumptions().unwrap())));
}

#[test]
fn authored_tautology_duplicates_empty_row_and_source_ids_remain_distinct() {
    let duplicate = [p(1), p(0), p(1)];
    let tautology = [p(0), n(0)];
    let clauses = [&duplicate[..], &tautology[..], &[], &[p(1)]];
    let loaded = build(2, &clauses, &[n(1)], ample()).unwrap();
    assert_eq!(loaded.source_ids, [Some(1), Some(2), Some(3), Some(5)]);
    for (i, clause) in clauses.iter().enumerate() {
        assert_eq!(loaded.input.clause(i).unwrap().unwrap().original(), *clause);
        assert_eq!(loaded.source_clause_id(i).unwrap(), loaded.source_ids[i]);
    }
    assert_eq!(
        loaded.initial_conflict,
        InitialConflict::OriginalEmpty {
            source_row: 2,
            clause_id: 3
        }
    );
    assert_eq!(loaded.solver.cold.original_ledger.clause_ids(), &[1, 3, 5]);
    assert_eq!(
        rows(&loaded.solver),
        vec![
            (1, vec![p(0), p(1)], true, vec![]),
            (3, vec![], true, vec![]),
            (4, vec![], false, vec![]),
            (5, vec![p(1)], true, vec![]),
        ]
    );
    assert!(loaded.solver.trail.is_empty());
}

#[test]
fn actual_conflicting_clause_reference_is_retained_not_a_boolean_verdict() {
    for clauses in [
        vec![vec![p(0)], vec![n(0)]],
        vec![vec![p(0)], vec![n(0), p(1)], vec![n(1)]],
    ] {
        let views: Vec<_> = clauses.iter().map(Vec::as_slice).collect();
        let loaded = build(2, &views, &[], ample()).unwrap();
        let InitialConflict::Clause(actual) = loaded.initial_conflict else {
            panic!("real root clause expected")
        };
        let (expected, conflict) = ordinary(2, &views);
        assert_eq!(Some(actual), conflict);
        assert_eq!(
            loaded.solver.arena.literals(actual.0 as usize),
            expected.arena.literals(actual.0 as usize)
        );
        assert!(loaded
            .solver
            .arena
            .literals(actual.0 as usize)
            .iter()
            .all(|l| loaded.solver.lit_val(*l) < 0));
        assert_eq!(rows(&loaded.solver), rows(&expected));
    }
}

#[test]
fn invalid_assumptions_refuse_before_solver_allocation_without_losing_first_cause() {
    let original = ample();
    let input = CountedInitialCnf::try_new(1, &[&[p(0)]], original.clone()).unwrap();
    assert!(matches!(
        input.construct_traced(&[p(1)]).err(),
        Some(CountedAdmissionError::Original(
            OriginalAdmissionError::Query(QueryError::Invalid(
                "initial assumption literal outside original namespace"
            ))
        ))
    ));
    let stopped = original.usage().unwrap();
    assert!(stopped.storage_admitted < 4096);
    assert!(build(1, &[&[p(0)]], &[], original.clone()).is_err());
    assert_eq!(original.usage().unwrap(), stopped);
}
