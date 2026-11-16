// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

fn identity_parity(actual: &Solver, expected: &Solver) {
    assert_eq!(
        actual.cold.original_ledger.clause_ids(),
        expected.cold.original_ledger.clause_ids()
    );
    assert_eq!(actual.cold.next_clause_id, expected.cold.next_clause_id);
    assert_eq!(
        actual.cold.next_original_clause_id,
        expected.cold.next_original_clause_id
    );
    assert_eq!(
        actual.cold.issued_original_clause_id_max,
        expected.cold.issued_original_clause_id_max
    );
    assert_eq!(
        actual.cold.original_clause_id_bits,
        expected.cold.original_clause_id_bits
    );
    assert_eq!(actual.has_empty_clause, expected.has_empty_clause);
    assert_eq!(
        actual.cold.empty_clause_in_proof,
        expected.cold.empty_clause_in_proof
    );
    assert_eq!(
        actual.cold.empty_clause_lrat_id,
        expected.cold.empty_clause_lrat_id
    );
    assert_eq!(
        actual.cold.incremental_original_boundary,
        expected.cold.incremental_original_boundary
    );
    assert_eq!(
        actual.cold.ic3_new_clauses_pending,
        expected.cold.ic3_new_clauses_pending
    );
    assert_eq!(
        actual.cold.veripb_hints.adds_by_pass,
        expected.cold.veripb_hints.adds_by_pass
    );
    assert_eq!(
        actual.cold.veripb_hints.derived.red_by_pass,
        expected.cold.veripb_hints.derived.red_by_pass
    );
}

#[test]
fn leading_interleaved_trailing_tautologies_and_empty_derivations_match_ordinary_ids() {
    let clauses = [
        &[p(0), n(0)][..],
        &[p(1), p(1)],
        &[n(1), p(1)],
        &[],
        &[],
        &[n(0), p(1)],
        &[n(0), p(0)],
    ];
    let loaded = build(2, &clauses, &[n(1)], ample()).unwrap();
    let (expected, _) = ordinary(2, &clauses);
    identity_parity(&loaded.solver, &expected);
    // No root unit or BCP step follows an original empty clause.
    assert_eq!(loaded.solver.trail, expected.trail);
    assert_eq!(loaded.solver.vals, expected.vals);
    assert_eq!(rows(&loaded.solver), rows(&expected));
    assert_eq!(
        loaded.source_ids,
        [
            Some(1),
            Some(2),
            Some(3),
            Some(4),
            Some(6),
            Some(8),
            Some(9)
        ]
    );
    assert_eq!(
        loaded.solver.cold.original_ledger.clause_ids(),
        &[2, 4, 6, 8]
    );
    assert!(!loaded.solver.is_original_clause_id(5));
    assert!(!loaded.solver.is_original_clause_id(7));
    assert!(loaded.solver.is_original_clause_id(1));
    assert!(loaded.solver.is_original_clause_id(9));
    assert_eq!(
        loaded.initial_conflict,
        InitialConflict::OriginalEmpty {
            source_row: 3,
            clause_id: 4
        }
    );
}

#[test]
fn trace_disabled_tautologies_do_not_issue_ids_or_source_trace_authority() {
    let clauses = [
        &[p(0), n(0)][..],
        &[p(1)],
        &[],
        &[],
        &[n(0), p(0)],
        &[p(0), p(1)],
    ];
    let loaded = CountedInitialCnf::try_new(2, &clauses, ample())
        .unwrap()
        .construct()
        .unwrap();
    let mut expected = Solver::with_clause_hint(2, clauses.len());
    for clause in clauses {
        expected.add_clause(clause.to_vec());
    }
    identity_parity(&loaded.solver, &expected);
    assert_eq!(
        loaded.source_ids,
        [None, Some(1), Some(2), Some(3), None, Some(4)]
    );
    assert!(loaded.solver.cold.clause_trace.is_none());
    assert!(!loaded.solver.cold.lrat_enabled);
    assert_eq!(
        loaded.solver.cold.original_ledger.clause_ids(),
        &[1, 2, 3, 4]
    );
    assert_eq!(
        loaded.initial_conflict,
        InitialConflict::OriginalEmpty {
            source_row: 2,
            clause_id: 2
        }
    );
}

#[test]
fn empty_input_and_tautology_only_input_preserve_fresh_traced_and_untraced_namespaces() {
    for vars in [0, 2] {
        let loaded = build(vars, &[], &[], ample()).unwrap();
        let (expected, conflict) = ordinary(vars, &[]);
        identity_parity(&loaded.solver, &expected);
        assert!(conflict.is_none() && rows(&loaded.solver).is_empty());
        assert_eq!(loaded.initial_conflict, InitialConflict::None);
        assert_eq!(loaded.source_ids.len(), 0);
    }
    let clauses = [&[p(0), n(0)][..], &[p(1), n(1)]];
    let traced = build(2, &clauses, &[], ample()).unwrap();
    let (expected, _) = ordinary(2, &clauses);
    identity_parity(&traced.solver, &expected);
    assert_eq!(rows(&traced.solver).len(), 0);
    assert_eq!(traced.source_ids, [Some(1), Some(2)]);
    let untraced = CountedInitialCnf::try_new(2, &clauses, ample())
        .unwrap()
        .construct()
        .unwrap();
    assert_eq!(untraced.source_ids, [None, None]);
    assert_eq!(untraced.solver.cold.next_clause_id, 1);
    assert_eq!(untraced.initial_conflict, InitialConflict::None);
}

#[test]
fn mixed_gap_and_empty_input_every_observer_cut_keeps_no_partial_namespace() {
    let _ = ay_core::misc_cli_flags();
    let mut total = 0;
    for cut in std::iter::once(usize::MAX).chain(1..=5000) {
        if cut != usize::MAX && cut > total {
            break;
        }
        let calls = Arc::new(AtomicUsize::new(0));
        let count = Arc::clone(&calls);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 100_000_000),
            None,
            Arc::new(move || count.fetch_add(1, Ordering::SeqCst) + 1 == cut),
        )
        .unwrap();
        let outcome = build(2, &[&[p(0), n(0)], &[], &[p(1)], &[]], &[], owner.clone());
        if cut == usize::MAX {
            drop(outcome.unwrap());
            total = calls.load(Ordering::SeqCst);
            assert!(total > 50 && total <= 5000);
        } else {
            assert_eq!(calls.load(Ordering::SeqCst), cut);
            assert_eq!(
                outcome.err(),
                Some(CountedAdmissionError::Original(
                    OriginalAdmissionError::ObserverStopped
                ))
            );
            let stopped = owner.usage().unwrap();
            assert!(owner.check().is_err());
            assert_eq!(owner.usage().unwrap(), stopped);
        }
    }
}
