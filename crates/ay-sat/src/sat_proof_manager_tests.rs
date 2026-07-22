// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ResolutionAntecedent, SatClauseDerivation, SatProofError, SatProofManager};
use crate::test_util::lit;

#[test]
fn allocates_monotonic_clause_ids_and_advances_past_explicit_ids() {
    let mut manager = SatProofManager::new();

    let first = manager.record_original_clause(vec![lit(0, true)]);
    let second = manager.record_original_clause(vec![lit(1, true)]);
    assert_eq!(first, 1);
    assert_eq!(second, 2);
    assert_eq!(manager.next_clause_id(), 3);

    manager
        .record_original_clause_with_id(10, vec![lit(2, true)])
        .expect("explicit ID should record");
    assert_eq!(manager.next_clause_id(), 11);

    let third = manager.record_original_clause(vec![lit(3, true)]);
    assert_eq!(third, 11);
    assert_eq!(manager.clause_count(), 4);
}

#[test]
fn rejects_duplicate_explicit_clause_ids() {
    let mut manager = SatProofManager::new();
    manager
        .record_original_clause_with_id(7, vec![lit(0, true)])
        .expect("first use of ID should record");

    let err = manager
        .record_original_clause_with_id(7, vec![lit(1, true)])
        .expect_err("duplicate ID should fail");
    assert_eq!(err, SatProofError::DuplicateClauseId(7));
}

#[test]
fn records_resolution_antecedents_with_pivots() {
    let mut manager = SatProofManager::new();
    let a = manager.record_original_clause(vec![lit(0, true), lit(1, true)]);
    let b = manager.record_original_clause(vec![lit(0, false)]);
    let pivot = lit(0, true);

    let derived = manager
        .record_resolution_clause(
            vec![lit(1, true)],
            vec![
                ResolutionAntecedent::with_pivot(a, pivot),
                ResolutionAntecedent::with_pivot(b, pivot),
            ],
        )
        .expect("retained antecedents should derive");

    let record = manager.clause(derived).expect("derived clause exists");
    assert_eq!(record.clause(), &[lit(1, true)]);
    match record.derivation() {
        SatClauseDerivation::Resolution { antecedents } => {
            assert_eq!(antecedents.len(), 2);
            assert_eq!(antecedents[0].clause_id, a);
            assert_eq!(antecedents[0].pivot, Some(pivot));
            assert_eq!(antecedents[1].clause_id, b);
            assert_eq!(antecedents[1].pivot, Some(pivot));
        }
        SatClauseDerivation::Original => panic!("derived clause recorded as original"),
    }
}

#[test]
fn rejects_resolution_without_antecedents() {
    let mut manager = SatProofManager::new();
    let err = manager
        .record_resolution_clause(vec![lit(0, true)], Vec::new())
        .expect_err("empty antecedents should fail");
    assert_eq!(err, SatProofError::EmptyAntecedents);
}

#[test]
fn rejects_unknown_resolution_antecedent() {
    let mut manager = SatProofManager::new();
    let err = manager
        .record_resolution_clause(vec![lit(0, true)], vec![ResolutionAntecedent::clause(99)])
        .expect_err("unknown antecedent should fail");
    assert_eq!(err, SatProofError::UnknownClauseId(99));
}

#[test]
fn deleted_clauses_are_retained_for_audit_but_not_for_new_derivations() {
    let mut manager = SatProofManager::new();
    let original = manager.record_original_clause(vec![lit(0, true)]);

    assert!(manager.is_retained(original));
    manager
        .delete_clause(original)
        .expect("known clause should delete");
    assert!(!manager.is_retained(original));
    assert!(manager.retained_clause(original).is_none());
    assert!(
        manager.clause(original).is_some(),
        "deleted record remains inspectable"
    );

    let err = manager
        .record_resolution_clause(
            vec![lit(1, true)],
            vec![ResolutionAntecedent::clause(original)],
        )
        .expect_err("deleted antecedent should fail");
    assert_eq!(err, SatProofError::DeletedClauseId(original));
}

#[test]
fn deleting_unknown_clause_fails() {
    let mut manager = SatProofManager::new();
    let err = manager
        .delete_clause(42)
        .expect_err("unknown deletion should fail");
    assert_eq!(err, SatProofError::UnknownClauseId(42));
}
