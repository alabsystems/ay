// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermId;

#[test]
fn empty_manager_returns_sat() {
    let mgr = InferenceManager::new();
    assert!(!mgr.has_conflict());
    assert!(!mgr.has_pending());
    assert!(matches!(mgr.to_theory_result(), TheoryResult::Sat));
}

#[test]
fn conflict_returns_unsat() {
    let mut mgr = InferenceManager::new();
    let atom = TermId::new(1);
    mgr.add_conflict(
        InferenceKind::ConstantConflict,
        vec![TheoryLit::new(atom, true)],
    );
    assert!(mgr.has_conflict());
    assert!(mgr.has_pending());
    match mgr.to_theory_result() {
        TheoryResult::Unsat(lits) => {
            assert_eq!(lits.len(), 1);
            assert_eq!(lits[0].term, atom);
            assert!(lits[0].value);
        }
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn empty_conflict_explanation_drops_conflict() {
    let mut mgr = InferenceManager::new();
    // Empty explanation → conflict is dropped (returns Sat), preventing
    // the false UNSAT caused by over-approximate blocking clauses (#3826).
    mgr.add_conflict(InferenceKind::ConstantConflict, vec![]);

    assert!(
        matches!(mgr.to_theory_result(), TheoryResult::Sat),
        "empty conflict explanation should be dropped (not fallback to assertions)"
    );
}

#[test]
fn clear_resets_state() {
    let mut mgr = InferenceManager::new();
    mgr.add_conflict(InferenceKind::ConstantConflict, vec![]);
    assert!(mgr.has_conflict());
    mgr.clear();
    assert!(!mgr.has_conflict());
    assert!(!mgr.has_pending());
    assert!(matches!(mgr.to_theory_result(), TheoryResult::Sat));
}

#[test]
fn propagation_is_not_conflict() {
    let mut mgr = InferenceManager::new();
    let lit = TheoryLit::new(TermId::new(5), true);
    mgr.add_propagation(InferenceKind::EndpointEmpty, lit, vec![]);
    assert!(!mgr.has_conflict());
    // Propagation adds to propagations, not pending inferences.
    assert!(matches!(mgr.to_theory_result(), TheoryResult::Sat));
}

#[test]
fn internal_equality_roundtrip() {
    let mut mgr = InferenceManager::new();
    let lhs = TermId::new(7);
    let rhs = TermId::new(9);
    let why = TheoryLit::new(TermId::new(11), true);

    mgr.add_internal_equality(InferenceKind::Unify, lhs, rhs, vec![why]);
    assert!(mgr.has_internal_equalities());
    assert!(mgr.has_pending());

    let pending = mgr.drain_internal_equalities();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].lhs, lhs);
    assert_eq!(pending[0].rhs, rhs);
    assert_eq!(pending[0].explanation, vec![why]);
    assert!(!mgr.has_internal_equalities());
}
