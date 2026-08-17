// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental theory scope cleanup and reset regressions.

use super::*;

/// Regression test for #2822: pop must invalidate activation scope entries
/// for the popped depth so that re-activation correctly re-adds them.
#[test]
fn incremental_theory_state_pop_invalidates_activation_scopes_at_popped_depth() {
    let mut st = IncrementalTheoryState::new();
    // Simulate assertions activated at various scope levels
    st.assertion_activation_scope.insert(TermId::new(1), 0); // global
    st.assertion_activation_scope.insert(TermId::new(2), 1); // scope 1
    st.assertion_activation_scope.insert(TermId::new(3), 2); // scope 2

    st.scope_depth = 2;

    // Pop from scope 2 to scope 1
    assert!(st.pop());
    assert_eq!(st.scope_depth, 1);
    // Scope 0 and scope 1 entries survive; scope 2 entry is invalidated
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(1)), Some(&0));
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(2)), Some(&1));
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(3)), None);

    // Pop from scope 1 to scope 0
    assert!(st.pop());
    assert_eq!(st.scope_depth, 0);
    // Only scope 0 entry survives
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(1)), Some(&0));
    assert_eq!(st.assertion_activation_scope.get(&TermId::new(2)), None);
}

#[test]
fn incremental_theory_state_reset_clears_all_state() {
    let mut st = IncrementalTheoryState::new();

    // Modify all fields from their defaults
    st.persistent_sat = Some(SatSolver::new(10));
    st.lia_persistent_sat = Some(SatSolver::new(5));
    st.encoded_assertions.insert(TermId::new(1), 7);
    st.assertion_activation_scope.insert(TermId::new(1), 2);
    st.tseitin_state.next_var = 50;
    st.scope_depth = 3;
    st.pending_push = 2;
    st.theory_atoms.push(TermId::new(1));
    st.pre_push_assertions.insert(TermId::new(2));
    st.needs_activation_reassert = true;
    st.theory_conflicts = 42;
    st.theory_propagations = 100;
    st.round_trips = 7;
    st.sat_solve_secs = 1.5;
    st.theory_sync_secs = 0.3;
    st.theory_check_secs = 0.8;

    // Reset
    st.reset();

    // Verify all fields are reset to initial state
    assert!(st.persistent_sat.is_none());
    assert!(st.lia_persistent_sat.is_none());
    assert!(st.encoded_assertions.is_empty());
    assert!(st.assertion_activation_scope.is_empty());
    assert_eq!(st.tseitin_state.next_var, 1);
    assert_eq!(st.scope_depth, 0);
    assert_eq!(st.pending_push, 0);
    assert!(st.theory_atoms.is_empty());
    assert!(st.pre_push_assertions.is_empty());
    assert!(!st.needs_activation_reassert);
    assert_eq!(st.theory_conflicts, 0);
    assert_eq!(st.theory_propagations, 0);
    assert_eq!(st.round_trips, 0);
    assert_eq!(st.sat_solve_secs, 0.0);
    assert_eq!(st.theory_sync_secs, 0.0);
    assert_eq!(st.theory_check_secs, 0.0);
}

/// Regression test for #8572: pop must trim clausification_proofs and
/// original_clause_theory_proofs to prevent memory leaks in long push/pop
/// sessions (IC3/PDR).
#[test]
fn incremental_theory_state_pop_trims_clausification_proofs() {
    let mut st = IncrementalTheoryState::new();
    // Simulate some global-scope proof entries (before any push)
    st.clausification_proofs.push(None);
    st.original_clause_theory_proofs.push(None);

    st.push(); // scope 1
               // Simulate scoped proof entries added during scope 1
    st.clausification_proofs.push(None);
    st.clausification_proofs.push(None);
    st.original_clause_theory_proofs.push(None);
    st.original_clause_theory_proofs.push(None);

    assert_eq!(st.clausification_proofs.len(), 3);
    assert_eq!(st.original_clause_theory_proofs.len(), 3);

    assert!(st.pop()); // back to scope 0
                       // Scoped entries should be trimmed; pre-push entries survive.
    assert_eq!(st.clausification_proofs.len(), 1);
    assert_eq!(st.original_clause_theory_proofs.len(), 1);
}

/// Verify nested push/pop trims proof vectors at each level (#8572).
#[test]
fn incremental_theory_state_nested_push_pop_trims_proof_vectors() {
    let mut st = IncrementalTheoryState::new();

    st.push(); // scope 1
    st.clausification_proofs.push(None);
    st.original_clause_theory_proofs.push(None);

    st.push(); // scope 2
    st.clausification_proofs.push(None);
    st.clausification_proofs.push(None);
    st.original_clause_theory_proofs.push(None);
    st.original_clause_theory_proofs.push(None);

    assert_eq!(st.clausification_proofs.len(), 3);

    // Pop scope 2 -> scope 1: entries from scope 2 removed
    assert!(st.pop());
    assert_eq!(st.clausification_proofs.len(), 1);
    assert_eq!(st.original_clause_theory_proofs.len(), 1);

    // Pop scope 1 -> scope 0: entries from scope 1 removed
    assert!(st.pop());
    assert_eq!(st.clausification_proofs.len(), 0);
    assert_eq!(st.original_clause_theory_proofs.len(), 0);
}

/// Verify that reset clears proof_scope_starts (#8572).
#[test]
fn incremental_theory_state_reset_clears_proof_scope_starts() {
    let mut st = IncrementalTheoryState::new();
    st.push();
    st.push();
    assert_eq!(st.proof_scope_starts.len(), 2);

    st.reset();
    assert!(st.proof_scope_starts.is_empty());
}
