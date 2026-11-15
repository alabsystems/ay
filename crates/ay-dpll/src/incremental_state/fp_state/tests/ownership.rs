// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn moving_a_complete_trial_leaves_only_a_same_scope_rebuild_shell() {
    let mut state = IncrementalFpState::new();
    let term = TermId(0);
    state.persistent_sat = Some(SatSolver::new(3));
    state.push();
    state.push();
    state.encoded_assertions.insert(term, 1);
    state.assertion_activation_scope.insert(term, 2);
    state.fp_cache.bool_input_lits.insert(term, 1);
    state.linked_predicate_vars.insert(1);
    state.linked_bool_inputs.insert(term);
    state.solves = 2;
    let trial = state.take_for_update();
    empty_encoding(&state);
    assert_eq!(state.scope_depth, 2);
    assert_eq!(state.pending_pushes, 2);
    assert!(!state.disabled);
    assert_eq!(trial.persistent_sat.as_ref().unwrap().total_num_vars(), 5);
    assert_eq!(trial.fp_cache.bool_input_lits.get(&term), Some(&1));
    assert_eq!(trial.assertion_activation_scope.get(&term), Some(&2));
    state = trial;
    assert!(state.pop());
    assert!(state.assertion_activation_scope.is_empty());
    assert_eq!(state.encoded_assertions.get(&term), Some(&1));
    assert_eq!(state.persistent_sat.as_ref().unwrap().total_num_vars(), 5);
}

#[test]
fn unwinding_a_trial_does_not_restore_partial_encoding_owners() {
    let mut state = IncrementalFpState::new();
    state.push();
    let caught = catch_unwind(AssertUnwindSafe(|| {
        let mut trial = state.take_for_update();
        trial.persistent_sat = Some(SatSolver::new(2));
        trial.fp_cache.bool_input_lits.insert(TermId(0), 1);
        trial.encoded_assertions.insert(TermId(0), 1);
        panic!("interrupted trial mutation");
    }));
    assert!(caught.is_err());
    empty_encoding(&state);
    assert_eq!((state.scope_depth, state.pending_pushes), (1, 1));
    state.push();
    assert_eq!((state.scope_depth, state.pending_pushes), (2, 2));
    assert!(state.pop());
    assert!(state.pop());
    assert!(!state.pop());
    assert_eq!((state.scope_depth, state.pending_pushes), (0, 0));
}

#[test]
fn pending_selector_overflow_is_sticky_across_pop_and_delivered_once() {
    let mut state = IncrementalFpState::new();
    state.tseitin_state.next_var = i32::MAX as u32;
    state.push();
    assert_eq!(state.pending_pushes, 1);
    assert!(state.pending_namespace_refusal.is_none());
    state.push();
    empty_encoding(&state);
    assert_eq!((state.scope_depth, state.pending_pushes), (2, 2));
    assert!(!state.disabled);
    assert!(state.pop());
    state.reset_sat_encoding_for_rebuild();
    assert_eq!(
        state.checked_total_vars(0, 0),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    assert_eq!(
        state.take_pending_namespace_refusal(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    assert_eq!(state.take_pending_namespace_refusal(), None);
    assert_eq!(state.checked_total_vars(0, state.pending_pushes), Ok(1));
}

#[test]
fn overflowing_push_drops_an_owned_solver_without_installing_a_selector() {
    let mut state = IncrementalFpState::new();
    state.persistent_sat = Some(SatSolver::new(3));
    // Metadata fault injection reaches the real pre-push check without a
    // billion-variable SAT allocation.
    state.tseitin_state.next_var = i32::MAX as u32 + 1;
    state.push();
    empty_encoding(&state);
    assert_eq!((state.scope_depth, state.pending_pushes), (1, 1));
    assert_eq!(
        state.take_pending_namespace_refusal(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    assert!(!state.disabled);
}

#[test]
fn semantic_disable_and_explicit_reset_keep_their_separate_meanings() {
    let mut state = IncrementalFpState::new();
    state.disable_and_teardown();
    state.scope_depth = i32::MAX as usize;
    state.pending_pushes = state.scope_depth;
    state.push();
    assert_eq!(state.scope_depth, i32::MAX as usize + 1);
    assert_eq!(state.pending_pushes, state.scope_depth);
    assert_eq!(state.take_pending_namespace_refusal(), None);
    let trial = state.take_for_update();
    assert!(state.disabled && trial.disabled);
    empty_encoding(&state);
    state.reset();
    assert!(!state.disabled);
    assert_eq!((state.scope_depth, state.pending_pushes), (0, 0));
    state.tseitin_state.next_var = i32::MAX as u32 + 1;
    state.push();
    assert!(state.pending_namespace_refusal.is_some());
    state.reset();
    assert_eq!(state.take_pending_namespace_refusal(), None);
    empty_encoding(&state);
}
