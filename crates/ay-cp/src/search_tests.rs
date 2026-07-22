// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

/// Helper: create a SearchState with no propagators for unit testing.
fn make_state(strategy: SearchStrategy, num_props: usize, num_vars: usize) -> SearchState {
    let no_props: Vec<Box<dyn crate::propagator::Propagator>> = Vec::new();
    let mut state = SearchState::new(
        strategy,
        ValueChoice::default(),
        Vec::new(),
        &no_props,
        num_vars,
    );
    state.propagator_weights = vec![1; num_props];
    state
}

#[test]
fn test_search_state_creation() {
    let state = make_state(SearchStrategy::DomWDeg, 5, 10);
    assert_eq!(state.propagator_weights.len(), 5);
    assert_eq!(state.var_activity.len(), 10);
    assert!(state.propagator_weights.iter().all(|&w| w == 1));
    assert!(state.var_activity.iter().all(|&a| a == 0.0));
}

#[test]
fn test_on_conflict_bumps_weight() {
    let mut state = make_state(SearchStrategy::DomWDeg, 3, 5);

    state.on_conflict(1, &[IntVarId(0), IntVarId(2)]);
    assert_eq!(state.propagator_weights[0], 1);
    assert_eq!(state.propagator_weights[1], 2);
    assert_eq!(state.propagator_weights[2], 1);

    // Activities should be bumped for vars 0 and 2
    assert!(state.var_activity[0] > 0.0);
    assert_eq!(state.var_activity[1], 0.0);
    assert!(state.var_activity[2] > 0.0);
}

#[test]
fn test_on_conflict_decay_increases_increment() {
    let mut state = make_state(SearchStrategy::Activity, 2, 3);
    let initial_increment = state.activity_increment;

    state.on_conflict(0, &[IntVarId(0)]);
    assert!(
        state.activity_increment > initial_increment,
        "activity increment should grow after conflict"
    );
}

#[test]
fn test_default_strategy_is_dom_wdeg() {
    assert_eq!(SearchStrategy::default(), SearchStrategy::DomWDeg);
}

#[test]
fn test_cached_wdeg_updated_on_conflict() {
    let mut state = make_state(SearchStrategy::DomWDeg, 3, 5);
    // No propagators → all cached_wdeg start at 1.0 (minimum)
    assert!(state.cached_wdeg.iter().all(|&w| w == 1.0));

    // Conflict on propagator 1, involving vars 0 and 2
    state.on_conflict(1, &[IntVarId(0), IntVarId(2)]);
    assert_eq!(state.cached_wdeg[0], 2.0);
    assert_eq!(state.cached_wdeg[1], 1.0);
    assert_eq!(state.cached_wdeg[2], 2.0);

    // Second conflict on propagator 0, involving vars 0 and 1
    state.on_conflict(0, &[IntVarId(0), IntVarId(1)]);
    assert_eq!(state.cached_wdeg[0], 3.0);
    assert_eq!(state.cached_wdeg[1], 2.0);
    assert_eq!(state.cached_wdeg[2], 2.0);
}
