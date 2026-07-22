// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_warmup_stats_default() {
    let stats = WarmupStats::default();
    assert_eq!(stats.warmup_count, 0);
    assert_eq!(stats.decisions, 0);
    assert_eq!(stats.propagations, 0);
    assert_eq!(stats.conflicts, 0);
}

#[test]
fn test_warmup_state_creation() {
    let state = Warmup::new(10);
    assert_eq!(state.num_vars, 10);
    assert_eq!(state.assignment.len(), 10);
    assert_eq!(state.trail.len(), 0);
    assert_eq!(state.watches.len(), 20); // 2 * num_vars
}

#[test]
fn test_warmup_reset() {
    let mut state = Warmup::new(5);

    // Simulate some state
    state.assignment[0] = Some(true);
    state.trail.push(Literal::positive(crate::Variable(0)));
    state.propagated = 1;

    // Reset
    state.reset();

    assert!(state.assignment.iter().all(Option::is_none));
    assert_eq!(state.trail.len(), 0);
    assert_eq!(state.propagated, 0);
}

#[test]
fn test_warmup_value() {
    let mut state = Warmup::new(3);

    // var0 = true
    state.assignment[0] = Some(true);
    // var1 = false
    state.assignment[1] = Some(false);
    // var2 unassigned

    // Positive literal for true variable -> true
    assert_eq!(
        state.value(Literal::positive(crate::Variable(0))),
        Some(true)
    );
    // Negative literal for true variable -> false
    assert_eq!(
        state.value(Literal::negative(crate::Variable(0))),
        Some(false)
    );
    // Positive literal for false variable -> false
    assert_eq!(
        state.value(Literal::positive(crate::Variable(1))),
        Some(false)
    );
    // Negative literal for false variable -> true
    assert_eq!(
        state.value(Literal::negative(crate::Variable(1))),
        Some(true)
    );
    // Unassigned variable -> None
    assert_eq!(state.value(Literal::positive(crate::Variable(2))), None);
}

#[test]
fn test_warmup_watch_index() {
    // Positive literal for var 0 -> index 0
    assert_eq!(
        Warmup::watch_index(Literal::positive(crate::Variable(0))),
        0
    );
    // Negative literal for var 0 -> index 1
    assert_eq!(
        Warmup::watch_index(Literal::negative(crate::Variable(0))),
        1
    );
    // Positive literal for var 5 -> index 10
    assert_eq!(
        Warmup::watch_index(Literal::positive(crate::Variable(5))),
        10
    );
    // Negative literal for var 5 -> index 11
    assert_eq!(
        Warmup::watch_index(Literal::negative(crate::Variable(5))),
        11
    );
}
