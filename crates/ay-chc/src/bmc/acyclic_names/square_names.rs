// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use std::cell::Cell;

#[test]
fn square_ordinals_span_calls_without_consuming_expansion_instances() {
    let problem = ChcProblem::new();
    let mut live = || true;
    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    assert_eq!(
        names.square_name().as_deref(),
        Some("__bmc_square_lia_aux_0")
    );
    assert_eq!(names.instance(), Some(0));
    assert_eq!(
        names.square_name().as_deref(),
        Some("__bmc_square_lia_aux_1")
    );
    assert_eq!(names.instance(), Some(1));
    drop(names);
    let mut retry = AcyclicNames::new(&problem, &mut live).unwrap();
    assert_eq!(
        retry.square_name().as_deref(),
        Some("__bmc_square_lia_aux_0")
    );
}

#[test]
fn every_allocated_square_name_keeps_the_source_disjoint_suffix() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("__bmc_square_lia_aux_0", Vec::new());
    problem.declare_predicate("reserved__ay_exact_0", Vec::new());
    let mut live = || true;
    let mut names = AcyclicNames::new(&problem, &mut live).unwrap();
    for ordinal in 0..4 {
        assert_eq!(
            names.square_name(),
            Some(format!("__bmc_square_lia_aux_{ordinal}__ay_exact_1")),
        );
    }
}

#[test]
fn square_counter_overflow_refuses_without_wrapping_or_repolling() {
    let calls = Cell::new(0);
    let mut live = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut live).unwrap();
    names.next_square = usize::MAX;
    assert_eq!(names.square_name(), None);
    assert_eq!(names.next_square, usize::MAX);
    assert!(names.stopped());
    let stopped_at = calls.get();
    assert_eq!(names.square_name(), None);
    assert_eq!(names.instance(), None);
    assert_eq!(calls.get(), stopped_at);
}

#[test]
fn refused_or_caught_panicking_name_callbacks_cannot_revive_the_attempt() {
    for panic_on_poll in [false, true] {
        let armed = Cell::new(false);
        let calls = Cell::new(0);
        let mut progress = || {
            calls.set(calls.get() + 1);
            if armed.replace(false) {
                assert!(!panic_on_poll, "caught callback panic");
                return false;
            }
            true
        };
        let mut names = AcyclicNames::new(&ChcProblem::new(), &mut progress).unwrap();
        armed.set(true);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| names.square_name()));
        if panic_on_poll {
            assert!(result.is_err());
        } else {
            assert_eq!(result.unwrap(), None);
        }
        assert!(names.stopped());
        let stopped_at = calls.get();
        assert_eq!(names.square_name(), None);
        assert_eq!(calls.get(), stopped_at);
    }
}
