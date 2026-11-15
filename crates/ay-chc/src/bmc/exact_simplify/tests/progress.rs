// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

fn attempt(conjuncts: Vec<ChcExpr>, refusal: usize) -> (Option<ChcExpr>, usize) {
    let armed = Cell::new(false);
    let calls = Cell::new(0usize);
    let mut keep_going = || {
        if !armed.get() {
            return true;
        }
        calls.set(calls.get() + 1);
        calls.get() != refusal
    };
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut keep_going).unwrap();
    armed.set(true);
    let result = simplify(conjuncts, &mut names);
    if result.is_none() {
        assert!(names.stopped());
        let stopped_at = calls.get();
        assert!(simplify(Vec::new(), &mut names).is_none());
        assert_eq!(calls.get(), stopped_at, "refusal must stay sticky");
    }
    (result, calls.get())
}

#[test]
fn every_callback_including_final_admission_is_terminal_for_true_false_and_rewrites() {
    for conjuncts in ordinary_cases() {
        let (expected, calls) = attempt(conjuncts.clone(), usize::MAX);
        assert!(expected.is_some());
        assert!(calls > 0);
        for refusal in 1..=calls {
            let (result, observed) = attempt(conjuncts.clone(), refusal);
            assert!(result.is_none(), "refusal {refusal}/{calls}");
            assert_eq!(observed, refusal);
        }
        assert_eq!(attempt(conjuncts, usize::MAX).0, expected);
    }
}

fn twice(refusal: usize) -> (Option<ChcExpr>, usize) {
    let armed = Cell::new(false);
    let calls = Cell::new(0usize);
    let mut keep_going = || {
        if !armed.get() {
            return true;
        }
        calls.set(calls.get() + 1);
        calls.get() != refusal
    };
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut keep_going).unwrap();
    armed.set(true);
    let result = simplify(vec![ChcExpr::Bool(true)], &mut names)
        .and_then(|_| simplify(contradictory_bounds(), &mut names));
    (result, calls.get())
}

#[test]
fn consecutive_simplifications_share_the_same_caller_allowance() {
    let (expected, calls) = twice(usize::MAX);
    assert_eq!(expected, Some(ChcExpr::Bool(false)));
    for refusal in 1..=calls {
        let (result, observed) = twice(refusal);
        assert!(result.is_none());
        assert_eq!(observed, refusal);
    }
}
