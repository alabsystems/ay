// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::cell::Cell;

#[test]
fn dense_twelve_bit_membership_removes_the_quadratic_observations() {
    const K: usize = 12;
    const N: usize = 1 << K;
    let reach: HashSet<_> = (0..N).map(|bits| state(K, bits)).collect();
    let ordered: Vec<_> = reach.iter().collect();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let p = Proof::new_with_progress(
        "dense.".into(),
        "@dense".into(),
        EmissionProgress::with_caller(&mut callback),
    );
    let budget = p.budget;
    for s in &ordered {
        assert_eq!(covered_state(&p, &reach, &[], s), Some(true));
    }
    assert_eq!(calls.get(), 2 * N, "one pre- and one post-lookup poll");
    calls.set(0);
    for s in &ordered {
        assert_eq!(legacy::covered_state(&p, &ordered, &[], s), Some(true));
    }
    assert_eq!(calls.get(), N * (N + 1) / 2);
    assert_eq!(p.budget, budget);
    assert_eq!(p.out, "");
}

fn assert_sticky_refusal(reach: &HashSet<Vec<bool>>, chosen: &[Vec<(usize, bool)>], s: &[bool]) {
    let calls = Cell::new(0usize);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let healthy = Proof::new_with_progress(
        "healthy.".into(),
        "@healthy".into(),
        EmissionProgress::with_caller(&mut accepting),
    );
    assert!(covered_state(&healthy, reach, chosen, s).is_some());
    assert!(calls.get() >= 2, "both sides of the lookup are observed");
    for stop_at in 1..=calls.get() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let p = Proof::new_with_progress("stopped.".into(), "@stopped".into(), owner.clone());
        let budget = p.budget;
        assert_eq!(covered_state(&p, reach, chosen, s), None);
        assert_eq!(seen.get(), stop_at);
        assert!(owner.refused());
        assert_eq!(covered_state(&p, reach, chosen, s), None);
        let retry = Proof::new_with_progress("retry.".into(), "@retry".into(), owner.clone());
        assert_eq!(covered_state(&retry, reach, chosen, s), None);
        assert_eq!(
            seen.get(),
            stop_at,
            "one-shot refusal cannot be polled away"
        );
        assert_eq!(p.budget, budget);
        assert_eq!(p.out, "");
    }
}

#[test]
fn every_lookup_and_chosen_clause_poll_refuses_without_retry() {
    let reach = reachable(2, 1);
    assert_sticky_refusal(&reach, &[], &[false, false]);
    assert_sticky_refusal(&reach, &[], &[true, true]);
    assert_sticky_refusal(&reach, &[vec![(0, true)], vec![(1, true)]], &[true, true]);
    assert_sticky_refusal(&reach, &[vec![(0, false)]], &[true, true]);
    assert_sticky_refusal(&reach, &[vec![(0, true)], vec![(1, false)]], &[true, true]);
}

#[test]
fn either_lookup_poll_unwind_permanently_refuses_the_original_owner() {
    let reach = reachable(2, 1);
    for stop_at in 1..=2 {
        let calls = Cell::new(0usize);
        let mut callback = || {
            calls.set(calls.get() + 1);
            assert_ne!(calls.get(), stop_at, "original observer unwound");
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let p = Proof::new_with_progress("panic.".into(), "@panic".into(), owner.clone());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            covered_state(&p, &reach, &[], &[false, false])
        }))
        .is_err());
        assert!(owner.refused());
        assert_eq!(covered_state(&p, &reach, &[], &[false, false]), None);
        assert_eq!(calls.get(), stop_at);
    }
}

#[test]
fn membership_supports_the_existing_maximum_bounded_state() {
    let p = new_proof();
    let last = vec![true; MAX_STATE];
    let reach = HashSet::from_iter([last.clone()]);
    assert_eq!(covered_state(&p, &reach, &[], &last), Some(true));
    assert_eq!(
        covered_state(&p, &reach, &[], &[false; MAX_STATE]),
        Some(false)
    );
    assert_eq!(covered_state(&p, &reach, &[], &[true; MAX_STATE + 1]), None);
}
