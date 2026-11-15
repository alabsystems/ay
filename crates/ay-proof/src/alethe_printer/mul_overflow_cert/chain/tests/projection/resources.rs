// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

fn fixture() -> Vec<Clause> {
    vec![vec![(1, true), (2, true)]]
}

fn project(budget: &mut u64, progress: &EmissionProgress<'_>) -> Option<HashSet<Vec<bool>>> {
    let mut db = fixture();
    let original = db.clone();
    let answer = Chain::project(&mut db, &Model::default(), &[1, 2], budget, progress);
    assert_eq!(
        db, original,
        "temporary clauses never escape a refused projection"
    );
    answer
}

#[test]
fn exact_remaining_quota_succeeds_and_every_smaller_quota_refuses() {
    let owner = EmissionProgress::default();
    let mut budget = 1_000_000;
    let expected = project(&mut budget, &owner).unwrap();
    assert_eq!(expected.len(), 3);
    let cost = 1_000_000 - budget;
    assert!(cost > 0);
    let mut exact = cost;
    assert_eq!(project(&mut exact, &owner), Some(expected));
    assert_eq!(exact, 0);
    for admitted in 0..cost {
        let mut remaining = admitted;
        assert_eq!(project(&mut remaining, &owner), None, "admitted={admitted}");
        assert_eq!(remaining, 0);
    }
}

#[test]
fn every_original_owner_poll_refuses_and_restores_the_database() {
    let calls = Cell::new(0usize);
    let mut healthy = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(project(&mut 1_000_000, &EmissionProgress::with_caller(&mut healthy)).is_some());
    for stop_at in 1..=calls.get() {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut budget = 1_000_000;
        assert_eq!(project(&mut budget, &owner), None, "stop_at={stop_at}");
        assert_eq!(seen.get(), stop_at);
        assert!(owner.refused());
        let retained = budget;
        assert_eq!(project(&mut budget, &owner), None);
        assert_eq!(budget, retained, "no work after a sticky owner refusal");
        assert_eq!(seen.get(), stop_at);
    }
}

#[test]
fn a_partial_index_append_poison_cannot_be_retried_or_solved() {
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut callback);
    let fixed = Model::default();
    let mut initial_budget = 1_000_000;
    let mut initial_db = fixture();
    drop(localsat::Projection::new(&mut initial_db, &fixed, &mut initial_budget, &owner).unwrap());
    let construction_cost = 1_000_000 - initial_budget;
    let mut full_budget = 1_000_000;
    let mut full_db = fixture();
    let mut full =
        localsat::Projection::new(&mut full_db, &fixed, &mut full_budget, &owner).unwrap();
    full.append((3..20).map(|atom| (atom, true))).unwrap();
    drop(full);
    let append_cost = 1_000_000 - full_budget - construction_cost;
    for extra in 0..append_cost {
        let mut db = fixture();
        let original = db.clone();
        let mut budget = construction_cost + extra;
        let mut solver = localsat::Projection::new(&mut db, &fixed, &mut budget, &owner).unwrap();
        // Enough distinct occurrences to force refusal during clause/index growth.
        assert_eq!(solver.append((3..20).map(|atom| (atom, true))), None);
        let at_refusal = calls.get();
        assert_eq!(solver.solve(), None);
        assert_eq!(solver.append([(1, false)].into_iter()), None);
        assert_eq!(
            calls.get(),
            at_refusal,
            "poisoned sessions do not resume work"
        );
        drop(solver);
        assert_eq!(db, original);
        assert_eq!(budget, 0);
    }
}

#[test]
fn owner_refusal_poison_survives_a_caller_that_would_accept_again() {
    let calls = Cell::new(0usize);
    let accepting = Cell::new(true);
    let mut callback = || {
        calls.set(calls.get() + 1);
        accepting.get()
    };
    let owner = EmissionProgress::with_caller(&mut callback);
    let fixed = Model::default();
    let mut db = fixture();
    let original = db.clone();
    let mut budget = 1_000_000;
    let mut solver = localsat::Projection::new(&mut db, &fixed, &mut budget, &owner).unwrap();
    accepting.set(false);
    assert_eq!(solver.append([(1, false)].into_iter()), None);
    accepting.set(true);
    let stopped = calls.get();
    assert_eq!(solver.solve(), None);
    assert_eq!(solver.append([(2, false)].into_iter()), None);
    assert_eq!(calls.get(), stopped);
    drop(solver);
    assert_eq!(db, original);
}

#[test]
fn observer_unwind_restores_temporary_clauses_and_cannot_revive_the_owner() {
    let calls = Cell::new(0usize);
    let mut healthy = || {
        calls.set(calls.get() + 1);
        true
    };
    assert!(project(&mut 1_000_000, &EmissionProgress::with_caller(&mut healthy)).is_some());
    for stop_at in [1, calls.get() / 2, calls.get()] {
        let seen = Cell::new(0usize);
        let mut callback = || {
            seen.set(seen.get() + 1);
            assert_ne!(seen.get(), stop_at, "original observer unwound");
            true
        };
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut db = fixture();
        let original = db.clone();
        let mut budget = 1_000_000;
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            Chain::project(&mut db, &Model::default(), &[1, 2], &mut budget, &owner)
        }));
        assert!(unwind.is_err());
        assert_eq!(db, original);
        assert!(owner.refused());
        let remaining = budget;
        assert_eq!(project(&mut budget, &owner), None);
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop_at);
    }
}
