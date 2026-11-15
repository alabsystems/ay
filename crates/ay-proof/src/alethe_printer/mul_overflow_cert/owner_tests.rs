// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual local-search owner controls, without a test-only solver.

use super::super::emission_progress::EmissionProgress;
use super::{cdcl, localsat};
use ay_core::kani_compat::DetHashMap as HashMap;
use std::cell::Cell;

#[path = "owner_tests/document.rs"]
mod document;

#[path = "owner_tests/chain.rs"]
mod chain;

fn unsat() -> Vec<localsat::Clause> {
    vec![
        vec![(1, true), (2, true)],
        vec![(1, true), (2, false)],
        vec![(1, false), (2, true)],
        vec![(1, false), (2, false)],
    ]
}

fn sat() -> Vec<localsat::Clause> {
    vec![vec![(1, true), (2, true)], vec![(1, false), (2, true)]]
}

#[test]
fn cdcl_accepting_owner_preserves_refutation_and_budget() {
    let db = unsat();
    let mut ordinary_budget = 10_000;
    let ordinary = cdcl::refute(
        &db,
        &[],
        &[],
        &mut ordinary_budget,
        &EmissionProgress::default(),
    )
    .expect("ordinary local refutation");
    assert_eq!(ordinary.learned, vec![vec![(1, false)]]);
    assert_eq!(ordinary.used, vec![0, 1, 2, 3]);
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let progress = EmissionProgress::with_caller(&mut callback);
    let mut budget = 10_000;
    let controlled =
        cdcl::refute(&db, &[], &[], &mut budget, &progress).expect("same local refutation");
    assert_eq!(controlled.learned, ordinary.learned);
    assert_eq!(controlled.used, ordinary.used);
    assert_eq!(budget, ordinary_budget);
    assert!(calls.get() > 1);
}

#[test]
fn cdcl_every_search_poll_refuses_and_stays_sticky() {
    let db = unsat();
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    assert!(cdcl::refute(&db, &[], &[], &mut 10_000, &owner).is_some());
    for stop_at in 1..=calls.get() {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let progress = EmissionProgress::with_caller(&mut callback);
        let nested = progress.clone();
        let mut budget = 10_000;
        assert!(cdcl::refute(&db, &[], &[], &mut budget, &nested).is_none());
        assert_eq!(seen.get(), stop_at, "local CDCL poll {stop_at}");
        let remaining = budget;
        assert!(progress.refused());
        assert!(cdcl::refute(&db, &[], &[], &mut budget, &progress).is_none());
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop_at);
    }
}

#[test]
fn localsat_accepting_owner_preserves_sat_and_unsat() {
    for db in [sat(), unsat()] {
        let fixed = HashMap::default();
        let mut ordinary_budget = 10_000;
        let ordinary = localsat::solve(
            &db,
            &fixed,
            &mut ordinary_budget,
            &EmissionProgress::default(),
        )
        .expect("ordinary local decision");
        let mut callback = || true;
        let owner = EmissionProgress::with_caller(&mut callback);
        let mut budget = 10_000;
        let controlled =
            localsat::solve(&db, &fixed, &mut budget, &owner).expect("same local decision");
        assert_eq!(controlled, ordinary);
        assert_eq!(budget, ordinary_budget);
        assert_eq!(controlled.is_some(), db == sat());
        if db == sat() {
            let expected = [(1, true), (2, true)].into_iter().collect();
            assert_eq!(controlled, Some(expected));
        }
    }
}

fn every_localsat_poll_refuses(db: &[localsat::Clause]) {
    let fixed = HashMap::default();
    let calls = Cell::new(0);
    let mut accepting = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accepting);
    assert!(localsat::solve(db, &fixed, &mut 10_000, &owner).is_some());
    assert!(calls.get() > 1);
    for stop_at in 1..=calls.get() {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let progress = EmissionProgress::with_caller(&mut callback);
        let nested = progress.clone();
        let mut budget = 10_000;
        assert!(localsat::solve(db, &fixed, &mut budget, &nested).is_none());
        assert_eq!(seen.get(), stop_at, "local DPLL poll {stop_at}");
        let remaining = budget;
        assert!(progress.refused());
        assert!(localsat::solve(db, &fixed, &mut budget, &progress).is_none());
        assert_eq!(budget, remaining);
        assert_eq!(seen.get(), stop_at);
    }
}

#[test]
fn localsat_sat_search_refusal_is_not_sat() {
    every_localsat_poll_refuses(&sat());
}

#[test]
fn localsat_unsat_search_refusal_is_not_unsat() {
    every_localsat_poll_refuses(&unsat());
}

#[test]
fn exhausted_local_budgets_are_never_renewed() {
    let mut callback = || true;
    let owner = EmissionProgress::with_caller(&mut callback);
    let mut budget = 0;
    assert!(cdcl::refute(&unsat(), &[], &[], &mut budget, &owner).is_none());
    assert_eq!(budget, 0);
    assert!(localsat::solve(&sat(), &HashMap::default(), &mut budget, &owner).is_none());
    assert_eq!(budget, 0);
}

#[test]
fn callback_panic_prevents_later_local_search() {
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        panic!("original owner unwound")
    };
    let owner = EmissionProgress::with_caller(&mut callback);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        localsat::solve(&sat(), &HashMap::default(), &mut 10_000, &owner)
    }));
    assert!(result.is_err());
    assert!(owner.refused());
    assert!(cdcl::refute(&unsat(), &[], &[], &mut 10_000, &owner).is_none());
    assert_eq!(calls.get(), 1);
}
