// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The actual nested core child inherits the parent stop owner.

use super::super::LEAF_CONFLICTS;
use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn fixture(sweep: &mut Sweep<'_, '_>) -> (Pool, Propagated, Core) {
    let pool = sweep.pool(&[], &[]);
    let prop = Propagated {
        value: vec![None],
        reason_of: vec![None],
        trail: vec![],
    };
    let core = Core {
        global: vec![0],
        local_of: [(0usize, 0usize)].into_iter().collect(),
        clauses: pool.clauses.clone(),
        sources: (0..pool.len()).collect(),
    };
    (pool, prop, core)
}

#[test]
fn nested_core_refusal_is_sticky_and_cannot_select_direct_fallback() {
    let calls = Cell::new(0usize);
    let refuse_once = Cell::new(false);
    let mut keep_going = || {
        calls.set(calls.get() + 1);
        !refuse_once.replace(false)
    };
    let p = literal(0, false);
    let cnf = vec![vec![p], vec![p.negated()]];
    let limits = SweepLimits::standalone();
    let mut sweep = Sweep::new(
        vec![Gate::Input],
        &cnf,
        &[0, 1],
        false,
        limits,
        &mut keep_going,
    )
    .unwrap();
    let (pool, prop, core) = fixture(&mut sweep);
    let derived = Derived::new(&pool, &prop, &[]);
    let baseline = calls.get();
    refuse_once.set(true);
    assert!(sweep.refute_core(&derived, &core, LEAF_CONFLICTS).is_none());
    assert!(sweep.stopped);
    assert!(
        !refuse_once.get(),
        "the nested child observed the actual owner"
    );
    assert_eq!(calls.get(), baseline + 1);
    assert_eq!(sweep.deadline, limits.deadline);
    assert_eq!(sweep.conflicts_left, limits.total_conflicts);
    assert!(sweep.refute_core(&derived, &core, LEAF_CONFLICTS).is_none());
    assert!(sweep.solve(1, &cnf, LEAF_CONFLICTS).is_none());
    assert_eq!(
        calls.get(),
        baseline + 1,
        "no callback credit after refusal"
    );
}

#[test]
fn healthy_nested_core_keeps_the_existing_replayable_refutation() {
    let calls = Cell::new(0usize);
    let mut keep_going = || {
        calls.set(calls.get() + 1);
        true
    };
    let p = literal(0, false);
    let cnf = vec![vec![p], vec![p.negated()]];
    let limits = SweepLimits::standalone();
    let mut sweep = Sweep::new(
        vec![Gate::Input],
        &cnf,
        &[0, 1],
        false,
        limits,
        &mut keep_going,
    )
    .unwrap();
    let (pool, prop, core) = fixture(&mut sweep);
    let derived = Derived::new(&pool, &prop, &[]);
    let baseline = calls.get();
    let dag = sweep.refute_core(&derived, &core, LEAF_CONFLICTS).unwrap();
    assert!(
        calls.get() > baseline + 1,
        "entry AND actual child must observe progress"
    );
    assert!(!sweep.stopped);
    assert_eq!(sweep.deadline, limits.deadline);
    dag.validate().unwrap();
}

#[test]
fn a_caught_nested_owner_panic_does_not_reopen_the_parent() {
    let calls = Cell::new(0usize);
    let panic_once = Cell::new(false);
    let mut keep_going = || {
        calls.set(calls.get() + 1);
        assert!(
            !panic_once.replace(false),
            "test-only inherited owner panic"
        );
        true
    };
    let p = literal(0, false);
    let cnf = vec![vec![p], vec![p.negated()]];
    let mut sweep = Sweep::new(
        vec![Gate::Input],
        &cnf,
        &[0, 1],
        false,
        SweepLimits::standalone(),
        &mut keep_going,
    )
    .unwrap();
    let (pool, prop, core) = fixture(&mut sweep);
    let derived = Derived::new(&pool, &prop, &[]);
    let baseline = calls.get();
    panic_once.set(true);
    assert!(catch_unwind(AssertUnwindSafe(|| {
        sweep.refute_core(&derived, &core, LEAF_CONFLICTS)
    }))
    .is_err());
    assert!(sweep.stopped);
    assert!(!panic_once.get());
    assert!(sweep.refute_core(&derived, &core, LEAF_CONFLICTS).is_none());
    assert!(sweep.solve(1, &cnf, LEAF_CONFLICTS).is_none());
    assert_eq!(calls.get(), baseline + 1);
}

#[test]
fn a_refusal_inside_the_nested_child_not_only_its_entry_stops_the_parent() {
    let calls = Cell::new(0usize);
    let stop_at = Cell::new(0usize);
    let mut keep_going = || {
        let ordinal = calls.get() + 1;
        calls.set(ordinal);
        ordinal != stop_at.get()
    };
    let p = literal(0, false);
    let cnf = vec![vec![p], vec![p.negated()]];
    let limits = SweepLimits::standalone();
    let mut sweep = Sweep::new(
        vec![Gate::Input],
        &cnf,
        &[0, 1],
        false,
        limits,
        &mut keep_going,
    )
    .unwrap();
    let (pool, prop, core) = fixture(&mut sweep);
    let derived = Derived::new(&pool, &prop, &[]);
    let baseline = calls.get();
    // The first observation is Core::sweep entry; the SECOND belongs to
    // the actual refute_counted child. An always-true child bypass fails here.
    stop_at.set(baseline + 2);
    assert!(sweep.refute_core(&derived, &core, LEAF_CONFLICTS).is_none());
    assert_eq!(
        calls.get(),
        baseline + 2,
        "the actual child observed refusal"
    );
    assert!(sweep.stopped);
    assert_eq!(sweep.deadline, limits.deadline);
    assert_eq!(sweep.conflicts_left, limits.total_conflicts);
    assert!(sweep.refute_core(&derived, &core, LEAF_CONFLICTS).is_none());
    assert!(sweep.solve(1, &cnf, LEAF_CONFLICTS).is_none());
    assert_eq!(calls.get(), baseline + 2, "no retry or new callback credit");
}
