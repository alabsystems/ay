// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::resource::ResourceGuard;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};
use std::time::Instant;

fn budget(limit: u64) -> ResourceGuard {
    let mut owner = ResourceGuard::new();
    owner.set_rlimit(Some(limit));
    owner
}

/// Every call has a distinct callback context/effect ledger, as Kernel::call
/// does. Only the actual caller-owned resource and its typed stop are shared.
fn callback(guard: &Guard, cost: u64, produced: &mut usize) -> (Result<(), GiveUp>, u64) {
    let mut terms = TermStore::new();
    let atoms = AtomTable::default();
    let mut effects = Effects::default();
    let result = {
        let mut ctx = Ctx::new(&mut terms, None, &atoms, None, &mut effects, 0, false)
            .with_guard(Some(guard));
        ctx.tick(cost).map(|()| *produced += 1)
    };
    (result, effects.ticks)
}

#[test]
fn kernel_plugin_tick_callbacks_and_clones_share_the_original_hundred_ticks() {
    let owner = budget(100);
    let guard = Guard::new().with_resource(owner.clone());
    let clone = guard.clone();
    let mut produced = 0;
    for source in [&guard, &clone] {
        let (result, statistic) = callback(source, 40, &mut produced);
        assert!(result.is_ok());
        assert_eq!(statistic, 40);
    }
    let (result, statistic) = callback(&guard, 40, &mut produced);
    assert_eq!(result.unwrap_err().reason, "resourceout");
    assert_eq!(statistic, 40);
    assert_eq!(produced, 2, "no producer runs after the third admission");
    assert_eq!(
        owner.ticks(),
        120,
        "three costs, no fresh or double-debited owner"
    );
}

#[test]
fn kernel_plugin_tick_small_refusal_precedes_producer_and_is_sticky() {
    let owner = budget(5);
    let guard = Guard::new().with_resource(owner.clone());
    let mut produced = 0;
    let (result, statistic) = callback(&guard, 6, &mut produced);
    assert_eq!(result.unwrap_err().reason, "resourceout");
    assert_eq!(statistic, 6);
    assert_eq!(produced, 0);
    assert_eq!(owner.ticks(), 6);
    let (result, _) = callback(&guard.clone(), 0, &mut produced);
    assert_eq!(result.unwrap_err().reason, "resourceout");
    assert_eq!(produced, 0);
}

#[test]
fn kernel_plugin_tick_effects_are_statistics_and_do_not_replace_owner_debits() {
    let owner = budget(1000);
    let guard = Guard::new().with_resource(owner.clone());
    let mut terms = TermStore::new();
    let atoms = AtomTable::default();
    let mut effects = Effects::default();
    {
        let mut ctx = Ctx::new(&mut terms, None, &atoms, None, &mut effects, 0, false)
            .with_guard(Some(&guard));
        for cost in [10, 20, 30] {
            ctx.tick(cost).unwrap();
        }
    }
    assert_eq!(effects.ticks, 60);
    assert_eq!(owner.ticks(), 60);
    // Kernel aggregation moves effects into stats; it never charges again.
    let aggregated = std::mem::take(&mut effects.ticks);
    assert_eq!(aggregated, 60);
    assert_eq!(owner.ticks(), 60);
}

#[test]
fn kernel_plugin_tick_resource_cancel_keeps_original_flag_and_stop_reason() {
    let flag = Arc::new(AtomicBool::new(false));
    let mut owner = budget(1000);
    owner.set_cancel(Some(flag.clone()));
    let guard = Guard::new().with_resource(owner.clone());
    let mut produced = 0;
    assert!(callback(&guard, 1, &mut produced).0.is_ok());
    flag.store(true, Ordering::Relaxed);
    assert_eq!(
        callback(&guard, 1, &mut produced).0.unwrap_err().reason,
        "interrupted"
    );
    flag.store(false, Ordering::Relaxed);
    assert_eq!(
        callback(&guard.clone(), 1, &mut produced)
            .0
            .unwrap_err()
            .reason,
        "interrupted"
    );
    assert!(
        !flag.load(Ordering::Relaxed),
        "the adapter does not alter caller flags"
    );
    assert_eq!(produced, 1);
}

#[test]
fn kernel_plugin_tick_external_cancel_latches_across_callbacks_without_cancelling_owner() {
    let flag = Arc::new(AtomicBool::new(true));
    let owner = budget(1000);
    let guard = Guard::new()
        .with_resource(owner.clone())
        .with_cancel(flag.clone());
    let mut produced = 0;
    assert_eq!(
        callback(&guard, 64, &mut produced).0.unwrap_err().reason,
        "interrupted"
    );
    flag.store(false, Ordering::Relaxed);
    assert_eq!(
        callback(&guard.clone(), 1, &mut produced)
            .0
            .unwrap_err()
            .reason,
        "interrupted"
    );
    assert_eq!(produced, 0);
    assert_eq!(
        owner.ticks(),
        65,
        "even a latched adapter offers each cost to the original owner"
    );
    assert_eq!(
        owner.exhausted(),
        None,
        "external refusal never mutates resource flags"
    );
}

#[test]
fn kernel_plugin_tick_external_deadline_preserves_precedence_and_cannot_be_renewed() {
    let owner = budget(1);
    let guard = Guard::new()
        .with_resource(owner.clone())
        .with_deadline(Some(Instant::now()));
    let mut produced = 0;
    let (result, _) = callback(&guard, 64, &mut produced);
    assert_eq!(
        result.unwrap_err().reason,
        "timeout",
        "the old external deadline poll precedes the newly exhausted allowance"
    );
    assert_eq!(owner.ticks(), 64);
    let cleared = guard.clone().with_deadline(None);
    assert_eq!(
        callback(&cleared, 1, &mut produced).0.unwrap_err().reason,
        "timeout"
    );
    assert_eq!(produced, 0);
}

#[test]
fn kernel_plugin_tick_external_stop_predicate_and_original_poll_stride_are_preserved() {
    let calls = Arc::new(AtomicUsize::new(0));
    let stopped = Arc::new(AtomicBool::new(false));
    let count = calls.clone();
    let flag = stopped.clone();
    let owner = budget(1000);
    let guard = Guard::new().with_resource(owner).with_stop(move || {
        count.fetch_add(1, Ordering::Relaxed);
        flag.load(Ordering::Relaxed)
    });
    let mut terms = TermStore::new();
    let atoms = AtomTable::default();
    let mut effects = Effects::default();
    {
        let mut ctx = Ctx::new(&mut terms, None, &atoms, None, &mut effects, 0, false)
            .with_guard(Some(&guard));
        ctx.tick(1).unwrap();
        assert_eq!(calls.load(Ordering::Relaxed), 0);
        stopped.store(true, Ordering::Relaxed);
        assert_eq!(ctx.tick(63).unwrap_err().reason, "interrupted");
    }
    assert_eq!(calls.load(Ordering::Relaxed), 1);
    stopped.store(false, Ordering::Relaxed);
    let mut produced = 0;
    assert_eq!(
        callback(&guard, 1, &mut produced).0.unwrap_err().reason,
        "interrupted"
    );
    assert_eq!(produced, 0);
    assert_eq!(
        calls.load(Ordering::Relaxed),
        1,
        "latched refusal does not rerun caller code"
    );
}
