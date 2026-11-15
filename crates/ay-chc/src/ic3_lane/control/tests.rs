// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

#[test]
fn refused_callback_cannot_resume_or_run_twice() {
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        calls.get() != 1
    };
    let control = Control::new(Instant::now() + Duration::from_secs(60), &mut callback);
    assert_eq!(control.poll(), None);
    assert!(control.stopped());
    assert_eq!(control.poll(), None);
    assert_eq!(calls.get(), 1);
}

#[test]
fn callback_panic_keeps_attempt_stopped() {
    let mut callback = || panic!("test callback");
    let control = Control::new(Instant::now() + Duration::from_secs(60), &mut callback);
    assert!(catch_unwind(AssertUnwindSafe(|| control.poll())).is_err());
    assert!(control.stopped());
    assert_eq!(control.poll(), None);
}

#[test]
fn reentrant_refusal_cannot_be_ignored_by_true_outer_callback() {
    let slot = Cell::new(None::<&Control<'_>>);
    let mut callback = || {
        assert_eq!(slot.get().expect("installed control").poll(), None);
        true
    };
    let control = Control::new(Instant::now() + Duration::from_secs(60), &mut callback);
    slot.set(Some(&control));
    assert_eq!(control.poll(), None);
    assert!(control.stopped());
    slot.set(None);
}

#[test]
fn clock_is_checked_before_and_after_even_true_callback() {
    let start = Instant::now();
    let deadline = start + Duration::from_secs(60);
    let clock_value = Cell::new(start);
    let clock = || clock_value.get();
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        clock_value.set(deadline);
        true
    };
    let control = Control::with_clock(deadline, &mut callback, &clock);
    assert_eq!(control.poll(), None);
    assert_eq!(calls.get(), 1);
    clock_value.set(start);
    assert_eq!(control.poll(), None);
    assert_eq!(calls.get(), 1);

    clock_value.set(deadline);
    let mut never_called = || panic!("expired before callback");
    let expired = Control::with_clock(deadline, &mut never_called, &clock);
    assert_eq!(expired.poll(), None);
}

#[test]
fn local_rung_expiry_preserves_parent_but_parent_refusal_stops_fresh_rung() {
    let start = Instant::now();
    let now = Cell::new(start);
    let clock = || now.get();
    let live = Cell::new(true);
    let mut parent_callback = || live.get();
    let parent = Control::with_clock(
        start + Duration::from_secs(60),
        &mut parent_callback,
        &clock,
    );
    let mut first_callback = || parent.poll().is_some();
    let first = Control::with_clock(start + Duration::from_secs(1), &mut first_callback, &clock);
    now.set(start + Duration::from_secs(2));
    assert_eq!(first.poll(), None);
    assert!(!parent.stopped());
    let mut second_callback = || parent.poll().is_some();
    let second = Control::with_clock(parent.deadline(), &mut second_callback, &clock);
    assert_eq!(second.poll(), Some(()));
    live.set(false);
    assert_eq!(second.poll(), None);
    live.set(true);
    let mut third_callback = || parent.poll().is_some();
    let third = Control::with_clock(parent.deadline(), &mut third_callback, &clock);
    assert_eq!(third.poll(), None);
}
