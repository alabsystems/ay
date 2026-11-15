// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn budget(work: usize, bytes: usize) -> ArrayReplayBudget {
    ArrayReplayBudget::with_controls(work, bytes, Box::new(|| false))
}

#[test]
fn separate_candidates_share_one_exact_allowance_without_reset() {
    let shared = budget(5, 7);
    let first = |work, bytes| shared.charge(work, bytes);
    let second = |work, bytes| shared.charge(work, bytes);
    assert!(first(2, 3));
    assert!(second(3, 4));
    assert!(shared.charge(0, 0));
    assert_eq!((shared.work_left.get(), shared.bytes_left.get()), (0, 0));
    assert!(!second(1, 0));
    assert!(!first(0, 0), "even zero debit cannot revive a refused run");
    assert!(budget(5, 7).charge(5, 7));
}

#[test]
fn independent_work_and_byte_shortfalls_are_atomic_and_sticky() {
    for debit in [(4, 0), (0, 6), (4, 6)] {
        let shared = budget(3, 5);
        assert!(!shared.charge(debit.0, debit.1));
        assert_eq!((shared.work_left.get(), shared.bytes_left.get()), (3, 5));
        assert!(!shared.charge(0, 0));
        assert!(!shared.charge(1, 1));
    }
}

#[test]
fn maximum_integer_charges_never_wrap_or_refund() {
    let shared = budget(usize::MAX, usize::MAX);
    assert!(shared.charge(usize::MAX, usize::MAX));
    assert!(!shared.charge(1, 1));
    assert!(!shared.charge(0, 0));
    assert_eq!((shared.work_left.get(), shared.bytes_left.get()), (0, 0));
    assert!(!budget(MAX_WORK, MAX_BYTES).charge(usize::MAX, 0));
    assert!(!budget(MAX_WORK, MAX_BYTES).charge(0, usize::MAX));
}

#[test]
fn stop_is_polled_at_the_exact_periodic_boundary_and_stays_latched() {
    let stop = Rc::new(Cell::new(false));
    let polls = Rc::new(Cell::new(0));
    let (observed_stop, observed_polls) = (Rc::clone(&stop), Rc::clone(&polls));
    let shared = ArrayReplayBudget::with_controls(
        POLL_INTERVAL * 2,
        POLL_INTERVAL * 2,
        Box::new(move || {
            observed_polls.set(observed_polls.get() + 1);
            observed_stop.get()
        }),
    );
    assert_eq!(polls.get(), 1, "constructor polls before admission");
    stop.set(true);
    for _ in 1..POLL_INTERVAL {
        assert!(shared.charge(1, 1));
    }
    assert_eq!(polls.get(), 1);
    assert!(!shared.charge(1, 1));
    assert_eq!(polls.get(), 2);
    stop.set(false);
    assert!(!shared.charge(0, 0));
    assert_eq!(
        polls.get(),
        2,
        "refusal cannot be undone by clearing a signal"
    );
}

#[test]
fn zero_delta_forces_initial_and_final_stop_checks() {
    let stopped = ArrayReplayBudget::with_controls(5, 7, Box::new(|| true));
    assert!(!stopped.charge(0, 0));
    assert!(!stopped.charge(1, 1));

    let stop = Rc::new(Cell::new(false));
    let observed = Rc::clone(&stop);
    let shared = ArrayReplayBudget::with_controls(5, 7, Box::new(move || observed.get()));
    assert!(shared.charge(5, 7));
    stop.set(true);
    assert!(!shared.charge(0, 0), "final admission must see a late stop");
    stop.set(false);
    assert!(!shared.charge(0, 0));
}

#[test]
fn owned_executor_controls_observe_live_interrupt_and_deadline() {
    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_solve_controls(Some(Arc::clone(&interrupt)), None);
    let shared = ArrayReplayBudget::new(&executor);
    assert!(shared.charge(1, 1));
    interrupt.store(true, Ordering::Relaxed);
    assert!(!shared.charge(0, 0));
    interrupt.store(false, Ordering::Relaxed);
    assert!(!shared.charge(0, 0));

    let fresh = ArrayReplayBudget::new(&executor);
    assert!(fresh.charge(0, 0));
    executor.set_solve_controls(None, Some(ay_core::time::Instant::now()));
    assert!(
        !fresh.charge(0, 0),
        "deadline handle remains live after capture"
    );
    executor.set_solve_controls(None, None);
    assert!(!fresh.charge(0, 0));
    let detached = ArrayReplayBudget::new(&executor);
    drop(executor);
    assert!(
        detached.charge(1, 1),
        "the budget owns its controls, not Executor"
    );
}
