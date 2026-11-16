// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

fn past() -> Instant {
    Instant::now().checked_sub(Duration::from_secs(1)).unwrap()
}

fn future() -> Instant {
    Instant::now()
        .checked_add(Duration::from_secs(600))
        .unwrap()
}

#[test]
fn work_allowance_is_shared_across_phases_and_zero_poll_cannot_resume_refusal() {
    let executor = Executor::new();
    let mut control = Control::new(&executor);
    assert!(control.poll(3, 0));
    assert!(control.poll(MAX_WORK - 3, 0));
    assert!(control.poll(0, 0));
    assert_eq!(control.work, MAX_WORK);
    assert!(!control.poll(1, 0));
    assert!(control.stopped());
    assert!(!control.poll(0, 0));
    assert!(Control::new(&executor).poll(MAX_WORK, 0));
}

#[test]
fn charged_byte_allowance_is_cumulative_and_has_an_exact_boundary() {
    let executor = Executor::new();
    let mut control = Control::new(&executor);
    assert!(control.poll(0, 13));
    assert!(control.poll(0, MAX_CHARGED_BYTES - 13));
    assert!(control.poll(0, 0));
    assert_eq!(control.charged_bytes, MAX_CHARGED_BYTES);
    assert!(!control.poll(0, 1));
    assert!(control.stopped());
    assert!(!control.poll_terms(&executor.ctx.terms, 0, 0));
    assert!(Control::new(&executor).poll(0, MAX_CHARGED_BYTES));
}

#[test]
fn arithmetic_overflow_refuses_before_callback_and_does_not_wrap_the_ledger() {
    let executor = Executor::new();
    for (work, bytes) in [(usize::MAX, 0), (0, usize::MAX)] {
        let calls = Cell::new(0);
        let mut callback = |_, _| {
            calls.set(calls.get() + 1);
            true
        };
        let mut control = Control::with_progress(&executor, &mut callback);
        assert!(control.poll(1, 1));
        assert!(!control.poll(work, bytes));
        assert_eq!(calls.get(), 1);
        assert_eq!((control.work, control.charged_bytes), (1, 1));
        assert!(!control.poll(0, 0));
        assert_eq!(calls.get(), 1);
    }
}

#[test]
fn one_callback_refusal_is_terminal_but_a_fresh_attempt_can_retry() {
    let executor = Executor::new();
    let calls = Cell::new(0);
    let mut callback = |work, bytes| {
        assert_eq!((work, bytes), (2, 3));
        calls.set(calls.get() + 1);
        calls.get() != 1
    };
    {
        let mut control = Control::with_progress(&executor, &mut callback);
        assert!(!control.poll(2, 3));
        assert!(control.stopped());
        assert!(!control.poll(0, 0));
        assert!(!control.poll_terms(&executor.ctx.terms, 0, 0));
        assert_eq!(calls.get(), 1);
    }
    let mut retry = Control::with_progress(&executor, &mut callback);
    assert!(retry.poll(2, 3));
    assert_eq!(calls.get(), 2);
}

#[test]
fn caught_callback_panic_cannot_resume_the_same_attempt() {
    let executor = Executor::new();
    let calls = Cell::new(0);
    let mut callback = |_, _| {
        calls.set(calls.get() + 1);
        assert!(calls.get() != 1, "SOS callback panic");
        true
    };
    {
        let mut control = Control::with_progress(&executor, &mut callback);
        let panic = catch_unwind(AssertUnwindSafe(|| control.poll(1, 2)))
            .expect_err("the control does not swallow the original panic");
        assert_eq!(panic.downcast_ref::<&str>(), Some(&"SOS callback panic"));
        assert!(control.stopped());
        assert!(!control.poll(0, 0));
        assert!(!control.poll_terms(&executor.ctx.terms, 0, 0));
        assert_eq!(calls.get(), 1);
    }
    assert!(Control::with_progress(&executor, &mut callback).poll(0, 0));
    assert_eq!(calls.get(), 2);
}

#[test]
fn either_expired_deadline_refuses_before_the_callback() {
    for certification in [false, true] {
        let executor = Executor::new();
        executor.solve_deadline.set(Some(future()));
        executor.certification_deadline.set(Some(future()));
        if certification {
            executor.certification_deadline.set(Some(past()));
        } else {
            executor.solve_deadline.set(Some(past()));
        }
        let mut callback = |_, _| panic!("expired control must not invoke the callback");
        let mut control = Control::with_progress(&executor, &mut callback);
        assert!(!control.poll(0, 0));
        assert!(control.stopped());
    }
}

#[test]
fn clearing_or_extending_deadline_handles_does_not_renew_the_original_attempt() {
    for replacement in [None, Some(future())] {
        let executor = Executor::new();
        executor.certification_deadline.set(Some(past()));
        let mut control = Control::new(&executor);
        // Change the cells before the first poll: there has not yet been a
        // refusal to latch, so only the original absolute deadline closes this.
        executor.solve_deadline.set(replacement);
        executor.certification_deadline.set(replacement);
        assert!(!control.poll(0, 0));
        assert!(Control::new(&executor).poll(0, 0));
    }
}

#[test]
fn callback_true_cannot_publish_past_a_newly_tightened_deadline() {
    for certification in [false, true] {
        let executor = Executor::new();
        let cell = if certification {
            executor.certification_deadline.clone()
        } else {
            executor.solve_deadline.clone()
        };
        let calls = Cell::new(0);
        let mut callback = |_, _| {
            calls.set(calls.get() + 1);
            cell.set(Some(past()));
            true
        };
        let mut control = Control::with_progress(&executor, &mut callback);
        assert!(!control.poll(0, 0));
        assert!(control.stopped());
        cell.set(None);
        assert!(!control.poll(0, 0));
        assert_eq!(calls.get(), 1);
    }
}

#[test]
fn interrupt_is_observed_after_callback_and_its_reset_cannot_resume() {
    let mut executor = Executor::new();
    let flag = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&flag));
    let mut callback = |_, _| {
        flag.store(true, Ordering::Relaxed);
        true
    };
    let mut control = Control::with_progress(&executor, &mut callback);
    assert!(!control.poll(0, 0));
    assert!(control.stopped());
    assert!(
        flag.load(Ordering::Relaxed),
        "control never resets the caller flag"
    );
    flag.store(false, Ordering::Relaxed);
    assert!(!control.poll(0, 0));
    assert!(Control::new(&executor).poll(0, 0));
}

#[test]
fn owned_handles_allow_term_mutation_and_observe_live_deadline_changes() {
    let mut executor = Executor::new();
    let mut control = Control::new(&executor);
    let _ = executor
        .ctx
        .terms
        .mk_var("after_control", ay_core::Sort::Real);
    assert!(control.poll_terms(&executor.ctx.terms, 1, 1));
    executor.solve_deadline.set(Some(past()));
    assert!(!control.poll_terms(&executor.ctx.terms, 0, 0));
    assert!(control.stopped());
}

#[test]
fn a_store_ceiling_is_sampled_at_the_boundary_and_retained_across_phases() {
    let mut executor = Executor::new();
    executor.set_term_memory_limit(Some(0));
    let mut control = Control::new(&executor);
    // No immutable arena is retained in the controller: ordinary callback
    // polling alone cannot claim to sample a subsequently mutated term store.
    assert!(control.poll(0, 0));
    assert!(!control.poll_terms(&executor.ctx.terms, 0, 0));
    assert!(control.stopped());
    executor.set_term_memory_limit(None);
    assert!(!control.poll_terms(&executor.ctx.terms, 0, 0));
    assert!(Control::new(&executor).poll_terms(&executor.ctx.terms, 0, 0));
}

struct ResetMemorySignal;

impl Drop for ResetMemorySignal {
    fn drop(&mut self) {
        ay_sys::force_process_memory_exceeded_for_testing(false);
    }
}

#[test]
fn process_memory_is_sampled_on_entry_and_at_the_exact_periodic_boundary() {
    let _reset = ResetMemorySignal;
    let executor = Executor::new();
    ay_sys::force_process_memory_exceeded_for_testing(true);
    assert!(!Control::new(&executor).poll(0, 0));
    ay_sys::force_process_memory_exceeded_for_testing(false);

    let mut control = Control::new(&executor);
    assert!(control.poll(0, 0));
    assert_eq!(control.memory_polls_left, MEMORY_POLL_INTERVAL - 1);
    ay_sys::force_process_memory_exceeded_for_testing(true);
    for remaining in (0..MEMORY_POLL_INTERVAL - 1).rev() {
        assert!(control.poll(0, 0));
        assert_eq!(control.memory_polls_left, remaining);
    }
    assert!(!control.poll(0, 0));
    assert!(control.stopped());
    ay_sys::force_process_memory_exceeded_for_testing(false);
    assert!(!control.poll(0, 0));
    assert!(Control::new(&executor).poll(0, 0));
}

#[test]
fn arena_boundaries_and_callbacks_force_memory_samples_between_periodic_polls() {
    let _reset = ResetMemorySignal;
    let executor = Executor::new();
    let mut control = Control::new(&executor);
    assert!(control.poll(0, 0));
    ay_sys::force_process_memory_exceeded_for_testing(true);
    assert!(!control.poll_terms(&executor.ctx.terms, 0, 0));
    ay_sys::force_process_memory_exceeded_for_testing(false);

    let calls = Cell::new(0);
    let mut callback = |_, _| {
        calls.set(calls.get() + 1);
        if calls.get() == 2 {
            ay_sys::force_process_memory_exceeded_for_testing(true);
        }
        true
    };
    let mut control = Control::with_progress(&executor, &mut callback);
    assert!(control.poll(0, 0));
    assert!(!control.poll(0, 0));
    assert_eq!(calls.get(), 2);
    ay_sys::force_process_memory_exceeded_for_testing(false);
    assert!(!control.poll(0, 0));
    assert_eq!(calls.get(), 2);
}
