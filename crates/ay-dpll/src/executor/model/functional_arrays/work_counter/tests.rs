// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Accounting controls only; no accepted native SAT or performance claim.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};
use std::thread;

use super::super::{debit_work, MAX_FUNCTIONAL_WORK};
use super::{debit, REFUSED};
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;

#[test]
fn exact_limit_and_following_zero_debits_are_successful() {
    let used = AtomicUsize::new(0);
    assert!(debit(&used, MAX_FUNCTIONAL_WORK));
    assert_eq!(used.load(Ordering::Acquire), MAX_FUNCTIONAL_WORK);
    assert!(debit(&used, 0));
    assert!(debit(&used, 0));
    assert_eq!(used.load(Ordering::Acquire), MAX_FUNCTIONAL_WORK);
}

#[test]
fn split_exact_consumption_does_not_mint_a_refusal_or_an_extra_unit() {
    let used = AtomicUsize::new(0);
    assert!(debit(&used, MAX_FUNCTIONAL_WORK - 1));
    assert!(debit(&used, 0));
    assert!(debit(&used, 1));
    assert!(debit(&used, 0));
    assert_eq!(used.load(Ordering::Acquire), MAX_FUNCTIONAL_WORK);
    assert!(!debit(&used, 1));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
}

#[test]
fn over_limit_refusal_remains_terminal_for_zero_and_positive_retry() {
    let used = AtomicUsize::new(0);
    assert!(!debit(&used, MAX_FUNCTIONAL_WORK + 1));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
    assert!(!debit(&used, 0));
    assert!(!debit(&used, 1));
    assert!(!debit(&used, usize::MAX));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
}

#[test]
fn overflow_amount_refuses_through_the_same_shared_atomic_clone() {
    let used = Arc::new(AtomicUsize::new(7));
    let copied = Arc::clone(&used);
    assert!(Arc::ptr_eq(&used, &copied));
    assert!(!debit(&copied, usize::MAX));
    assert!(!debit(&used, 0));
    assert!(!debit(&copied, 1));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
}

#[test]
fn previously_saturated_storage_normalizes_to_the_same_refusal_sentinel() {
    let used = AtomicUsize::new(usize::MAX);
    assert!(!debit(&used, 0));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
    assert!(!debit(&used, 0));
    assert!(!debit(&used, MAX_FUNCTIONAL_WORK));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
}

fn simultaneous_debits(workers: usize) -> (usize, Arc<AtomicUsize>) {
    let used = Arc::new(AtomicUsize::new(0));
    let start = Arc::new(Barrier::new(workers + 1));
    let mut children = Vec::new();
    for _ in 0..workers {
        let counter = Arc::clone(&used);
        let barrier = Arc::clone(&start);
        children.push(thread::spawn(move || {
            barrier.wait();
            debit(&counter, MAX_FUNCTIONAL_WORK / 4)
        }));
    }
    start.wait();
    let admitted = children
        .into_iter()
        .map(|child| child.join().expect("accounting worker completed"))
        .filter(|admitted| *admitted)
        .count();
    (admitted, used)
}

#[test]
fn concurrent_exact_total_is_admitted_and_zero_remains_healthy() {
    let (admitted, used) = simultaneous_debits(4);
    assert_eq!(admitted, 4);
    assert_eq!(admitted * (MAX_FUNCTIONAL_WORK / 4), MAX_FUNCTIONAL_WORK);
    assert_eq!(used.load(Ordering::Acquire), MAX_FUNCTIONAL_WORK);
    assert!(debit(&used, 0));
}

#[test]
fn concurrent_excess_cannot_admit_more_than_the_original_limit_or_rollback() {
    let (admitted, used) = simultaneous_debits(8);
    assert_eq!(admitted, 4);
    assert_eq!(admitted * (MAX_FUNCTIONAL_WORK / 4), MAX_FUNCTIONAL_WORK);
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
    assert!(!debit(&used, 0));
    assert!(!debit(&used, 1));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
}

#[test]
fn native_debit_entry_keeps_the_original_attempt_and_error_across_clones() {
    let exec = Executor::new();
    let attempt = exec.evaluation_attempt();
    let copied = attempt.clone();
    let used = attempt.functional_work_counter();
    let shared = copied.functional_work_counter();
    assert!(Arc::ptr_eq(&used, &shared));
    assert!(debit_work(&exec, &used, MAX_FUNCTIONAL_WORK).is_ok());
    assert!(debit_work(&exec, &shared, 0).is_ok());
    let expected = "functional array original cumulative work exhausted";
    assert_eq!(debit_work(&exec, &shared, 1), Err(expected.to_owned()));
    assert_eq!(debit_work(&exec, &used, 0), Err(expected.to_owned()));
    assert_eq!(debit_work(&exec, &shared, 1), Err(expected.to_owned()));
    assert_eq!(used.load(Ordering::Acquire), REFUSED);
    assert!(exec.evaluation_attempt().is_same_attempt(&attempt));
}

#[test]
fn original_evaluation_stop_is_polled_before_any_counter_update() {
    for origin in [
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::SolveDeadline,
        UnknownOrigin::MemoryBudget,
    ] {
        let exec = Executor::new();
        let used = exec.evaluation_attempt().functional_work_counter();
        used.store(7, Ordering::Release);
        exec.record_evaluation_stop(origin);
        assert_eq!(
            debit_work(&exec, &used, 0),
            Err("functional array owner interrupted".to_owned())
        );
        // The original stop admits no work; REFUSED is terminal storage.
        assert_eq!(used.load(Ordering::Acquire), REFUSED);
        assert_eq!(exec.evaluation_stop_origin(), Some(origin));
    }
}
