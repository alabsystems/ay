// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn isolated(name: &str) -> bool {
    ay_test_support::isolated_test::run_alone(module_path!(), name).expect("fresh process")
}

#[test]
fn held_spares_force_actual_caller_inline_work() {
    if !isolated("held_spares_force_actual_caller_inline_work") {
        return;
    }
    let caller = ComputeScope::enter().expect("caller");
    let mut retained = Vec::new();
    while let Some(unit) = caller.try_extra().expect("spare") {
        retained.push(unit);
    }
    let thread = std::thread::current().id();
    let mut workers = Workers::acquire(8, || false)
        .expect("budget")
        .expect("ready");
    assert_eq!(workers.count(), 1);
    let report = workers
        .run(
            vec![41],
            "milp-inline",
            None,
            |input| {
                assert_eq!(std::thread::current().id(), thread);
                assert!(ay_sys::compute_budget::try_extra()
                    .expect("entered unit")
                    .is_none());
                input + 1
            },
            |_| panic!("no worker failed"),
        )
        .expect("run");
    assert_eq!(report.results, vec![42]);
    assert_eq!(report.spawn_failures + report.panics, 0);
    drop(workers);
    assert!(caller
        .try_extra()
        .expect("all original spares still retained")
        .is_none());
}

#[test]
fn original_cancellation_refuses_before_worker_construction() {
    let mut polled = false;
    assert!(Workers::acquire(8, || {
        polled = true;
        true
    })
    .expect("poll")
    .is_none());
    assert!(polled);
}

struct Input {
    index: usize,
    dropped_outside_unit: Arc<AtomicBool>,
}

impl Drop for Input {
    fn drop(&mut self) {
        if ay_sys::compute_budget::try_extra().is_err() {
            self.dropped_outside_unit.store(true, Ordering::SeqCst);
        }
    }
}

#[test]
fn worker_unwind_keeps_input_cleanup_inside_actual_unit() {
    if !isolated("worker_unwind_keeps_input_cleanup_inside_actual_unit") {
        return;
    }
    let mut workers = Workers::acquire(2, || false)
        .expect("budget")
        .expect("ready");
    let count = workers.count();
    let outside = Arc::new(AtomicBool::new(false));
    let failed = AtomicBool::new(false);
    let inputs = (0..count)
        .map(|index| Input {
            index,
            dropped_outside_unit: Arc::clone(&outside),
        })
        .collect();
    let report = workers
        .run(
            inputs,
            "milp-unwind",
            None,
            |input| {
                // On a one-CPU host the caller is the only possible worker.
                if input.index == count - 1 {
                    panic!("owned worker panic");
                }
                input.index
            },
            |_| failed.store(true, Ordering::SeqCst),
        )
        .expect("run");
    assert_eq!(report.panics, 1);
    assert_eq!(report.results.len(), count - 1);
    assert!(failed.load(Ordering::SeqCst));
    assert!(!outside.load(Ordering::SeqCst));
}
