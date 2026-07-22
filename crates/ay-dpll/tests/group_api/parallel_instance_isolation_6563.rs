// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for issue #6563: per-instance term memory isolation.
//!
//! Before the fix, `GLOBAL_TERM_BYTES` was a process-wide `AtomicUsize` counter.
//! When multiple `Solver` instances ran concurrently in the same process, their
//! combined term allocation could exceed `DEFAULT_TERM_MEMORY_LIMIT` (4GB), causing
//! `global_memory_exceeded()` to return `true` for both instances even though neither
//! individually exceeded the budget. This produced non-deterministic `Unknown` results.
//!
//! The fix adds `instance_term_bytes` to `TermStore` so each solver tracks its own
//! allocation independently.

use ntest::timeout;
use std::thread;

/// Public API solvers are commonly moved into watchdog/worker threads by
/// downstream tools. Keep that contract compile-checked.
#[test]
fn test_api_solver_is_send_for_downstream_workers() {
    fn assert_send<T: Send>() {}

    assert_send::<ay_dpll::api::Solver>();
}

/// Four solver instances in parallel threads must all produce correct results,
/// not `Unknown` from cross-instance budget interference.
#[test]
#[timeout(30000)]
fn test_parallel_solvers_no_cross_instance_interference_6563() {
    let handles: Vec<_> = (0..4)
        .map(|i| {
            thread::spawn(move || {
                let smt = format!(
                    r#"
                    (set-logic QF_LIA)
                    (declare-const x Int)
                    (declare-const y Int)
                    (assert (> x {}))
                    (assert (< y {}))
                    (assert (= (+ x y) {}))
                    (check-sat)
                "#,
                    i,
                    100 + i,
                    50 + i
                );
                let output = crate::common::solve(&smt);
                let result = crate::common::sat_result(&output).unwrap_or("no result");
                assert_eq!(
                    result, "sat",
                    "Thread {i}: expected sat, got {result} (cross-instance interference?)"
                );
            })
        })
        .collect();

    for h in handles {
        h.join().expect("Thread panicked");
    }
}

/// Verify that `instance_term_bytes` tracks per-instance, not global.
/// Create two solvers, add terms to each, verify each tracks independently.
#[test]
#[timeout(10000)]
fn test_instance_term_bytes_independent_tracking_6563() {
    use ay_dpll::api::{Logic, Solver, Sort};

    #[allow(deprecated)]
    let mut solver_a = Solver::new(Logic::QfLia);
    #[allow(deprecated)]
    let mut solver_b = Solver::new(Logic::QfLia);

    // Create some terms in solver A only
    for i in 0..100 {
        let name = format!("a_{i}");
        let _ = solver_a.declare_const(&name, Sort::Int);
    }

    // Solver B should have fewer instance bytes than A (only built-in terms)
    let bytes_a = solver_a.instance_term_bytes();
    let bytes_b = solver_b.instance_term_bytes();

    assert!(
        bytes_a > bytes_b,
        "Solver A ({bytes_a} bytes) should have more instance bytes than B ({bytes_b} bytes)"
    );

    // Now add terms to solver B
    for i in 0..200 {
        let name = format!("b_{i}");
        let _ = solver_b.declare_const(&name, Sort::Int);
    }

    let bytes_a_after = solver_a.instance_term_bytes();
    let bytes_b_after = solver_b.instance_term_bytes();

    // Solver A's count should not have changed
    assert_eq!(
        bytes_a, bytes_a_after,
        "Solver A's instance bytes should not change when B allocates"
    );

    // Solver B should now have more
    assert!(
        bytes_b_after > bytes_a_after,
        "Solver B ({bytes_b_after}) should have more instance bytes than A ({bytes_a_after})"
    );
}
