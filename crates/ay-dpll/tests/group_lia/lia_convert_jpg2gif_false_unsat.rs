// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for false UNSAT on convert-jpg2gif QF_LIA benchmarks.
//!
//! AY returns UNSAT on satisfiable benchmarks involving:
//! - 32-bit integer arithmetic (coefficients up to 2^32)
//! - Equality atoms that become disequalities under certain Boolean assignments
//! - Branch-and-bound with disequality splits excluding value 0
//!
//! The convert-jpg2gif benchmarks simulate sequential equivalence checking
//! of 32-bit circuits. Z3 confirms SAT. AY falsely returns UNSAT after 6
//! disequality splits. Regression from commit 4718b6cbb (baseline: timeout)
//! to current (false UNSAT).
//!
//! Root cause (P31-476 investigation): the LIA outer loop's disequality split
//! mechanism creates conditional clauses (e.g., `(= sigma_5 sigma_9) OR sigma_5 >= 1`)
//! that interact with the Dioph solver's bound propagation. When the Dioph processes
//! derived equalities (sigma_5 = sigma_9 from ay = z8 via multiplication equations)
//! with tightened bounds (sigma_5 forced to [1,1] by an active conditional clause),
//! it propagates sigma_5 = 1, sigma_9 = 1, causing ay = z8 = 2^32 > bound violations.
//! The CDCL fails to find the satisfying both-equalities-TRUE assignment where
//! all conditional clauses are trivially satisfied and the all-zeros model works.
//! See #4830 for tracking.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::time::Duration;

fn solve_with_timeout(smt: &str, timeout_ms: u64) -> String {
    let commands = match parse(smt) {
        Ok(commands) => commands,
        Err(_) => return "error".to_string(),
    };

    let mut exec = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));

    let (cancel_tx, cancel_rx) = mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx
            .recv_timeout(Duration::from_millis(timeout_ms))
            .is_err()
        {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    let result = exec.execute_all(&commands);
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    if timed_out {
        "timeout".to_string()
    } else {
        match result {
            Ok(outputs) => outputs.join("\n"),
            Err(_) => "error".to_string(),
        }
    }
}

/// Minimal test: 32-bit carry-chain equality that AY falsely reports UNSAT.
///
/// Models a single 32-bit addition with carry: z = x + y where:
///   z_full = sigma * 2^32 + z_sum  (sigma is the carry)
///   z_full = x + y
///   0 <= sigma <= 1
///   0 <= z_sum < 2^32
///   0 <= x, y < 2^32
///
/// Plus an equality atom (= z_sum x) that the SAT solver may negate
/// into a disequality, triggering disequality splits.
///
/// Expected: SAT (e.g., x=0, y=0, sigma=0, z_sum=0, z_full=0)
#[test]
#[timeout(10_000)]
fn test_32bit_carry_chain_equality_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z_sum Int)
        (declare-const z_full Int)
        (declare-const sigma Int)
        ; Bounds: unsigned 32-bit values
        (assert (<= 0 x))
        (assert (<= x 4294967295))
        (assert (<= 0 y))
        (assert (<= y 4294967295))
        (assert (<= 0 z_sum))
        (assert (<= z_sum 4294967295))
        ; Carry bit
        (assert (<= 0 sigma))
        (assert (<= sigma 1))
        ; z_full = x + y
        (assert (= z_full (+ x y)))
        ; z_full = sigma * 2^32 + z_sum
        (assert (= z_full (+ (* sigma 4294967296) z_sum)))
        ; Add an equality that creates a disequality atom
        (assert (or (= z_sum x) (<= z_sum y)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // This is SAT (e.g., x=0, y=0, sigma=0, z_sum=0, z_full=0)
    assert_eq!(
        result.trim(),
        "sat",
        "32-bit carry chain with equality should be SAT"
    );
}

/// Test from the convert-jpg2gif benchmark family: multi-variable disequality
/// with 32-bit arithmetic. The DPLL(T) loop must not falsely conclude UNSAT
/// from accumulated disequality splits.
#[test]
#[timeout(10_000)]
fn test_multi_sigma_32bit_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const ay_31_0 Int)
        (declare-const z8_31_0 Int)
        (declare-const sigma_5 Int)
        (declare-const sigma_9 Int)
        ; Bounds: 32-bit unsigned
        (assert (<= 0 ay_31_0))
        (assert (<= ay_31_0 4294967295))
        (assert (<= 0 z8_31_0))
        (assert (<= z8_31_0 4294967295))
        ; Sigma bounds (carry bits)
        (assert (<= 0 sigma_5))
        (assert (<= sigma_5 1))
        (assert (<= 0 sigma_9))
        (assert (<= sigma_9 1))
        ; 32-bit addition constraint: ay = sigma_5 * 2^32 + some_result
        (assert (= ay_31_0 (* sigma_5 4294967296)))
        ; Second constraint involving z8
        (assert (= z8_31_0 (* sigma_9 4294967296)))
        ; Equality atoms that may become disequalities
        (assert (or (= ay_31_0 z8_31_0) (= sigma_5 sigma_9)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // SAT: all zeros satisfies this
    assert_eq!(
        result.trim(),
        "sat",
        "Multi-sigma 32-bit with equalities should be SAT"
    );
}

/// Direct test using the convert-jpg2gif-query-1168 benchmark file.
/// This benchmark is status=sat in SMT-LIB metadata, confirmed by Z3.
/// AY must not return UNSAT.
#[test]
#[timeout(30_000)]
fn test_convert_jpg2gif_query_1168_not_unsat() {
    let benchmark_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/smtcomp/QF_LIA/convert-jpg2gif-query-1168.smt2"
    );
    let smt = match std::fs::read_to_string(benchmark_path) {
        Ok(smt) => smt,
        Err(err) => {
            // Keep this test behaviorally meaningful even when SMT-COMP corpora are
            // absent in CI/local checkouts.
            eprintln!(
                "Benchmark file not found at {benchmark_path} ({err}); \
                 using embedded convert-jpg2gif-family fallback"
            );
            r#"
                (set-logic QF_LIA)
                (declare-const ay_31_0 Int)
                (declare-const z8_31_0 Int)
                (declare-const sigma_5 Int)
                (declare-const sigma_9 Int)
                ; 32-bit style bounds
                (assert (<= 0 ay_31_0))
                (assert (<= ay_31_0 4294967295))
                (assert (<= 0 z8_31_0))
                (assert (<= z8_31_0 4294967295))
                (assert (<= 0 sigma_5))
                (assert (<= sigma_5 1))
                (assert (<= 0 sigma_9))
                (assert (<= sigma_9 1))
                ; Carry-style equations
                (assert (= ay_31_0 (* sigma_5 4294967296)))
                (assert (= z8_31_0 (* sigma_9 4294967296)))
                ; Equality atom that may branch to disequality in CDCL(T)
                (assert (or (= ay_31_0 z8_31_0) (= sigma_5 sigma_9)))
                (check-sat)
            "#
            .to_owned()
        }
    };
    // The full benchmark can exceed debug test-time budgets. Treat timeout as
    // incomplete (sound) and only fail on a definite false UNSAT.
    let result = solve_with_timeout(&smt, 10_000);
    let result = result.lines().next().unwrap_or("").trim();
    // The benchmark is SAT. AY must not return UNSAT (false UNSAT = soundness bug).
    // Acceptable results: sat/unknown/timeout (incomplete but sound).
    assert_ne!(
        result, "unsat",
        "convert-jpg2gif-query-1168 is SAT (confirmed by Z3 and SMT-LIB metadata). \
         AY returning UNSAT is a soundness bug. See #4786."
    );
}
