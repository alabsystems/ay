// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cancellation responsiveness tests for CHC engines.
//!
//! These tests verify that each engine responds promptly to cancellation requests.
//! Per the portfolio cancellation contract (the development design notes),
//! engines must poll CancellationToken frequently enough that they return within a bounded
//! time after cancellation.
//!
//! We test "pre-cancellation": cancel the token BEFORE starting the engine, then verify
//! the engine detects the cancelled state and returns Unknown almost immediately.
//!
//! Part of #1005.

use ay_chc::{
    testing, BmcConfig, CancellationToken, ChcEngineResult, ChcParser, PdkindResult, PdrConfig,
    PdrResult,
};
use ntest::timeout;
use std::time::{Duration, Instant};

/// A simple CHC problem - the specific problem doesn't matter for cancellation tests
/// since we cancel before the engine starts.
const SIMPLE_INPUT: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert
  (forall ((x Int))
    (=>
      (= x 0)
      (Inv x))))
(assert
  (forall ((x Int) (y Int))
    (=>
      (and (Inv x) (= y (+ x 1)) (< x 100))
      (Inv y))))
(assert
  (forall ((x Int))
    (=>
      (and (Inv x) (< x 0))
      false)))
(check-sat)
(exit)
"#;

/// Max time we allow an engine to take with a pre-cancelled token.
/// Since we cancel before the engine starts, it should detect cancellation and
/// return almost immediately (within the first loop iteration).
/// Note: Use generous timeout to avoid flaky failures on loaded CI systems (#1585).
const MAX_PRECANCELLED_LATENCY: Duration = Duration::from_secs(2);

/// Test that PDR detects pre-cancellation and returns quickly.
/// Note: PDR may return Safe if it finds a trivial invariant before entering the main loop.
/// This is acceptable - the key is that it returns promptly, not that it returns Unknown.
#[test]
#[timeout(5_000)]
fn pdr_responds_to_precancellation() {
    let problem = ChcParser::parse(SIMPLE_INPUT).unwrap();
    let token = CancellationToken::new();

    // Cancel BEFORE starting the engine
    token.cancel();

    let mut config = PdrConfig::default();
    config.max_frames = 100;
    config.max_iterations = 10_000;
    config.max_obligations = 100_000;
    config.verbose = false;
    config.cancellation_token = Some(token);

    let start = Instant::now();
    let mut solver = testing::new_pdr_solver(problem, config);
    let result = solver.solve();
    let latency = start.elapsed();

    // Either Unknown (detected cancellation) or Safe/Unsafe (solved trivially before loop)
    // All are acceptable - the key is responding promptly
    assert!(
        matches!(
            result,
            PdrResult::Unknown | PdrResult::Safe(_) | PdrResult::Unsafe(_)
        ),
        "expected Unknown, Safe, or Unsafe with pre-cancelled token, got {result:?}"
    );

    // Verify the engine returned quickly
    assert!(
        latency < MAX_PRECANCELLED_LATENCY,
        "PDR took {latency:?} to respond, expected < {MAX_PRECANCELLED_LATENCY:?}"
    );
}

/// Test that BMC detects pre-cancellation and returns quickly.
/// Note: BMC checks cancellation at the start of its loop, so it should always return Unknown.
#[test]
#[timeout(5_000)]
fn bmc_responds_to_precancellation() {
    let problem = ChcParser::parse(SIMPLE_INPUT).unwrap();
    let token = CancellationToken::new();

    // Cancel BEFORE starting the engine
    token.cancel();

    let config = BmcConfig::with_engine_config(10_000, false, Some(token));

    let start = Instant::now();
    let solver = testing::new_bmc_solver(problem, config);
    let result = solver.solve();
    let latency = start.elapsed();

    // BMC checks cancellation at the very start of its loop (before any work),
    // so it should always return Unknown when pre-cancelled
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "expected Unknown with pre-cancelled token, got {result:?}"
    );

    // Verify the engine returned quickly
    assert!(
        latency < MAX_PRECANCELLED_LATENCY,
        "BMC took {latency:?} to detect pre-cancellation, expected < {MAX_PRECANCELLED_LATENCY:?}"
    );
}

/// Test that PDKIND detects pre-cancellation and returns quickly.
/// Note: PDKIND may return Safe/Unsafe if it solves trivial cases before checking cancellation.
#[test]
#[timeout(5_000)]
fn pdkind_responds_to_precancellation() {
    let problem = ChcParser::parse(SIMPLE_INPUT).unwrap();
    let token = CancellationToken::new();

    // Cancel BEFORE starting the engine
    token.cancel();

    let start = Instant::now();
    let solver = testing::pdkind_solver_cancellation(problem, token);
    let result = solver.solve();
    let latency = start.elapsed();

    // Either Unknown (detected cancellation) or Safe/Unsafe (solved trivially before loop)
    // All are acceptable - the key is responding promptly
    assert!(
        matches!(
            result,
            PdkindResult::Unknown | PdkindResult::Safe(_) | PdkindResult::Unsafe(_)
        ),
        "expected Unknown, Safe, or Unsafe with pre-cancelled token, got {result:?}"
    );

    // Verify the engine returned quickly
    assert!(
        latency < MAX_PRECANCELLED_LATENCY,
        "PDKIND took {latency:?} to respond, expected < {MAX_PRECANCELLED_LATENCY:?}"
    );
}
