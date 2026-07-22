// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Startup timing regression tests for Kani Fast Priority 2.2.
//!
//! These checks measure the in-process executor startup path after parsing so
//! the timing window stays focused on solver initialization and the first
//! `check-sat`, rather than parser allocation noise.
//!
//! The release budget remains the real regression gate. Debug builds keep a
//! much wider budget so local `cargo test` runs stay useful without becoming
//! flaky on slower developer machines.

use ay::executor::Executor;
use ay::{parse, Command};
use ntest::timeout;
use std::time::{Duration, Instant};

const STARTUP_SAMPLES: usize = 9;
const STARTUP_BATCH_SIZE: u32 = 5;

fn startup_budget_qf_bv() -> Duration {
    if cfg!(debug_assertions) {
        // Raised from 50ms to 75ms to avoid flaky failures when the test
        // suite runs under heavy system load (multiple parallel workers).
        Duration::from_millis(75)
    } else {
        Duration::from_millis(10)
    }
}

fn startup_budget_sat() -> Duration {
    if cfg!(debug_assertions) {
        Duration::from_millis(10)
    } else {
        Duration::from_millis(2)
    }
}

fn burst_budget_for_instances(instances: u32) -> Duration {
    // Debug budget raised from 50ms to 100ms per instance to avoid flaky
    // failures when the test suite runs under heavy system load
    // (multiple parallel workers sharing CPU).
    let per_instance = if cfg!(debug_assertions) { 100 } else { 10 };
    Duration::from_millis(u64::from(instances) * per_instance)
}

fn parse_commands(smt: &str) -> Vec<Command> {
    parse(smt).expect("startup timing input must parse")
}

fn execute_commands(commands: &[Command]) -> Duration {
    let start = Instant::now();
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(commands)
        .expect("startup timing commands must execute successfully");
    let elapsed = start.elapsed();

    assert_eq!(
        outputs.len(),
        1,
        "startup timing workload should produce exactly one check-sat result"
    );
    assert_eq!(outputs[0], "sat", "startup timing workload must remain SAT");

    elapsed
}

fn median_startup_time(commands: &[Command]) -> Duration {
    let mut times = Vec::with_capacity(STARTUP_SAMPLES);

    // Warm up code paths before measuring steady-state startup latency.
    let _ = execute_commands(commands);

    for _ in 0..STARTUP_SAMPLES {
        let batch_start = Instant::now();
        for _ in 0..STARTUP_BATCH_SIZE {
            let _ = execute_commands(commands);
        }
        times.push(batch_start.elapsed() / STARTUP_BATCH_SIZE);
    }

    times.sort_unstable();
    times[STARTUP_SAMPLES / 2]
}

/// Regression test: QF_BV startup must remain within the configured budget.
#[test]
#[timeout(10000)]
fn qf_bv_startup_within_budget() {
    let smt =
        "(set-logic QF_BV)(declare-const x (_ BitVec 32))(assert (bvugt x #x00000000))(check-sat)";
    let commands = parse_commands(smt);
    let median = median_startup_time(&commands);
    let max_allowed = startup_budget_qf_bv();

    assert!(
        median <= max_allowed,
        "Startup time regression: median {}us exceeds {:?} budget",
        median.as_micros(),
        max_allowed
    );
}

/// Regression test: propositional startup should remain within the tighter budget.
#[test]
#[timeout(10000)]
fn propositional_startup_within_budget() {
    let smt =
        "(set-logic QF_BOOL)(declare-const p1 Bool)(declare-const p2 Bool)(assert (or p1 p2))(check-sat)";
    let commands = parse_commands(smt);
    let median = median_startup_time(&commands);
    let max_allowed = startup_budget_sat();

    assert!(
        median <= max_allowed,
        "Propositional startup time regression: median {}us exceeds {:?} budget",
        median.as_micros(),
        max_allowed
    );
}

/// Test repeated startup bursts to simulate many short-lived solver instances.
#[test]
#[timeout(10000)]
fn incremental_startup_burst_within_budget() {
    let smt =
        "(set-logic QF_BV)(declare-const x (_ BitVec 32))(assert (bvugt x #x00000000))(check-sat)";
    let commands = parse_commands(smt);
    let num_instances = 10_u32;

    // Warm up once so the burst check measures repeated instance startup.
    let _ = execute_commands(&commands);
    let start = Instant::now();

    for _ in 0..num_instances {
        let _ = execute_commands(&commands);
    }

    let total = start.elapsed();
    let max_allowed = burst_budget_for_instances(num_instances);

    assert!(
        total <= max_allowed,
        "Creating {} solver instances took {}ms, exceeds {:?} budget",
        num_instances,
        total.as_millis(),
        max_allowed
    );
}
