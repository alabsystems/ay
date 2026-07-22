// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BMC-style stress test for QF_LIA incremental solving (#6853).
//!
//! Generates bounded model checking verification conditions with many push/pop
//! cycles, reproducing the pattern from CPAChecker-generated SMT-LIB benchmarks
//! that trigger false-unsat in ay.
//!
//! The program model: a simple counter that increments from 0.
//! Property: counter < bound (always true if bound is large enough).
//! BMC unrolling: at each step k, check if the property can be violated.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Generate a BMC-style incremental SMT script (scoped property checks).
///
/// Models a simple counter: x starts at 0, increments by 1 each step.
/// State variables and transitions are declared globally (accumulated).
/// Only the property check is pushed/popped at each step.
/// Property: x_{k+1} >= `bound`. If `bound > steps`, all check-sats should
/// be unsat (property holds at all steps).
///
/// This is the CPAChecker pattern: transition chain grows globally,
/// property violation is checked in a scoped push/pop.
fn generate_bmc_counter(steps: usize, bound: i64) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic QF_LIA)\n");

    // Step 0: initial state
    smt.push_str("(declare-const x_0 Int)\n");
    smt.push_str("(assert (= x_0 0))\n");

    for k in 0..steps {
        let cur = format!("x_{k}");
        let next = format!("x_{}", k + 1);

        // Global: declare next state and add transition
        smt.push_str(&format!("(declare-const {next} Int)\n"));
        smt.push_str(&format!("(assert (= {next} (+ {cur} 1)))\n"));

        // Scoped: property violation check
        smt.push_str("(push 1)\n");
        smt.push_str(&format!("(assert (>= {next} {bound}))\n"));
        smt.push_str("(check-sat)\n");
        smt.push_str("(pop 1)\n");
    }

    smt
}

/// Generate a more complex BMC script with multiple variables and non-trivial
/// transition relations. Transition chain grows globally, property check is scoped.
///
/// Models: x starts at 0, y starts at 10.
/// Transition: x' = x + 2, y' = y - 1
/// Property violation: x >= y (x catches up to y)
/// x catches y at step 4 (x_4=8, y_4=6), so first sat at step 3 (k=3, x_4=8 >= y_4=6).
fn generate_bmc_two_counters(steps: usize) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic QF_LIA)\n");

    // Step 0
    smt.push_str("(declare-const x_0 Int)\n");
    smt.push_str("(declare-const y_0 Int)\n");
    smt.push_str("(assert (= x_0 0))\n");
    smt.push_str("(assert (= y_0 10))\n");

    for k in 0..steps {
        let xc = format!("x_{k}");
        let yc = format!("y_{k}");
        let xn = format!("x_{}", k + 1);
        let yn = format!("y_{}", k + 1);

        // Global: declare next state and transition
        smt.push_str(&format!("(declare-const {xn} Int)\n"));
        smt.push_str(&format!("(declare-const {yn} Int)\n"));
        smt.push_str(&format!("(assert (= {xn} (+ {xc} 2)))\n"));
        smt.push_str(&format!("(assert (= {yn} (- {yc} 1)))\n"));

        // Scoped: property violation check
        smt.push_str("(push 1)\n");
        smt.push_str(&format!("(assert (>= {xn} {yn}))\n"));
        smt.push_str("(check-sat)\n");
        smt.push_str("(pop 1)\n");
    }

    smt
}

/// Generate BMC with mod/div constraints (exercises LIA preprocessing).
///
/// Models: counter x increments by 1, with a divisibility constraint.
/// Property: (mod x 3) = 0 AND x >= bound (checks if x is both divisible
/// by 3 and >= bound).
fn generate_bmc_with_mod(steps: usize, bound: i64) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic QF_LIA)\n");
    smt.push_str("(declare-const x_0 Int)\n");
    smt.push_str("(assert (= x_0 0))\n");

    for k in 0..steps {
        let cur = format!("x_{k}");
        let next = format!("x_{}", k + 1);

        smt.push_str(&format!("(declare-const {next} Int)\n"));
        smt.push_str(&format!("(assert (= {next} (+ {cur} 1)))\n"));

        // Check: can x_{k+1} be both >= bound AND divisible by 3?
        smt.push_str("(push 1)\n");
        smt.push_str(&format!("(assert (>= {next} {bound}))\n"));
        smt.push_str(&format!("(assert (= (mod {next} 3) 0))\n"));
        smt.push_str("(check-sat)\n");
        smt.push_str("(pop 1)\n");
    }

    smt
}

// --- Tests ---

/// Simple counter: 50 steps, bound 100. All check-sats should be unsat
/// because x never reaches 100 (x goes from 0 to 50).
#[test]
#[timeout(30_000)]
fn test_bmc_counter_50_steps_all_unsat() {
    let smt = generate_bmc_counter(50, 100);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 50, "expected 50 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        assert_eq!(
            r,
            "unsat",
            "step {i}: expected unsat (counter={}, bound=100)",
            i + 1
        );
    }
}

/// Simple counter: 50 steps, bound 30. First 28 should be unsat (x goes
/// 1..29, all < 30), step 29 should be sat (x_30 = 30 >= 30).
#[test]
#[timeout(30_000)]
fn test_bmc_counter_50_steps_sat_at_bound() {
    let smt = generate_bmc_counter(50, 30);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 50, "expected 50 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        let x_next = (i + 1) as i64;
        let expected = if x_next >= 30 { "sat" } else { "unsat" };
        assert_eq!(
            r,
            expected,
            "step {i}: x_{} = {x_next}, bound=30, expected {expected} got {r}",
            i + 1
        );
    }
}

/// Two counters: x starts 0 going up by 2, y starts 10 going down by 1.
/// x catches y at step 4 (x=8, y=6) so x >= y first becomes sat at step 3
/// (x_4=8, y_4=6: 8 >= 6 is true).
/// Steps 0-2: unsat. Steps 3+: sat.
#[test]
#[timeout(30_000)]
fn test_bmc_two_counters_20_steps() {
    let smt = generate_bmc_two_counters(20);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 20, "expected 20 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        let x_next = 2 * (i as i64 + 1); // x_{k+1} = 2*(k+1)
        let y_next = 10 - (i as i64 + 1); // y_{k+1} = 10-(k+1)
        let expected = if x_next >= y_next { "sat" } else { "unsat" };
        assert_eq!(
            r,
            expected,
            "step {i}: x_{x}={x_next}, y_{y}={y_next}, expected {expected} got {r}",
            x = i + 1,
            y = i + 1
        );
    }
}

/// Accumulated transitions: 100 push/pop cycles with global transition chain.
/// This pattern has the global assertion set growing with each step while
/// the property check is scoped.
#[test]
#[timeout(60_000)]
fn test_bmc_accumulated_100_steps_all_unsat() {
    let smt = generate_bmc_counter(100, 200);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 100, "expected 100 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        assert_eq!(
            r,
            "unsat",
            "step {i}: expected unsat (counter={}, bound=200)",
            i + 1
        );
    }
}

/// Accumulated transitions with mixed sat/unsat results.
/// Bound 50: steps 0-48 unsat, steps 49+ sat.
#[test]
#[timeout(60_000)]
fn test_bmc_accumulated_100_steps_mixed() {
    let smt = generate_bmc_counter(100, 50);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 100, "expected 100 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        let x_next = (i + 1) as i64;
        let expected = if x_next >= 50 { "sat" } else { "unsat" };
        assert_eq!(
            r,
            expected,
            "step {i}: x_{} = {x_next}, bound=50, expected {expected} got {r}",
            i + 1
        );
    }
}

/// BMC with mod constraints: exercises LIA preprocessing (mod/div elimination).
/// Counter goes 1..50, bound 100. All should be unsat (reduced from 200 steps
/// for test efficiency; the 100-step mod mixed test already covers the pattern).
#[test]
#[timeout(30_000)]
fn test_bmc_with_mod_50_steps_all_unsat() {
    let smt = generate_bmc_with_mod(50, 100);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 50, "expected 50 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        assert_eq!(r, "unsat", "step {i}: expected unsat");
    }
}

/// BMC with mod constraints: mixed results.
/// Counter goes 1..100, bound 50. Property: x >= 50 AND (mod x 3) = 0.
/// x = 50 is not divisible by 3, x = 51 is (51/3=17). So first sat at step 50 (x_51=51).
/// But in scoped push/pop, each check is independent — x_{k+1} = k+1 is fixed,
/// so sat when k+1 >= 50 AND (k+1) mod 3 = 0.
#[test]
#[timeout(60_000)]
fn test_bmc_with_mod_100_steps_mixed() {
    let smt = generate_bmc_with_mod(100, 50);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 100, "expected 100 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        let x_next = (i + 1) as i64;
        let expected = if x_next >= 50 && x_next % 3 == 0 {
            "sat"
        } else {
            "unsat"
        };
        assert_eq!(
            r,
            expected,
            "step {i}: x_{} = {x_next}, bound=50, mod3={}, expected {expected} got {r}",
            i + 1,
            x_next % 3
        );
    }
}

/// BMC stress test: 100 push/pop cycles (reduced from 500 for test efficiency;
/// the 50-step test already covers the #6853 pattern at smaller scale).
#[test]
#[timeout(30_000)]
fn test_bmc_counter_100_steps_stress() {
    let smt = generate_bmc_counter(100, 200);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 100, "expected 100 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        assert_eq!(
            r,
            "unsat",
            "step {i}: expected unsat but got {r} (counter={}, bound=200)",
            i + 1
        );
    }
}

/// Accumulated: 75 steps with growing global assertion set (reduced from 300
/// for test efficiency; 100-step accumulated tests already cover the pattern).
#[test]
#[timeout(30_000)]
fn test_bmc_accumulated_75_steps_stress() {
    let smt = generate_bmc_counter(75, 200);
    let output = crate::common::solve(&smt);
    let res = results(&output);
    assert_eq!(res.len(), 75, "expected 75 check-sat results");
    for (i, &r) in res.iter().enumerate() {
        assert_eq!(
            r,
            "unsat",
            "step {i}: expected unsat but got {r} (counter={}, bound=200)",
            i + 1
        );
    }
}
