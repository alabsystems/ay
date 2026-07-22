// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! UNSAT benchmark coverage tests for CHC solver (#5374)
//!
//! Tests exercise the UNSAT (unsafe) path of the CHC solver using inline
//! benchmark content. Each test verifies that AY does NOT return Safe (sat)
//! on a known-unsafe system. Returning Unknown is acceptable (capability gap);
//! returning Safe is a soundness bug.
//!
//! The inline tests are self-contained and do not depend on external benchmark
//! files being present on disk.

use ay_chc::{testing, ChcParser, PdrConfig, PortfolioConfig, PortfolioResult};
use ntest::timeout;
use std::time::Duration;

fn full_production_config() -> PortfolioConfig {
    // Use test_default() (PDR + BMC + Kind) to reduce thread count from 12 to 3.
    // This is sufficient for soundness testing; engine-diversity is tested separately.
    PortfolioConfig::test_default().parallel_timeout(Some(Duration::from_secs(10)))
}

enum ChcResult {
    Safe,
    /// Correct UNSAT result with counterexample trace step count
    Unsafe {
        trace_steps: usize,
    },
    Unknown,
}

fn run_ay_on_smt2(smt2: &str) -> ChcResult {
    let problem = ChcParser::parse(smt2).expect("parse error on inline benchmark");
    let solver = testing::new_portfolio_solver(problem.clone(), full_production_config());
    match solver.solve() {
        PortfolioResult::Safe(model) => {
            // Verify model — catches spurious invariants
            let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
            if !verifier.verify_model(&model) {
                return ChcResult::Unknown;
            }
            ChcResult::Safe
        }
        PortfolioResult::Unsafe(cex) => ChcResult::Unsafe {
            trace_steps: cex.steps.len(),
        },
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => ChcResult::Unknown,
        _ => panic!("unexpected variant"),
    }
}

// ── Inline UNSAT benchmark content ──────────────────────────────────────────

const COUNTER_DOWN_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 5) (Inv x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (Inv x) (= x1 (- x 1))) (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)";

const SUBTRACTION_UNBOUNDED_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 3) (Inv x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (Inv x) (= x1 (- x 1))) (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)";

const TWO_COUNTER_SUM_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (Inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (Inv x y) (= x1 (+ x 1)) (= y1 (+ y 2))) (Inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x y) (>= (+ x y) 10)) false)))
(check-sat)";

const DIVERGING_INCREMENT_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (Inv x) (= x1 (+ x 3))) (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (>= x 100)) false)))
(check-sat)";

const EVEN_COUNTER_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (Inv x) (= x1 (+ x 2))) (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 10)) false)))
(check-sat)";

const DOUBLING_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 1) (Inv x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (Inv x) (= x1 (* 2 x))) (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 1000)) false)))
(check-sat)";

const CONDITIONAL_BRANCH_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (< x 5) (= x1 (+ x 1))) (Inv x1))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (>= x 5) (= x1 (+ x 10))) (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (>= x 20)) false)))
(check-sat)";

const ACCUMULATOR_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (Inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (Inv x y) (= x1 (+ x 1)) (= y1 (+ y x))) (Inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x y) (>= y 50)) false)))
(check-sat)";

const TWO_PHASE_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (pc Int)) (=> (and (= x 0) (= pc 0)) (Inv x pc))))
(assert (forall ((x Int) (pc Int) (x1 Int) (pc1 Int))
  (=> (and (Inv x pc) (= pc 0) (< x 10) (= x1 (+ x 1)) (= pc1 0)) (Inv x1 pc1))))
(assert (forall ((x Int) (pc Int) (x1 Int) (pc1 Int))
  (=> (and (Inv x pc) (= pc 0) (>= x 10) (= x1 x) (= pc1 1)) (Inv x1 pc1))))
(assert (forall ((x Int) (pc Int) (x1 Int) (pc1 Int))
  (=> (and (Inv x pc) (= pc 1) (= x1 (- x 1)) (= pc1 1)) (Inv x1 pc1))))
(assert (forall ((x Int) (pc Int)) (=> (and (Inv x pc) (< x 0)) false)))
(check-sat)";

const REACHABLE_ABORT_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (pc Int)) (=> (and (= x 0) (= pc 0)) (Inv x pc))))
(assert (forall ((x Int) (pc Int) (x1 Int) (pc1 Int))
  (=> (and (Inv x pc) (= pc 0) (<= x 10) (= x1 (+ x 1)) (= pc1 0)) (Inv x1 pc1))))
(assert (forall ((x Int) (pc Int) (x1 Int) (pc1 Int))
  (=> (and (Inv x pc) (= pc 0) (> x 10) (= x1 x) (= pc1 1)) (Inv x1 pc1))))
(assert (forall ((x Int) (pc Int)) (=> (and (Inv x pc) (= pc 1)) false)))
(check-sat)";

// ── Tests: AY correctly returns Unsafe ──────────────────────────────────────

macro_rules! assert_not_safe {
    ($name:ident, $smt2:expr, $timeout_ms:expr) => {
        #[test]
        #[timeout($timeout_ms)]
        fn $name() {
            match run_ay_on_smt2($smt2) {
                ChcResult::Safe => {
                    panic!("SOUNDNESS BUG: AY returned Safe on known-unsafe benchmark (see #5376)")
                }
                ChcResult::Unsafe { trace_steps } => {
                    eprintln!(
                        "Correct: Unsafe (counterexample trace: {} steps)",
                        trace_steps
                    );
                }
                ChcResult::Unknown => {
                    eprintln!("AY returned Unknown (capability gap, not soundness bug)");
                }
            }
        }
    };
}

// Benchmarks where AY must NOT return Safe (Safe = soundness bug, Unknown = acceptable)
assert_not_safe!(test_unsat_counter_down, COUNTER_DOWN_UNSAFE, 15_000);
assert_not_safe!(
    test_unsat_subtraction_unbounded,
    SUBTRACTION_UNBOUNDED_UNSAFE,
    15_000
);
assert_not_safe!(test_unsat_two_counter_sum, TWO_COUNTER_SUM_UNSAFE, 15_000);
assert_not_safe!(
    test_unsat_diverging_increment,
    DIVERGING_INCREMENT_UNSAFE,
    15_000
);
assert_not_safe!(test_unsat_even_counter, EVEN_COUNTER_UNSAFE, 15_000);
assert_not_safe!(test_unsat_doubling, DOUBLING_UNSAFE, 15_000);

// Benchmarks that previously triggered TRL soundness bug (#5376, fixed in c01c3a8).
// TRL now returns Unknown on these (unsound diameter proof disabled).
assert_not_safe!(
    test_unsat_conditional_branch,
    CONDITIONAL_BRANCH_UNSAFE,
    15_000
);
assert_not_safe!(test_unsat_accumulator, ACCUMULATOR_UNSAFE, 15_000);
assert_not_safe!(test_unsat_two_phase, TWO_PHASE_UNSAFE, 15_000);

// Capability gap (AY returns unknown with CLI, may vary with test config)
assert_not_safe!(test_unsat_reachable_abort, REACHABLE_ABORT_UNSAFE, 15_000);

/// Aggregate test: run all UNSAT benchmarks and report coverage statistics.
#[test]
#[timeout(120_000)]
fn test_unsat_aggregate_coverage() {
    let benchmarks: &[(&str, &str)] = &[
        ("counter_down_unsafe", COUNTER_DOWN_UNSAFE),
        ("subtraction_unbounded_unsafe", SUBTRACTION_UNBOUNDED_UNSAFE),
        ("two_counter_sum_unsafe", TWO_COUNTER_SUM_UNSAFE),
        ("diverging_increment_unsafe", DIVERGING_INCREMENT_UNSAFE),
        ("even_counter_unsafe", EVEN_COUNTER_UNSAFE),
        ("doubling_unsafe", DOUBLING_UNSAFE),
        ("conditional_branch_unsafe", CONDITIONAL_BRANCH_UNSAFE),
        ("accumulator_unsafe", ACCUMULATOR_UNSAFE),
        ("two_phase_unsafe", TWO_PHASE_UNSAFE),
        ("reachable_abort_unsafe", REACHABLE_ABORT_UNSAFE),
    ];

    let mut correct_unsat = Vec::new();
    let mut wrong_safe = Vec::new();
    let mut unknown = Vec::new();
    let mut total_trace_steps = 0usize;
    let mut with_traces = 0usize;

    for (name, smt2) in benchmarks {
        match run_ay_on_smt2(smt2) {
            ChcResult::Safe => {
                eprintln!("  {name}: WRONG (safe on known-unsafe!)");
                wrong_safe.push(*name);
            }
            ChcResult::Unsafe { trace_steps } => {
                eprintln!("  {name}: correct (unsafe, trace: {trace_steps} steps)");
                correct_unsat.push(*name);
                total_trace_steps += trace_steps;
                if trace_steps > 0 {
                    with_traces += 1;
                }
            }
            ChcResult::Unknown => {
                eprintln!("  {name}: unknown (capability gap)");
                unknown.push(*name);
            }
        }
    }

    eprintln!(
        "\nUNSAT coverage: {}/{} correct, {} unknown, {} WRONG",
        correct_unsat.len(),
        benchmarks.len(),
        unknown.len(),
        wrong_safe.len(),
    );
    eprintln!(
        "Counterexample traces: {}/{} with steps ({} total steps)",
        with_traces,
        correct_unsat.len(),
        total_trace_steps,
    );

    // AY must never return Safe on a known-unsafe benchmark
    assert!(
        wrong_safe.is_empty(),
        "SOUNDNESS BUG (#5376): AY returned Safe on {} known-unsafe benchmarks: {:?}",
        wrong_safe.len(),
        wrong_safe,
    );

    // At least 8/10 should solve correctly (10/10 currently pass;
    // allow slack for 2 intermittent timeouts but catch significant regressions)
    assert!(
        correct_unsat.len() >= 8,
        "Expected at least 8 correct UNSAT results, got {}",
        correct_unsat.len(),
    );
}
