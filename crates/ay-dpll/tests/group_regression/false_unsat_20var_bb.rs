// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for 20-variable QF_LIA binary integer program (#2740).
//!
//! 20 binary variables (each in [0,1]) with:
//! - Cardinality constraint: sum = 10
//! - Two tight weighted-sum range constraints on odd/even-indexed variables
//!
//! Z3 returns SAT in ~0.01s. AY must return SAT (not UNSAT or unknown).
//! This is a performance regression test: the non-incremental path used to
//! rebuild the entire DPLL(T) solver per split iteration; batching all
//! tight-domain splits collapses ~7 iterations to 1.

use ay_dpll::Executor;
use ay_dpll::UnknownReason;
use ay_frontend::parse;
use ay_test_support::env::with_env_edits;
use ntest::timeout;
use std::time::{Duration, Instant};

const HARD_SEED_INPUT: &str = r#"
(set-logic QF_LIA)
(declare-fun x1 () Int) (declare-fun x2 () Int) (declare-fun x3 () Int)
(declare-fun x4 () Int) (declare-fun x5 () Int) (declare-fun x6 () Int)
(declare-fun x7 () Int) (declare-fun x8 () Int) (declare-fun x9 () Int)
(declare-fun x10 () Int) (declare-fun x11 () Int) (declare-fun x12 () Int)
(declare-fun x13 () Int) (declare-fun x14 () Int) (declare-fun x15 () Int)
(declare-fun x16 () Int) (declare-fun x17 () Int) (declare-fun x18 () Int)
(declare-fun x19 () Int) (declare-fun x20 () Int)
(assert (and (>= x1 0) (<= x1 1))) (assert (and (>= x2 0) (<= x2 1)))
(assert (and (>= x3 0) (<= x3 1))) (assert (and (>= x4 0) (<= x4 1)))
(assert (and (>= x5 0) (<= x5 1))) (assert (and (>= x6 0) (<= x6 1)))
(assert (and (>= x7 0) (<= x7 1))) (assert (and (>= x8 0) (<= x8 1)))
(assert (and (>= x9 0) (<= x9 1))) (assert (and (>= x10 0) (<= x10 1)))
(assert (and (>= x11 0) (<= x11 1))) (assert (and (>= x12 0) (<= x12 1)))
(assert (and (>= x13 0) (<= x13 1))) (assert (and (>= x14 0) (<= x14 1)))
(assert (and (>= x15 0) (<= x15 1))) (assert (and (>= x16 0) (<= x16 1)))
(assert (and (>= x17 0) (<= x17 1))) (assert (and (>= x18 0) (<= x18 1)))
(assert (and (>= x19 0) (<= x19 1))) (assert (and (>= x20 0) (<= x20 1)))
(assert (= (+ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) 10))
(assert (>= (+ (* 13 x1) (* 7 x3) (* 11 x5) (* 3 x7) (* 17 x9) (* 5 x11) (* 19 x13) (* 2 x15) (* 23 x17) (* 29 x19)) 85))
(assert (<= (+ (* 13 x1) (* 7 x3) (* 11 x5) (* 3 x7) (* 17 x9) (* 5 x11) (* 19 x13) (* 2 x15) (* 23 x17) (* 29 x19)) 87))
(assert (>= (+ (* 31 x2) (* 37 x4) (* 41 x6) (* 43 x8) (* 47 x10) (* 53 x12) (* 59 x14) (* 61 x16) (* 67 x18) (* 71 x20)) 250))
(assert (<= (+ (* 31 x2) (* 37 x4) (* 41 x6) (* 43 x8) (* 47 x10) (* 53 x12) (* 59 x14) (* 61 x16) (* 67 x18) (* 71 x20)) 254))
(check-sat)
"#;

fn with_global_timeout_ms<T>(timeout_ms: u64, f: impl FnOnce() -> T) -> T {
    with_global_timeout_override(Some(timeout_ms), f)
}

fn with_global_timeout_unset<T>(f: impl FnOnce() -> T) -> T {
    with_global_timeout_override(None, f)
}

fn with_global_timeout_override<T>(timeout_ms: Option<u64>, f: impl FnOnce() -> T) -> T {
    // Serialized + restore-on-exit via the workspace env choke point.
    with_env_edits(|env| {
        match timeout_ms {
            Some(ms) => env.set("AY_GLOBAL_TIMEOUT_MS", &ms.to_string()),
            None => env.remove("AY_GLOBAL_TIMEOUT_MS"),
        }
        f()
    })
}

#[test]
#[timeout(120_000)]
fn test_false_unsat_20var_branch_and_bound() {
    let commands = parse(HARD_SEED_INPUT).unwrap();
    let mut exec = Executor::new();
    let outputs = with_global_timeout_unset(|| exec.execute_all(&commands).unwrap());
    // Z3 returns SAT. AY must also return SAT (not UNSAT, not unknown).
    assert_eq!(
        outputs,
        vec!["sat"],
        "Expected sat (Z3 returns sat with verified model), got {outputs:?}"
    );
}

#[test]
#[timeout(120_000)]
fn test_false_unsat_20var_timeout_path_returns_quick_non_unsat() {
    let commands = parse(HARD_SEED_INPUT).unwrap();
    let mut exec = Executor::new();

    let (outputs, elapsed) = with_global_timeout_ms(30_000, || {
        let start = Instant::now();
        let outputs = exec.execute_all(&commands).unwrap();
        (outputs, start.elapsed())
    });

    let first = outputs.first().map_or("", String::as_str);
    assert_ne!(first, "unsat", "timeout path must not return unsat");
    assert!(
        matches!(first, "sat" | "unknown"),
        "expected sat or unknown, got {first:?}"
    );
    if first == "unknown" {
        assert_eq!(
            exec.unknown_reason(),
            Some(UnknownReason::Timeout),
            "unknown result should report timeout reason"
        );
    }
    assert!(
        elapsed < Duration::from_secs(8),
        "expected quick timeout-path response; elapsed={elapsed:?}"
    );
}
