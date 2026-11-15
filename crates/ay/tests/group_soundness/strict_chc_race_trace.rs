// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A strict CHC run publishes an UNSAFE verdict with a trace STEP D can
//! ground-check, whichever participant of the adaptive ladder race proves it
//! first.
//!
//! Measured at e2e3bd3a8 (the pre-stage ladder raced concurrently with the
//! portfolio): on a 7-step counter loop `ay --strict-proofs` printed `unknown`
//! in 3 of 3 runs, bounded and unbounded. The portfolio's CEGAR trace, which
//! carries no concrete values, decided the race, and STEP D demoted the
//! correct `unsat` ("missing concrete trace assignment for step 0, state arg
//! 0"). In the unbounded run the portfolio had also dropped its BMC for a
//! front BMC member that got no budget, so no BMC ran at all.

use ntest::timeout;
use std::process::Command;

use super::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};
use crate::spawn::OutputTimeout;

/// Printed only when STEP D (the UNSAFE ground check) ran and passed.
const UNSAFE_GATE_RAN: &str =
    "CHC strict trace check: UNSAFE counterexample independently ground-checked";

/// `inv` holds at 0 and is closed under `+ 1`, so `x > bound` is reached
/// after `bound + 2` states. UNSAFE, published as `unsat`.
fn counter(bound: u32) -> String {
    format!(
        "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x {bound})) false)))
(check-sat)
"
    )
}

/// `ay --strict-proofs <args> FILE` on `script` must print `unsat` alone,
/// after STEP D ground-checked the published trace.
fn assert_strict_unsat_ground_checked(script: &str, args: &[&str], attempt: usize) {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("horn.smt2");
    std::fs::write(&input, script).expect("write HORN input");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--strict-proofs")
        .args(args)
        .arg(&input)
        .output_timeout(QUERY_TIMEOUT)
        .unwrap_or_else(|e| panic!("run ay: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let context = format!("{args:?} attempt {attempt}\nstdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(output.status.success(), "{context}");
    assert_eq!(verdict_lines(&stdout), ["unsat"], "{context}");
    assert!(stderr.contains(UNSAFE_GATE_RAN), "{context}");
}

/// Bounded: the front BMC member races the portfolio, which drops its own
/// BMC. The portfolio's witness-free trace no longer decides as it is: it is
/// re-derived by a bounded BMC replay, or held while the race stays open for
/// a witness-bearing verdict (solo PDR, Farkas-PDR, the front BMC member).
#[test]
#[timeout(600_000)]
fn a_bounded_strict_run_publishes_a_ground_checked_unsafe_trace() {
    for attempt in 0..3 {
        assert_strict_unsat_ground_checked(&counter(5), &["--timeout", "30000"], attempt);
    }
}

/// Unbounded (no timeout): the front BMC member has no budget share, so the
/// portfolio keeps its own BMC, which finds this 47-state counterexample at
/// once. Measured with the portfolio's BMC dropped for the member regardless:
/// `unknown` at ~18 s, since no BMC ran and a witness-free trace the replay
/// could not re-derive in its 10 s window was the only verdict.
#[test]
#[timeout(600_000)]
fn an_unbounded_strict_run_keeps_the_portfolio_bmc_for_a_deep_counterexample() {
    assert_strict_unsat_ground_checked(&counter(45), &[], 0);
}

/// Bounded, deep: at 50 s the portfolio proves this 47-state counterexample
/// without a trace (PDKIND) well before the front BMC member reaches depth 46
/// (~18 s), and the replay's 10 s window ends short of it. Measured when that
/// unconfirmed trace decided the race as it was: `unknown` in 3 of 3 runs at
/// ~16 s, the front BMC member cancelled short of depth 46. Held instead, it
/// waits for the member's witness-bearing verdict. (At 120 s the portfolio's
/// slices grow and the member won first in 2 of 2 runs, so the budget here is
/// what makes the case bite.)
#[test]
#[timeout(600_000)]
fn a_bounded_strict_run_holds_an_unconfirmed_witness_free_unsafe_for_the_front_bmc() {
    assert_strict_unsat_ground_checked(&counter(45), &["--timeout", "50000"], 0);
}
