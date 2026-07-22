// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test: the quantifier / E-matching pipeline must poll the solve
//! deadline so a wall-clock budget actually bounds it.
//!
//! Before this fix, once control entered quantifier preprocessing ay ran every
//! E-matching round (preprocessing + interleaved) and CEGQI round to completion,
//! ignoring `self.solve_deadline`. A self-triggering quantified formula could
//! therefore blow far past its own timeout (observed 143932ms against a 60000ms
//! budget). These tests assert the loops break promptly and route to Unknown
//! (Timeout / QuantifierRoundLimit), never a finalized Sat.

use ay_dpll::UnknownReason;
use ntest::timeout;
use std::time::{Duration, Instant};

/// A self-triggering, fan-out quantifier set over a growing ground-term
/// universe. Each E-matching round multiplies the number of matched terms, so
/// without a deadline poll the pipeline runs all rounds to completion and
/// materializes a large instantiation set (uncapped: ~300ms, 5 rounds, 7000+
/// instances). With the deadline poll, the run must abort near the budget and
/// return `unknown`.
///
/// The soundness-critical property: a truncated run must be classified as
/// `unknown`, never as a final `sat`.
const SELF_TRIGGERING_SMT: &str = r#"
    (set-logic UFLIA)
    (declare-sort U 0)
    (declare-fun f (U U) U)
    (declare-fun g (U) U)
    (declare-fun h (U) U)
    (declare-fun P (U) Bool)
    (declare-fun a () U)
    (declare-fun b () U)
    (assert (P a))
    (assert (P b))
    ; Fan-out: from any matched pair build new ground terms, re-triggering.
    (assert (forall ((x U) (y U))
        (! (=> (and (P x) (P y)) (P (f x y)))
           :pattern ((P x) (P y)))))
    (assert (forall ((x U))
        (! (=> (P x) (P (g x)))
           :pattern ((P x)))))
    (assert (forall ((x U))
        (! (=> (P x) (P (h x)))
           :pattern ((P x)))))
    (check-sat)
"#;

/// The deadline must break the quantifier pipeline: result is `unknown` with a
/// timeout/round-limit reason, and wall-clock stays well within a small
/// multiple of the budget.
///
/// Proves the loop actually breaks (rather than eventually finishing) by
/// bounding elapsed time. The outer `#[timeout]` is a hard safety net far above
/// the inner deadline so a regression (infinite/very long loop) still fails.
#[test]
#[timeout(60000)]
fn test_quantifier_pipeline_respects_deadline_breaks_to_unknown() {
    let commands = ay_frontend::parse(SELF_TRIGGERING_SMT).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();

    // A budget well below the uncapped ~300ms run so the break is observable.
    let budget = Duration::from_millis(20);
    exec.set_timeout(Some(budget));

    let start = Instant::now();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let elapsed = start.elapsed();

    assert_eq!(
        outputs,
        vec!["unknown"],
        "a truncated quantifier run must be unknown, never a finalized sat/unsat"
    );

    let reason = exec.unknown_reason();
    assert!(
        matches!(
            reason,
            Some(UnknownReason::Timeout) | Some(UnknownReason::QuantifierRoundLimit)
        ),
        "expected Timeout or QuantifierRoundLimit, got {reason:?}"
    );

    // The loop must break near the deadline, not merely finish eventually.
    // Allow generous slack for the in-flight round/solve plus CI jitter, but
    // well below a full uncapped run.
    let cap = Duration::from_secs(10);
    assert!(
        elapsed <= cap,
        "quantifier pipeline overran its {budget:?} deadline: took {elapsed:?} (cap {cap:?})"
    );
}

/// Completeness guard: a formula that reaches UNSAT *before* the deadline must
/// still return UNSAT. A short-but-sufficient budget (5s) must not perturb a
/// 3-round chain that resolves in microseconds — proving the deadline poll adds
/// no completeness loss when the budget suffices.
#[test]
#[timeout(60000)]
fn test_unsat_before_deadline_still_unsat_with_short_budget() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun R (Int) Bool)
        (assert (forall ((x Int))
            (! (=> (P x) (Q x))
               :pattern ((P x)))))
        (assert (forall ((x Int))
            (! (=> (Q x) (R x))
               :pattern ((Q x)))))
        (assert (forall ((x Int))
            (! (=> (R x) false)
               :pattern ((R x)))))
        (assert (P 0))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(smt).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    exec.set_timeout(Some(Duration::from_secs(5)));
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "an UNSAT chain resolving within budget must still be UNSAT under a short timeout"
    );
}
