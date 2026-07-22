// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test (#quantifier-determinism, defect 1): the quantified-solve
//! wall-clock backstop must actually GOVERN the solve end-to-end — every stop
//! path must observe the extended (live) deadline, not a stale by-value
//! snapshot of the nominal deadline taken at closure construction.
//!
//! `Executor::solve_deadline` is now a shared live cell
//! (`SolveDeadlineCell`): `make_should_stop` and the theory-loop stop
//! closures read it at poll time. This test pins the observable contract: a
//! quantified solve whose deterministic instantiation work exceeds the
//! nominal budget runs well PAST the nominal wall (the backstop governs) and
//! still fails closed to `unknown` with a truncation reason — never a
//! finalized `sat`.

use ay_dpll::UnknownReason;
use ntest::timeout;
use std::time::{Duration, Instant};

/// Self-triggering fan-out quantifiers over a growing ground-term universe
/// (same shape as `group_quantifiers/ematching_deadline_break.rs`): the
/// deterministic E-matching budgets need seconds of work uncapped (debug
/// builds: >10s), so with a 50ms nominal budget the deterministic work always
/// exceeds even the backstop and the run MUST be truncated — the question is
/// only WHERE the wall is.
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

/// The quantified backstop (4x the remaining nominal budget) must govern the
/// stop, not the nominal deadline: with a 50ms nominal budget the solve must
/// run meaningfully past the nominal wall (>= 2x) before failing closed. A
/// stale-snapshot regression (any stop closure capturing the pre-extension
/// deadline by value) stops the solve at ~1x nominal and fails the lower
/// bound. The generous upper bound is hang protection only — poll granularity
/// in the E-matching rounds can overshoot the backstop itself.
#[test]
#[timeout(120000)]
fn quantified_solve_runs_past_nominal_to_the_backstop() {
    let budget = Duration::from_millis(50);
    let commands = ay_frontend::parse(SELF_TRIGGERING_SMT).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    exec.set_timeout(Some(budget));

    let start = Instant::now();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let elapsed = start.elapsed();

    // Fail-closed: a truncated quantified run is unknown, never sat/unsat.
    assert_eq!(
        outputs,
        vec!["unknown"],
        "truncated quantified run must stay unknown"
    );
    assert!(
        matches!(
            exec.unknown_reason(),
            Some(
                UnknownReason::Timeout
                    | UnknownReason::QuantifierRoundLimit
                    | UnknownReason::QuantifierUnhandled
            )
        ),
        "truncation reason expected, got {:?}",
        exec.unknown_reason()
    );
    // The backstop, not the nominal deadline, must be the wall: the
    // deterministic work here needs far more than 100ms on any machine, so
    // stopping before 2x nominal means some stop path used a stale
    // pre-extension deadline snapshot.
    assert!(
        elapsed >= budget * 2,
        "solve stopped at {elapsed:?} with a {budget:?} nominal budget: a \
         quantified solve must be governed by the 4x backstop (live deadline \
         reads), not the stale nominal deadline"
    );
}
