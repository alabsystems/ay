// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Minimize-counterexamples + combined theory route interaction tests.
//!
//! These tests verify that `:minimize-counterexamples true` works correctly
//! with combined theory routes that use `with_deferred_postprocessing`.
//!
//! The deferred postprocessing helper suppresses inner minimization (via
//! `CounterexampleStyle::Any`) during the isolated solve, then runs deferred
//! minimization against the restored (original) assertions. If this deferred
//! path fails, the model would either:
//! - Not be minimized at all (silent quality regression)
//! - Cause a validation failure degrading SAT to unknown (#6731 variant)
//!
//! Test gap identified by P10 strategic audit: no existing test exercises
//! `:minimize-counterexamples true` with any combined theory route.

use ntest::timeout;

/// QF_AUFLIA with `:minimize-counterexamples true`: array store/select SAT.
///
/// Exercises the deferred minimization path in `with_deferred_postprocessing`.
/// The formula has multiple valid models (i can be any integer). With
/// minimization, the solver should prefer i = 0 and return `sat`.
///
/// Critical invariant: the deferred minimization must run against the
/// original assertions (not the preprocessed ones with ITE-lifted terms).
#[test]
#[timeout(60_000)]
fn test_auflia_minimize_counterexamples_sat_6731() {
    let smt = r#"
        (set-option :minimize-counterexamples true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (>= i 0))
        (assert (= (store a i 42) b))
        (assert (= (select b i) 42))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "QF_AUFLIA with minimize-counterexamples must return sat, got {outputs:?}"
    );
}

/// QF_LIRA with `:minimize-counterexamples true`: mixed Int/Real SAT.
///
/// Exercises the deferred minimization path for the LIRA route.
/// Multiple models exist (x >= 0, y >= 1.0). Minimization should prefer
/// smaller values and still return `sat`.
#[test]
#[timeout(60_000)]
fn test_lira_minimize_counterexamples_sat_6731() {
    let smt = r#"
        (set-option :minimize-counterexamples true)
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (>= x 0))
        (assert (>= y 1.0))
        (assert (< (to_real x) y))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "QF_LIRA with minimize-counterexamples must return sat, got {outputs:?}"
    );
}

/// QF_AUFLIRA with `:minimize-counterexamples true`: arrays + mixed arithmetic SAT.
///
/// Exercises the deferred minimization path for the AUFLIRA route.
/// Combines array operations with mixed Int/Real constraints.
#[test]
#[timeout(60_000)]
fn test_auflira_minimize_counterexamples_sat_6731() {
    let smt = r#"
        (set-option :minimize-counterexamples true)
        (set-logic QF_AUFLIRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const v Real)
        (assert (>= i 0))
        (assert (>= v 0.0))
        (assert (= (select (store a i v) i) v))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "QF_AUFLIRA with minimize-counterexamples must return sat, got {outputs:?}"
    );
}

/// QF_AUFLIA check-sat-assuming + `:minimize-counterexamples true`.
///
/// The deferred minimization should be skipped when assumptions are present
/// (line 97 of incremental_scope.rs: `self.last_assumptions.is_none()`).
/// This test verifies that the assumption path doesn't crash or degrade
/// when minimization is enabled.
#[test]
#[timeout(60_000)]
fn test_auflia_assume_minimize_counterexamples_sat_6731() {
    let smt = r#"
        (set-option :minimize-counterexamples true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (>= i 0))
        (assert (= (store a i 42) b))
        (check-sat-assuming ((= (select b i) 42)))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "QF_AUFLIA check-sat-assuming with minimize-counterexamples must return sat, got {outputs:?}"
    );
}
