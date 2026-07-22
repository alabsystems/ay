// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Performance proof: PDR startup invariant discovery must respect solve_timeout
//! on high-arity predicates.
//!
//! PDR startup runs ~30 invariant discovery functions, many of which enumerate
//! all O(V^2) or O(V^3) variable combinations per predicate. Without variable-
//! count guards or inner-loop cancellation, high-arity predicates (V=20+) can
//! stall startup for seconds of wasted SMT queries.
//!
//! Functions with guards: triple_sum (V<=10), sum_equals_var (V<=15),
//!   counting (V<=20), affine_kernel (1500ms budget).
//! Functions without guards: difference, relational, scaled_sum.
//!
//! These tests verify the timeout contract is honored despite the O(V^k)
//! discovery loops. Regression in any discovery pass's cancellation handling
//! will cause these tests to exceed their wall-clock assertions.
//!
//! Part of #7016, #7006.

use ay_chc::{testing, PdrConfig, PdrResult};
use std::time::{Duration, Instant};

/// Build a CHC problem with N integer variables per predicate.
/// Init: all zeros. Transition: a0'=a0+1, rest unchanged.
/// Safety: a0 >= 0 (trivially safe).
fn build_high_arity_chc(n: usize) -> String {
    let mut smt2 = String::from("(set-logic HORN)\n");

    // Declare predicate with N Int parameters
    smt2.push_str("(declare-fun inv (");
    for _ in 0..n {
        smt2.push_str("Int ");
    }
    smt2.push_str(") Bool)\n");

    // Init clause: all zeros
    smt2.push_str("(assert (forall (");
    for i in 0..n {
        smt2.push_str(&format!("(a{i} Int) "));
    }
    smt2.push_str(") (=> (and ");
    for i in 0..n {
        smt2.push_str(&format!("(= a{i} 0) "));
    }
    smt2.push_str(") (inv ");
    for i in 0..n {
        smt2.push_str(&format!("a{i} "));
    }
    smt2.push_str("))))\n");

    // Transition: a0'=a0+1, rest unchanged
    smt2.push_str("(assert (forall (");
    for i in 0..n {
        smt2.push_str(&format!("(a{i} Int) "));
    }
    for i in 0..n {
        smt2.push_str(&format!("(b{i} Int) "));
    }
    smt2.push_str(") (=> (and (inv ");
    for i in 0..n {
        smt2.push_str(&format!("a{i} "));
    }
    smt2.push_str(") (= b0 (+ a0 1)) ");
    for i in 1..n {
        smt2.push_str(&format!("(= b{i} a{i}) "));
    }
    smt2.push_str(") (inv ");
    for i in 0..n {
        smt2.push_str(&format!("b{i} "));
    }
    smt2.push_str("))))\n");

    // Safety: a0 >= 0
    smt2.push_str("(assert (forall (");
    for i in 0..n {
        smt2.push_str(&format!("(a{i} Int) "));
    }
    smt2.push_str(") (=> (and (inv ");
    for i in 0..n {
        smt2.push_str(&format!("a{i} "));
    }
    smt2.push_str(") (< a0 0)) false)))\n");
    smt2.push_str("(check-sat)\n");
    smt2
}

/// 20-variable predicate must respect the 2s solve_timeout.
///
/// At V=20, the O(V^2) discovery passes generate up to 380 candidate pairs
/// and the O(V^3) passes up to 1140 triples. The nonfixpoint budget (40% of
/// solve_timeout = 800ms) and per-outer-loop cancellation checks must prevent
/// these from exceeding the timeout by more than one SMT query batch (~500ms).
///
/// Wall-clock budget: solve_timeout (2s) + overhead (parsing, SMT init, one
/// uncancellable inner-loop iteration) must stay under 4s total. If this
/// exceeds 4s, an O(V^k) pass is ignoring cancellation.
#[test]
fn pdr_20var_completes_within_timeout() {
    let smt2 = build_high_arity_chc(20);
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(Duration::from_secs(2));

    let start = Instant::now();
    let result = testing::pdr_solve_from_str(&smt2, config).unwrap();
    let elapsed = start.elapsed();

    // Verify the solver returned (not hung in discovery)
    assert!(
        matches!(result, PdrResult::Safe(_) | PdrResult::Unknown),
        "Expected Safe or Unknown, got {result:?}"
    );

    // Must complete within 4s (2s timeout + 2s overhead margin for debug mode).
    // In release mode this typically finishes in ~2.1s. In debug mode, SMT
    // overhead pushes it to ~2.5s. If it exceeds 4s, a discovery pass is
    // ignoring the timeout on the high-arity predicate.
    assert!(
        elapsed < Duration::from_secs(4),
        "PDR with 20-variable predicate took {elapsed:?} (expected < 4s with 2s timeout). \
         Invariant discovery O(V^2) passes may be ignoring cancellation."
    );
}

/// 30-variable predicate must also respect the timeout — not blow up O(V^3).
///
/// V=30 has C(30,2)=435 pairs for O(V^2), C(30,3)=4060 triples for O(V^3).
/// Without variable-count guards, O(V^3) passes would need 4060 SMT queries.
/// The solve_timeout must still be honored: the wall-clock bound is the same
/// as V=20 (timeout + overhead), proving that the cancellation mechanism
/// works independently of arity.
#[test]
fn pdr_30var_completes_within_timeout() {
    let smt2 = build_high_arity_chc(30);
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(Duration::from_secs(2));

    let start = Instant::now();
    let result = testing::pdr_solve_from_str(&smt2, config).unwrap();
    let elapsed = start.elapsed();

    assert!(
        matches!(result, PdrResult::Safe(_) | PdrResult::Unknown),
        "Expected Safe or Unknown, got {result:?}"
    );

    // Same 4s budget as V=20. If V=30 takes significantly longer than V=20,
    // an O(V^k) discovery pass lacks a variable-count guard AND its inner
    // loop doesn't check cancellation.
    assert!(
        elapsed < Duration::from_secs(4),
        "PDR with 30-variable predicate took {elapsed:?} (expected < 4s with 2s timeout). \
         O(V^3) discovery passes may lack variable-count guards."
    );
}
