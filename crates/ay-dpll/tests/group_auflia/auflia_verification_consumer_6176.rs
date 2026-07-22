// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6176: AUFLIA split-loop dedup SAT completeness regression.
//!
//! Commit cf9b2f0cb added expression-split and model-equality deduplication to
//! the split loop (#4906). This caused satisfiable QF_AUFLIA formulas with
//! `(distinct loc1 loc2)` + array selects to return Unknown instead of SAT.
//!
//! Root cause: the dedup bailed on the first duplicate expression split or
//! model equality, but the SAT solver needs a few iterations to activate
//! the split variables via VSIDS. The fix allows up to 3 retries before bailing.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// verification-consumer separation-logic pattern: two PointsTo cells on distinct locations.
/// Must return SAT. Previously returned Unknown (#6176).
#[test]
#[timeout(30_000)]
fn test_auflia_verification_consumer_distinct_locs_sat_6176() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const heap (Array Int Int))
        (declare-const domain (Array Int Int))
        (declare-const perms (Array Int Int))
        (declare-const loc1 Int)
        (declare-const loc2 Int)
        (assert (= (select domain loc1) 1))
        (assert (= (select heap loc1) 10))
        (assert (>= (select perms loc1) 2520))
        (assert (<= (select perms loc1) 2520))
        (assert (>= (select perms loc1) 0))
        (assert (= (select domain loc2) 1))
        (assert (= (select heap loc2) 20))
        (assert (>= (select perms loc2) 2520))
        (assert (<= (select perms loc2) 2520))
        (assert (>= (select perms loc2) 0))
        (assert (distinct loc1 loc2))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "verification-consumer PointsTo * PointsTo with distinct locs should be SAT"
    );
}

/// Simpler variant: two unconstrained integers that must be distinct.
/// Trivially SAT (assign loc1=0, loc2=1).
#[test]
#[timeout(30_000)]
fn test_auflia_simple_distinct_sat_6176() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const loc1 Int)
        (declare-const loc2 Int)
        (assert (= (select a loc1) 10))
        (assert (= (select a loc2) 20))
        (assert (distinct loc1 loc2))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(last.trim(), "sat", "simple array + distinct should be SAT");
}

/// Three distinct locations with array constraints — more complex pattern.
#[test]
#[timeout(30_000)]
fn test_auflia_triple_distinct_sat_6176() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const arr (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (= (select arr x) 1))
        (assert (= (select arr y) 2))
        (assert (= (select arr z) 3))
        (assert (distinct x y))
        (assert (distinct y z))
        (assert (distinct x z))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "sat",
        "three distinct array selects should be SAT"
    );
}
