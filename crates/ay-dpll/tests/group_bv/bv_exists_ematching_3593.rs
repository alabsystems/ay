// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for BV existential quantifier soundness (#3593).
//!
//! deductive-checks encodes existential membership checks over BV arrays via:
//!   assert(NOT(exists i:BV. bvult(i, len) && select(arr, i) == target))
//!   check-sat
//!
//! When the target is NOT in the array:
//! - The exists is FALSE → its negation (forall) is TRUE → the formula is SAT
//! - ay should return SAT (or unknown — safe incomplete)
//!
//! Bug: ay returns UNSAT, incorrectly claiming the forall is unsatisfiable.
//! This causes deductive-checks to accept counterexamples as verified.

use ntest::timeout;

/// Positive case: target IS in the array → exists is true → negation is unsat.
/// This case works correctly (both old and new code).
#[test]
#[timeout(60_000)]
fn test_bv_exists_array_member_found_unsat_3593() {
    // Array: s[0]=1, s[1]=2, s[2]=3, len=3
    // exists i:BV(32). bvult(i, len) && select(s, i) == 2
    // → TRUE (witness: i=1)
    // → negation (forall i. NOT(...)) is UNSAT
    let smt = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        (assert (= len #x00000003))
        (assert (= (select s #x00000000) #x00000001))
        (assert (= (select s #x00000001) #x00000002))
        (assert (= (select s #x00000002) #x00000003))
        (assert (forall ((i (_ BitVec 32)))
            (not (and (bvult i len) (= (select s i) #x00000002)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// REGRESSION: target NOT in the array → exists is false → negation is sat.
/// ay incorrectly returns UNSAT.
#[test]
#[timeout(60_000)]
fn test_bv_exists_array_member_not_found_sat_3593() {
    // Array: s[0]=1, s[1]=2, s[2]=3, len=3
    // exists i:BV(32). bvult(i, len) && select(s, i) == 5
    // → FALSE (no witness: 5 not in {1,2,3})
    // → negation (forall i. NOT(...)) is SAT
    let smt = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        (assert (= len #x00000003))
        (assert (= (select s #x00000000) #x00000001))
        (assert (= (select s #x00000001) #x00000002))
        (assert (= (select s #x00000002) #x00000003))
        (assert (forall ((i (_ BitVec 32)))
            (not (and (bvult i len) (= (select s i) #x00000005)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // SAT or unknown are both acceptable — UNSAT is a soundness bug
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "Expected sat or unknown, got: {outputs:?}"
    );
}

/// Direct exists assertion (no negation): target in array → SAT (witness exists).
#[test]
#[timeout(60_000)]
fn test_bv_exists_direct_member_found_sat_3593() {
    let smt = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        (assert (= len #x00000003))
        (assert (= (select s #x00000000) #x00000001))
        (assert (= (select s #x00000001) #x00000002))
        (assert (= (select s #x00000002) #x00000003))
        (assert (exists ((i (_ BitVec 32)))
            (and (bvult i len) (= (select s i) #x00000002))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // SAT is correct; unknown is safe incomplete
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "Expected sat or unknown, got: {outputs:?}"
    );
}

/// Direct exists assertion: target NOT in array → UNSAT (no witness).
#[test]
#[timeout(60_000)]
fn test_bv_exists_direct_member_not_found_unsat_3593() {
    let smt = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        (assert (= len #x00000003))
        (assert (= (select s #x00000000) #x00000001))
        (assert (= (select s #x00000001) #x00000002))
        (assert (= (select s #x00000002) #x00000003))
        (assert (exists ((i (_ BitVec 32)))
            (and (bvult i len) (= (select s i) #x00000005))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // UNSAT is correct; unknown is safe incomplete
    // SAT would be a soundness bug (false witness)
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Expected unsat or unknown, got: {outputs:?}"
    );
}

/// BV(64) width variant — deductive-checks uses 64-bit BV indices.
#[test]
#[timeout(60_000)]
fn test_bv64_exists_member_not_found_sat_3593() {
    let smt = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const len (_ BitVec 64))
        (assert (= len #x0000000000000003))
        (assert (= (select s #x0000000000000000) #x00000001))
        (assert (= (select s #x0000000000000001) #x00000002))
        (assert (= (select s #x0000000000000002) #x00000003))
        (assert (forall ((i (_ BitVec 64)))
            (not (and (bvult i len) (= (select s i) #x00000005)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "Expected sat or unknown for BV64 variant, got: {outputs:?}"
    );
}
