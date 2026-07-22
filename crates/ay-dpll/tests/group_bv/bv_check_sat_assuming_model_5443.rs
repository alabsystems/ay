// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #5443: check-sat-assuming BV SAT path stores no BvModel.
//!
//! Before the fix, the check-sat-assuming path in BV-family logics
//! called `solve_and_store_model` without extracting the BV model from
//! SAT bits, so `(get-value ...)` after an assumption-based SAT returned
//! empty/default BV values.

use ntest::timeout;

/// QF_BV: check-sat-assuming SAT then get-value returns correct BV value.
#[test]
#[timeout(60_000)]
fn test_bv_check_sat_assuming_get_value_5443() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const p Bool)
        (assert (= x #x2A))
        (assert (= p true))
        (check-sat-assuming (p))
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].to_lowercase().contains("#x2a"),
        "Expected #x2a in get-value output after check-sat-assuming, got: {}",
        outputs[1]
    );
}

/// QF_UFBV: check-sat-assuming SAT then get-value with UF.
#[test]
#[timeout(60_000)]
fn test_ufbv_check_sat_assuming_get_value_5443() {
    let smt = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const p Bool)
        (assert (= x #xFF))
        (assert (= (f x) #x01))
        (assert (= p true))
        (check-sat-assuming (p))
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].to_lowercase().contains("#xff"),
        "Expected #xff in get-value output after check-sat-assuming, got: {}",
        outputs[1]
    );
}

/// QF_ABV: check-sat-assuming SAT then get-value for BV term with arrays.
#[test]
#[timeout(60_000)]
fn test_abv_check_sat_assuming_get_value_5443() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const p Bool)
        (assert (= x #x42))
        (assert (= (select a x) #x10))
        (assert (= p true))
        (check-sat-assuming (p))
        (get-value (x))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].to_lowercase().contains("#x42"),
        "Expected #x42 in get-value output after check-sat-assuming, got: {}",
        outputs[1]
    );
}
