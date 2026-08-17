// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #6736: array axiom generation in `check-sat-assuming`
//! must see assumption-only array terms.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

#[test]
#[timeout(60_000)]
fn test_qf_ax_check_sat_assuming_array_term_only_in_assumption_6736() {
    let smt = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (check-sat-assuming ((not (= (select (store a i v) i) v))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn test_qf_auflia_check_sat_assuming_array_term_only_in_assumption_6736() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (declare-const x Int)
        (assert (= x 0))
        (check-sat-assuming ((not (= (select (store a i v) i) v))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn test_qf_auflia_assuming_closes_finite_bool_index_extensionality() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Bool Int))
        (declare-const b (Array Bool Int))
        (declare-const x Int)
        (assert (= x 0))
        (assert (= (select a false) (select b false)))
        (assert (= (select a true) (select b true)))
        (check-sat-assuming ((not (= a b))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn test_qf_auflia_assuming_closes_nested_finite_arrays_before_unsat_quarantine() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Bool (Array Bool Int)))
        (declare-const b (Array Bool (Array Bool Int)))
        (declare-const x Int)
        (assert (= x 0))
        (assert (= (select (select a false) false)
                   (select (select b false) false)))
        (assert (= (select (select a false) true)
                   (select (select b false) true)))
        (assert (= (select (select a true) false)
                   (select (select b true) false)))
        (assert (= (select (select a true) true)
                   (select (select b true) true)))
        (check-sat-assuming ((not (= a b))))
    "#;
    let commands = parse(smt).expect("nested finite-array assumption script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("nested finite-array assumption script should execute");
    assert_eq!(outputs, vec!["unknown"]);
    assert_eq!(
        exec.unknown_reason(),
        Some(ay_dpll::UnknownReason::Incomplete)
    );
    let stats = exec.statistics();
    assert_eq!(
        stats.get_int("smt.array.finite_ext.route_deferrals"),
        Some(1)
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.emitted_equalities"),
        Some(3),
        "the outer equality and both array-valued cells must close before the independent UNSAT quarantine fires"
    );
    assert_eq!(
        stats.get_string("unknown.cost_center"),
        Some("nested-array-unsat-quarantine")
    );
}

#[test]
#[timeout(60_000)]
fn test_qf_auflra_check_sat_assuming_array_term_only_in_assumption_6736() {
    let smt = r#"
        (set-logic QF_AUFLRA)
        (declare-const a (Array Real Real))
        (declare-const i Real)
        (declare-const v Real)
        (declare-const x Real)
        (assert (= x 0.0))
        (check-sat-assuming ((not (= (select (store a i v) i) v))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn test_qf_auflira_check_sat_assuming_array_term_only_in_assumption_6736() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const v Real)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= x 0))
        (assert (= y 0.0))
        (check-sat-assuming ((not (= (select (store a i v) i) v))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn test_qf_auflira_assuming_closes_finite_bool_index_extensionality() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-const a (Array Bool Real))
        (declare-const b (Array Bool Real))
        (declare-const x Int)
        (declare-const y Real)
        (assert (= x 0))
        (assert (= y 0.0))
        (assert (= (select a false) (select b false)))
        (assert (= (select a true) (select b true)))
        (check-sat-assuming ((not (= a b))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn test_qf_abv_check_sat_assuming_array_term_only_in_assumption_6736() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (check-sat-assuming ((not (= (select (store a i v) i) v))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[timeout(60_000)]
fn test_qf_aufbv_check_sat_assuming_array_term_only_in_assumption_6736() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= (f i) v))
        (check-sat-assuming ((not (= (select (store a i v) i) v))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}
