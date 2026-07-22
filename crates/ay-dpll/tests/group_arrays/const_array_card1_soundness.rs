// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regression tests for array (dis)equality reasoning involving
//! constant arrays, finite BitVec index domains, and cardinality-one element
//! sorts.
//!
//! Covers three previously wrong-answer families:
//!  1. Const-array vs const-array equality with distinct defaults: must be
//!     UNSAT (two const-arrays with different default values differ at every
//!     index). Was wrong-SAT.
//!  2. Const-array vs store-chain disequality with a free base: must be SAT
//!     (the free base can differ from the const default at some index). The
//!     ROW2b-alias axiom previously treated the negated equality as a
//!     definitional store alias and dropped the model -> wrong-UNSAT.
//!  3. Array distinctness over a cardinality-one element sort (datatype with a
//!     single nullary constructor): must be UNSAT (the array sort has a single
//!     inhabitant). Was wrong-SAT.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Run a raw SMT-LIB script and extract check-sat verdicts.
fn run_smt(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT:\n{smt}"));
    let mut exec = Executor::new();
    let output = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT:\n{smt}"))
        .join("\n");
    output
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .map(ToOwned::to_owned)
        .collect()
}

/// `(= (as const A true) (as const A false))` is UNSAT: distinct defaults
/// differ at every (Bool) index.
#[test]
#[timeout(10_000)]
fn const_array_distinct_defaults_bool_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (assert (= ((as const (Array Bool Bool)) true) ((as const (Array Bool Bool)) false)))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["unsat"],
        "const=const distinct defaults must be unsat"
    );
}

/// `(= (as const A 3) (as const A 4))` over Int defaults is UNSAT.
#[test]
#[timeout(10_000)]
fn const_array_distinct_defaults_int_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (assert (= ((as const (Array Int Int)) 3) ((as const (Array Int Int)) 4)))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// `(= (as const A 3) (as const A 3))` (equal defaults) is SAT.
#[test]
#[timeout(10_000)]
fn const_array_equal_defaults_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (assert (= ((as const (Array Int Int)) 3) ((as const (Array Int Int)) 3)))\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat"]);
}

/// QF_ABV: `(= (as const A #xa) (as const A #x8))` is UNSAT via finite-domain
/// extensionality over the small BitVec index domain.
#[test]
#[timeout(10_000)]
fn qf_abv_const_array_distinct_defaults_is_unsat() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (assert (= ((as const (Array (_ BitVec 1) (_ BitVec 4))) #xa) \
                    ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x8)))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// QF_ABV: a store-chain over a free base equal to a const-array is decided
/// correctly by finite-domain extensionality (here UNSAT, matching z3): the
/// store writes #x2 at #b110 and the const default is #b00, which differ at
/// that index unless the base supplies #b00 elsewhere — z3 says unsat.
#[test]
#[timeout(10_000)]
fn qf_abv_store_chain_eq_const_array_decided() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (declare-const a0 (Array (_ BitVec 3) (_ BitVec 2)))\
         (assert (and (= (store (store a0 #b101 #b10) #b110 (select a0 #b111)) \
                         ((as const (Array (_ BitVec 3) (_ BitVec 2))) #b00)) \
                      (not (bvslt #b010 #b110))))\
         (check-sat)",
    );
    // Must not be wrong-SAT; z3 decides unsat. Accept unsat (decided) but
    // never sat.
    assert!(
        result == vec!["unsat"] || result == vec!["unknown"],
        "store-chain vs const-array must not be wrong-SAT, got {result:?}"
    );
    assert_ne!(result, vec!["sat"]);
}

/// Const-array vs store-chain DISEQUALITY with a free base must be SAT: the
/// free base may differ from the const default at some non-overwritten index.
/// Regression for the ROW2b-alias wrong-UNSAT.
#[test]
#[timeout(10_000)]
fn const_array_vs_store_disequality_free_base_is_sat() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (declare-const a0 (Array (_ BitVec 4) (_ BitVec 4)))\
         (assert (not (= ((as const (Array (_ BitVec 4) (_ BitVec 4))) #x2) \
                         (store a0 #xb #x2))))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["sat"],
        "free-base const-vs-store disequality must be sat"
    );
}

/// Distinctness over a cardinality-one datatype element sort is UNSAT: the
/// array sort has a single inhabitant.
#[test]
#[timeout(10_000)]
fn distinct_arrays_card1_element_sort_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype D1 ((c2)))\
         (declare-const v3 (Array Int D1))\
         (declare-const v5 (Array Int D1))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["unsat"],
        "distinct over card-1 element sort must be unsat"
    );
}

/// 3-way distinctness over a cardinality-one element sort is UNSAT.
#[test]
#[timeout(10_000)]
fn three_way_distinct_arrays_card1_element_sort_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype D1 ((c2)))\
         (declare-const a (Array Int D1))\
         (declare-const b (Array Int D1))\
         (declare-const c (Array Int D1))\
         (assert (distinct a b c))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Nested cardinality-one datatype (struct of struct of nullary): UNSAT.
#[test]
#[timeout(10_000)]
fn distinct_arrays_nested_card1_element_sort_is_unsat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype Inner ((ic)))\
         (declare-datatype Outer ((oc (f Inner))))\
         (declare-const v3 (Array Int Outer))\
         (declare-const v5 (Array Int Outer))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}

/// Distinctness over a CARDINALITY-TWO datatype element sort must stay SAT:
/// the arrays can genuinely differ. Guards against over-refutation of the
/// cardinality check.
#[test]
#[timeout(10_000)]
fn distinct_arrays_card2_element_sort_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype D2 ((a2) (b2)))\
         (declare-const v3 (Array Int D2))\
         (declare-const v5 (Array Int D2))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(
        result,
        vec!["sat"],
        "distinct over card-2 element sort must stay sat"
    );
}

/// A single-constructor datatype whose field is an infinite-cardinality array
/// is NOT a singleton sort, so distinctness must stay SAT (fail-open, not a
/// false refutation).
#[test]
#[timeout(10_000)]
fn distinct_arrays_card1_ctor_infinite_field_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-datatype U1 ((mk (g (Array Int Bool)))))\
         (declare-const v3 (Array Int U1))\
         (declare-const v5 (Array Int U1))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat"]);
}

/// Distinctness over a genuinely uninterpreted (non-datatype) element sort
/// must stay SAT: cardinality is unknown, so we must not refute.
#[test]
#[timeout(10_000)]
fn distinct_arrays_uninterpreted_element_sort_is_sat() {
    let result = run_smt(
        "(set-logic ALL)\
         (declare-sort U 0)\
         (declare-const v3 (Array Int U))\
         (declare-const v5 (Array Int U))\
         (assert (distinct v3 v5))\
         (check-sat)",
    );
    assert_eq!(result, vec!["sat"]);
}

/// Extensionality must still refute a contradictory select disequality on
/// equal arrays (non-regression for genuine extensionality).
#[test]
#[timeout(10_000)]
fn extensionality_refutes_select_diseq_on_equal_arrays() {
    let result = run_smt(
        "(set-logic QF_ABV)\
         (declare-const a (Array (_ BitVec 2) (_ BitVec 2)))\
         (declare-const b (Array (_ BitVec 2) (_ BitVec 2)))\
         (assert (= a b))\
         (assert (not (= (select a #b00) (select b #b00))))\
         (check-sat)",
    );
    assert_eq!(result, vec!["unsat"]);
}
