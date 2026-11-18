// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! A user symbol spelled like a variable AY mints while elaborating is a
//! symbol of its own. Each script gets the stated verdict from AY and, when a
//! z3 oracle is available, from z3.

use ntest::timeout;

/// The `sat`/`unsat`/`unknown` lines of `output`, in order.
fn verdicts(output: &[String]) -> Vec<&str> {
    output
        .iter()
        .map(String::as_str)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

/// AY answers `expected` through the CLI's authored boundary, and z3 agrees
/// when an oracle is available.
fn assert_verdicts(script: &str, expected: &[&str]) {
    let output = crate::common::solve_authored_vec(script);
    assert_eq!(verdicts(&output), expected, "{output:?}\n{script}");
    if crate::common::z3::check_z3_or_skip() {
        let z3 = crate::common::z3::solve_with_z3(script).expect("z3 answers");
        let z3_verdicts: Vec<&str> = z3
            .lines()
            .map(str::trim)
            .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
            .collect();
        assert_eq!(z3_verdicts, expected, "z3: {z3}");
    }
}

/// Hunt probe `binder-n/qs8`: the inner quantifier of the first assertion
/// has the outer binder, minted as `x_0`, free.
const BINDER_THEN_CONSTANT: &str = "(set-logic LIA)\n\
    (assert (forall ((x Int)) (or (< x 1) (> x 1) (forall ((y Int)) (=> (> y x) (> y 0))))))\n\
    (declare-const x_0 Int)\n\
    (assert (forall ((w Int)) (=> (> w x_0) (> w 0))))\n\
    (assert (= x_0 (- 1)))\n\
    (check-sat)\n";

/// Hunt probe `binder-n/qs8p`: the user part inside `push`/`pop`.
const BINDER_THEN_SCOPED_CONSTANT: &str = "(set-logic LIA)\n\
    (assert (forall ((x Int)) (or (< x 1) (> x 1) (forall ((y Int)) (=> (> y x) (> y 0))))))\n\
    (check-sat)\n\
    (push 1)\n\
    (declare-const x_0 Int)\n\
    (assert (forall ((w Int)) (=> (> w x_0) (> w 0))))\n\
    (assert (= x_0 (- 1)))\n\
    (check-sat)\n\
    (pop 1)\n\
    (check-sat)\n";

/// Hunt probe `binder-names/vdef`: a quantifier in a `define-fun` body has
/// the formal `x` free.
const FORMAL_THEN_CONSTANT: &str =
    "(define-fun h ((x Int)) Bool (forall ((z Int)) (>= (+ z x) z)))\n\
    (declare-const x Int)\n\
    (assert (forall ((w Int)) (>= (+ w x) w)))\n\
    (assert (< x 0))\n\
    (check-sat)\n";

/// Hunt probe `powneg/wsat_alpha0`.
const NEGATIVE_POWER_WITNESS_SPELLING: &str = "(declare-const x Real)\n\
    (assert (= x 0.0))\n\
    (assert (forall ((b Bool)) (or b (= (^ x (- 1)) 0.0))))\n\
    (declare-const |pow_neg_at_zero_2| Real)\n\
    (assert (forall ((c Bool)) (or c (= (ite (= x 0.0) |pow_neg_at_zero_2| (/ 1.0 x)) 0.0))))\n\
    (assert (= |pow_neg_at_zero_2| 5.0))\n\
    (check-sat)\n";

#[test]
#[timeout(60_000)]
fn a_constant_spelled_like_an_earlier_binder_is_not_that_binder() {
    assert_verdicts(BINDER_THEN_CONSTANT, &["unsat"]);
}

#[test]
#[timeout(60_000)]
fn a_scoped_constant_spelled_like_an_earlier_binder_is_not_that_binder() {
    assert_verdicts(BINDER_THEN_SCOPED_CONSTANT, &["sat", "unsat", "sat"]);
}

#[test]
#[timeout(60_000)]
fn a_constant_spelled_like_an_earlier_formal_is_not_that_formal() {
    assert_verdicts(FORMAL_THEN_CONSTANT, &["unsat"]);
}

#[test]
#[timeout(60_000)]
fn a_real_spelled_like_the_old_negative_power_witness_is_not_the_witness() {
    assert_verdicts(NEGATIVE_POWER_WITNESS_SPELLING, &["unsat"]);
}

#[test]
#[timeout(60_000)]
fn the_negated_twin_of_the_negative_power_script_is_not_unsat() {
    // Hunt probe `powneg/wunsat_alpha0`; z3 answers `sat`. The test asserts
    // only that AY does not answer `unsat`.
    let script = "(declare-const x Real)\n\
        (assert (= x 0.0))\n\
        (assert (forall ((b Bool)) (or b (= (^ x (- 1)) 0.0))))\n\
        (declare-const |pow_neg_at_zero_2| Real)\n\
        (assert (not (forall ((c Bool)) (or c (= (ite (= x 0.0) |pow_neg_at_zero_2| (/ 1.0 x)) 0.0)))))\n\
        (check-sat)\n";
    let output = crate::common::solve_authored_vec(script);
    assert_ne!(verdicts(&output), ["unsat"], "{output:?}");
    if crate::common::z3::check_z3_or_skip() {
        let z3 = crate::common::z3::solve_with_z3(script).expect("z3 answers");
        assert_eq!(z3.lines().next().map(str::trim), Some("sat"), "z3: {z3}");
    }
}

#[test]
#[timeout(60_000)]
fn get_value_of_a_negative_power_reports_the_asserted_value() {
    // Hunt probe `powneg/gv`.
    let script = "(set-option :produce-models true)\n\
        (declare-const x Real)\n\
        (assert (= x 0.0))\n\
        (assert (= (^ x (- 1)) 0.0))\n\
        (check-sat)\n\
        (get-value ((^ x (- 1))))\n";
    let output = crate::common::solve_authored_vec(script);
    assert_eq!(verdicts(&output), ["sat"], "{output:?}");
    let values: String = output[1..]
        .join(" ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(values, "(((^ x (- 1)) 0.0))", "{output:?}");
}

#[test]
#[timeout(60_000)]
fn the_model_of_a_constant_spelled_like_a_binder_prints_the_users_spelling() {
    let script = "(set-option :produce-models true)\n\
        (assert (forall ((x Int)) (or (< x 1) (> x 1) (forall ((y Int)) (=> (> y x) (> y 0))))))\n\
        (declare-const x_0 Int)\n\
        (assert (= x_0 7))\n\
        (check-sat)\n\
        (get-value (x_0))\n\
        (get-model)\n";
    let output = crate::common::solve_authored_vec(script);
    assert_eq!(verdicts(&output), ["sat"], "{output:?}");
    let text = output[1..].join(" ");
    assert!(text.contains("((x_0 7))"), "{output:?}");
    assert!(text.contains("(define-fun x_0 () Int"), "{output:?}");
    assert!(!text.contains("__ay_"), "{output:?}");
}
