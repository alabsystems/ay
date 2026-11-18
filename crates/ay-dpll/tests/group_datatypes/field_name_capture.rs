// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! A user constant spelled like a single-constructor field path
//! (`<root>!<selector>`) is a constant of its own, distinct from the field the
//! eager datatype elimination mints for `(<selector> <root>)`, in either
//! declaration order. Each script is `sat` in AY and, when a z3 oracle is
//! available, in z3.

use ntest::timeout;

/// The `sat`/`unsat`/`unknown` line of `output`.
fn verdict(output: &[String]) -> &str {
    output
        .iter()
        .map(String::as_str)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| panic!("no verdict in {output:?}"))
}

/// AY answers `expected` through the CLI's authored boundary, and z3 agrees
/// when an oracle is available.
fn assert_verdict(script: &str, expected: &str) {
    let output = crate::common::solve_authored_vec(script);
    assert_eq!(verdict(&output), expected, "{output:?}\n{script}");
    if crate::common::z3::check_z3_or_skip() {
        let z3 = crate::common::z3::solve_with_z3(script).expect("z3 answers");
        assert_eq!(z3.lines().next().map(str::trim), Some(expected), "z3: {z3}");
    }
}

const BEFORE_ROOT: &str = "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
    (declare-const p!x Int)\n\
    (declare-const p P)\n\
    (assert (= p!x 1))\n\
    (assert (= (x p) 2))\n\
    (check-sat)\n";

const AFTER_ROOT: &str = "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
    (declare-const p P)\n\
    (declare-const p!x Int)\n\
    (assert (= p!x 1))\n\
    (assert (= (x p) 2))\n\
    (check-sat)\n";

const EMPTY_SELECTOR: &str = "(declare-datatypes ((P 0)) (((mk (|| Int)))))\n\
    (declare-const p! Int)\n\
    (declare-const p P)\n\
    (assert (= p! 1))\n\
    (assert (= (|| p) 2))\n\
    (check-sat)\n";

const NESTED: &str = "(declare-datatypes ((I 0)) (((mkI (top Int) (bot Int)))))\n\
    (declare-datatypes ((O 0)) (((mkO (right I) (lft Int)))))\n\
    (declare-const s!right!top Int)\n\
    (declare-const s!lft Int)\n\
    (declare-const s O)\n\
    (assert (= s!right!top 1))\n\
    (assert (= (top (right s)) 2))\n\
    (assert (= s!lft 3))\n\
    (assert (= (lft s) 4))\n\
    (check-sat)\n";

const DECLARE_FUN_ROOT: &str = "(declare-datatypes ((P 0)) (((mk (x Int)))))\n\
    (declare-fun p!x () Int)\n\
    (declare-fun p () P)\n\
    (assert (= p!x 1))\n\
    (assert (= (x p) 2))\n\
    (check-sat)\n";

#[test]
#[timeout(60_000)]
fn a_user_constant_declared_before_the_root_is_not_its_field() {
    assert_verdict(BEFORE_ROOT, "sat");
}

#[test]
#[timeout(60_000)]
fn a_user_constant_declared_after_the_root_is_not_its_field() {
    assert_verdict(AFTER_ROOT, "sat");
}

#[test]
#[timeout(60_000)]
fn an_empty_selector_field_is_not_the_root_spelled_with_a_bang() {
    assert_verdict(EMPTY_SELECTOR, "sat");
}

#[test]
#[timeout(60_000)]
fn nested_fields_are_not_user_constants_spelled_like_their_path() {
    assert_verdict(NESTED, "sat");
}

#[test]
#[timeout(60_000)]
fn a_nullary_declare_fun_root_does_not_capture_its_field_spelling() {
    assert_verdict(DECLARE_FUN_ROOT, "sat");
}

#[test]
#[timeout(60_000)]
fn the_model_keeps_the_user_constant_and_the_field_apart() {
    let script =
        format!("(set-option :produce-models true)\n{BEFORE_ROOT}(get-value (p!x (x p) p))\n");
    let output = crate::common::solve_authored_vec(&script);
    assert_eq!(verdict(&output), "sat", "{output:?}");
    let values: String = output[1..]
        .join(" ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(values, "((p!x 1) ((x p) 2) (p (mk 2)))", "{output:?}");
}
