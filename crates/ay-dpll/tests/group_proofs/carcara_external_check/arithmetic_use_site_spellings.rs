// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Use-site arithmetic spellings the printer refused or published `invalid`.
//!
//! The OR-substitution fuzz (1,200 QF_LIA files, z3 5.1.0 and pinned Carcara
//! 1.1.0 as oracles) measured that a quarter of certified UNSATs refused
//! `(get-proof)`, and that the scalar OR reorder bridge moved five rows from
//! a Carcara-valid document to a refusal. The causes are printer gaps, not
//! the bridge: a congruence over an authored spelling the frontend
//! normalized (`(+ x1 0)`, `-2`, `(>= x2 3)`), an equality the override prints
//! in the author's operand order, and `evaluate` with a negative value. Each
//! row below is a measured file of that fuzz; each must print a hole-free
//! document pinned Carcara accepts with no allowance.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict,
};
use ntest::timeout;

fn assert_valid(label: &str, problem: &str) {
    let proof = solve_unsat_and_get_proof(problem, label);
    for forbidden in [":rule hole", ":rule trust"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must re-derive every step:\n{proof}"
        );
    }
}

const OR_REORDER_ZERO_SUMMAND_O5_188: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (and (= x0 x4) (= x1 (+ x0 (- 2))) (= x4 x3) (= b0 (or (>= x1 (+ x3 (- 3))) (>= x3 (- 1)))) (= b1 (or (> x4 (+ x0 2)) (< x1 (+ x2 2)) (< x1 0))) (= b2 (or (<= x0 (+ x1 (- 3))) (> x0 (- 2)) (> x1 (+ x4 0)))) (or (<= x1 (+ x0 2)) (< x4 2)) (or b1 (< x4 (+ x1 2)) (>= x1 (+ x4 3)) (= x4 (+ x0 (- 3)))) (or (= x0 (+ x1 0)) (< x0 (- 1)) (= x0 (+ x4 (- 2))) (< x3 (- 3))) (or (= x1 (+ x2 2)) (= x1 (+ x3 3)) (<= x4 (+ x3 3))) (or b0 (= x1 (+ x3 (- 3))) (= x4 (+ x1 3))) (>= x1 3)))
(check-sat)
"#;

/// The scalar OR reorder bridge's `cong` over an authored `(+ x1 0)`: `left="(+ x1 0)"; right="x1"` (additive identity, `sum_simplify`).
#[test]
#[timeout(120_000)]
fn or_reorder_zero_summand_o5_188() {
    assert_valid(
        "or_reorder_zero_summand_o5_188",
        OR_REORDER_ZERO_SUMMAND_O5_188,
    );
}

const OR_REORDER_ZERO_SUMMAND_LENIENT_LITERALS_O5_188: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (and (= x0 x4) (= x1 (+ x0 -2)) (= x4 x3) (= b0 (or (>= x1 (+ x3 -3)) (>= x3 -1))) (= b1 (or (> x4 (+ x0 2)) (< x1 (+ x2 2)) (< x1 0))) (= b2 (or (<= x0 (+ x1 -3)) (> x0 -2) (> x1 (+ x4 0)))) (or (<= x1 (+ x0 2)) (< x4 2)) (or b1 (< x4 (+ x1 2)) (>= x1 (+ x4 3)) (= x4 (+ x0 -3))) (or (= x0 (+ x1 0)) (< x0 -1) (= x0 (+ x4 -2)) (< x3 -3)) (or (= x1 (+ x2 2)) (= x1 (+ x3 3)) (<= x4 (+ x3 3))) (or b0 (= x1 (+ x3 -3)) (= x4 (+ x1 3))) (>= x1 3)))
(check-sat)
"#;

/// The same row with the lenient `-2` literals the fuzz generator wrote.
#[test]
#[timeout(120_000)]
fn or_reorder_zero_summand_lenient_literals_o5_188() {
    assert_valid(
        "or_reorder_zero_summand_lenient_literals_o5_188",
        OR_REORDER_ZERO_SUMMAND_LENIENT_LITERALS_O5_188,
    );
}

const FLIPPED_AUTHORED_EQUALITY_PREMISE_O6_202: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun b0 () Bool)
(assert (and (= x3 (+ x2 0)) (= x3 x0) (= b0 (or (< x1 3) (> x3 (- 2)) (<= x0 (+ x1 (- 1))) (< x3 3))) (or (< x2 (- 3)) (< x2 0) (< x2 (+ x3 0))) (or (<= x0 (+ x1 (- 2))) (> x0 (+ x1 (- 3))) (= x2 0) (< x2 0)) (or (< x3 (+ x0 0)) (> x0 (+ x1 3))) (< x0 (+ x1 (- 1)))))
(check-sat)
"#;

/// An authored `(= x2 (+ x0 0))` interned as `(= x0 x2)` and cited as a congruence premise.
#[test]
#[timeout(120_000)]
fn flipped_authored_equality_premise_o6_202() {
    assert_valid(
        "flipped_authored_equality_premise_o6_202",
        FLIPPED_AUTHORED_EQUALITY_PREMISE_O6_202,
    );
}

const COMPARISON_REVERSAL_AT_A_USE_SITE_O6_210: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(assert (= x2 x1))
(assert (= b0 (or (= x0 (+ x2 (- 2))) (= x2 0) (<= x0 0))))
(assert (= b1 (or (> x2 (- 1)) (> x2 (+ x1 2)) (= x2 (+ x0 (- 2))))))
(assert (or (not b0) (> x2 (+ x1 1)) (= x2 (+ x0 (- 2))) (< x0 (+ x2 1))))
(assert (or (>= x0 (+ x1 2)) (< x2 (- 3)) (<= x2 (- 2)) (<= x1 (- 3))))
(assert (or (>= x2 3) (> x1 (- 1)) (> x2 0)))
(assert (or (< x0 (+ x1 3)) (< x0 (+ x2 3)) b0))
(assert (= x2 (+ x1 (- 2))))
(assert (<= x1 1))
(assert (< x1 (- 1)))
(check-sat)
"#;

/// `left="(<= 3 x2)"; right="(>= x2 3)"` at a disjunct position (comparison reversal as a use-site leaf).
#[test]
#[timeout(120_000)]
fn comparison_reversal_at_a_use_site_o6_210() {
    assert_valid(
        "comparison_reversal_at_a_use_site_o6_210",
        COMPARISON_REVERSAL_AT_A_USE_SITE_O6_210,
    );
}

const FLIPPED_AUTHORED_EQUALITY_APPLICATION_O7_223: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (and (= x2 (+ x0 0)) (= b0 (or (= x1 (+ x2 0)) (> x1 0))) (= b1 (or (>= x1 1) (> x1 (+ x0 1)))) (= b2 (or (<= x0 2) (= x0 1))) (or (= x1 (+ x2 (- 2))) (<= x0 (- 2))) (or (>= x2 0) (> x2 (+ x1 1)) (<= x0 (- 2)) (> x0 0)) (or (not b2) (< x2 (+ x1 0)) (<= x0 (+ x1 0))) (or b0 (> x0 1) (<= x2 (+ x0 2)) (< x2 (+ x1 (- 2)))) (= x1 (+ x2 (- 3))) (= x2 3)))
(check-sat)
"#;

/// `left="x2"; right="x0"`: the congruence's own left equality prints in the author's order.
#[test]
#[timeout(120_000)]
fn flipped_authored_equality_application_o7_223() {
    assert_valid(
        "flipped_authored_equality_application_o7_223",
        FLIPPED_AUTHORED_EQUALITY_APPLICATION_O7_223,
    );
}

const REVERSED_ORDER_OPERATOR_WITH_ZERO_SUMMAND_O7_297: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(assert (and (= x5 (+ x3 (- 2))) (= x0 (+ x3 1)) (= x5 x2) (= b0 (or (= x6 (+ x5 (- 2))) (>= x3 (+ x5 0)) (<= x4 (+ x5 (- 3))))) (= b1 (or (< x2 3) (< x0 (+ x5 (- 2))))) (or (< x1 0) (>= x5 1) (<= x3 1)) (or (> x5 (+ x2 0)) (= x6 (+ x0 2)) (>= x6 1)) (or (> x4 (+ x2 2)) (>= x0 1)) (<= x0 2) (< x0 3) (= x2 (+ x6 (- 1)))))
(check-sat)
"#;

/// `(> x5 (+ x2 0))` over the interned `(< x2 x5)`: the converse operator AND a zero summand on one side.
#[test]
#[timeout(120_000)]
fn reversed_order_operator_with_zero_summand_o7_297() {
    assert_valid(
        "reversed_order_operator_with_zero_summand_o7_297",
        REVERSED_ORDER_OPERATOR_WITH_ZERO_SUMMAND_O7_297,
    );
}

const NEGATIVE_EVALUATE_VALUE_O6_12: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(assert (and (= x0 (+ x3 (- 1))) (= x2 (+ x4 (- 2))) (= b0 (or (>= x2 (+ x1 (- 3))) (<= x1 (- 2)) (>= x0 3) (= x2 (- 3)))) (= b1 (or (> x1 (+ x0 0)) (> x1 (+ x4 0)))) (= b2 (or (< x1 1) (= x1 (+ x0 (- 3))) (<= x3 (+ x1 (- 2))))) (or b0 (>= x0 (- 3)) (<= x4 (+ x0 0))) (or (< x4 0) (= x2 3) b0 (= x4 (+ x1 (- 3)))) (or (> x1 (+ x3 1)) (< x0 (+ x3 2))) (or (= x4 (- 2)) (>= x0 (- 1)) (= x4 (+ x0 2)) (<= x0 (- 3))) (or (>= x0 0) (not b1) (< x0 2)) (> x2 (+ x4 2)) (= x1 2) (>= x4 0) (= x4 (- 3))))
(check-sat)
"#;

/// An `evaluate` step concluding `(= (+ (- 3) 2) (- 1))`, which pinned Carcara refuses as printed.
#[test]
#[timeout(120_000)]
fn negative_evaluate_value_o6_12() {
    assert_valid(
        "negative_evaluate_value_o6_12",
        NEGATIVE_EVALUATE_VALUE_O6_12,
    );
}

const LENIENT_NEGATIVE_LITERAL_CONG_O6_341: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(assert (and (= x1 (+ x2 -2)) (= x0 x2) (= x1 x0) (= b0 (or (<= x2 -1) (> x0 (+ x2 0)))) (= b1 (or (> x0 (+ x1 0)) (= x1 2) (< x1 (+ x2 3)))) (or b1 (= x0 -2) (>= x0 -3) (= x2 (+ x0 -1))) (or (<= x1 -3) (< x0 -3)) (or (<= x0 1) (= x0 2) (< x2 (+ x1 0)) (<= x2 (+ x1 1))) (or (< x0 (+ x1 3)) (not b1) (> x0 (+ x2 0)) (= x0 3)) (or (<= x1 (+ x2 -1)) (> x1 2) (= x0 3) (< x0 -1)) (> x2 1) (< x2 (+ x0 2))))
(check-sat)
"#;

/// `left="-2"; right="(- 2)"`: the lenient literal against the printed unary minus (`minus_simplify`).
#[test]
#[timeout(120_000)]
fn lenient_negative_literal_cong_o6_341() {
    assert_valid(
        "lenient_negative_literal_cong_o6_341",
        LENIENT_NEGATIVE_LITERAL_CONG_O6_341,
    );
}
