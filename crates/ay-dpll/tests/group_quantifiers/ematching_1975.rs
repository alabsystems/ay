// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for issue #1975 (verification-consumer mail): AUFLIA E-matching instantiates a triggered axiom
//! but the resulting UF↔LIA equality must be respected by LIA when checking comparisons.

use ntest::timeout;

fn assert_sat_or_unknown(outputs: &[String], label: &str) {
    assert!(
        outputs.len() == 1 && (outputs[0] == "sat" || outputs[0] == "unknown"),
        "{label}: expected sat or unknown, got: {outputs:?}"
    );
}

#[test]
#[timeout(60000)]
fn test_issue_1975_auflia_ematching_uf_lia_comparison() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun add_one (Int) Int)
        (declare-const y Int)
        (declare-const result Int)

        ; Axiom: add_one(x) = x + 1 (triggered)
        (assert (forall ((x Int)) (! (= (add_one x) (+ x 1)) :pattern ((add_one x)))))

        ; Precondition: y >= 0
        (assert (>= y 0))

        ; Body constraint: result = y + 1
        (assert (= result (+ y 1)))

        ; Negated postcondition: NOT(result > add_one(y))
        (assert (not (> result (add_one y))))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_sat_or_unknown(&outputs, "#1975 AUFLIA E-matching UF/LIA comparison");
}
