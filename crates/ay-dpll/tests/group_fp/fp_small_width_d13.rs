// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Frontend-to-FP-circuit controls for the minimum legal formats.
//!
//! Expectations below use exact Fraction arithmetic from the checked-in
//! `scripts/differential/gen/strings-dt-fp/fpref.py`, not a Z3 FMA oracle.

use ntest::timeout;

const FMA_23_SAT: &str = r#"
    (set-logic QF_FP)
    (declare-const x (_ FloatingPoint 2 3))
    (declare-const y (_ FloatingPoint 2 3))
    (declare-const z (_ FloatingPoint 2 3))
    (assert (= x (fp #b1 #b10 #b00)))
    (assert (= y (fp #b0 #b00 #b11)))
    (assert (= z (fp #b0 #b10 #b10)))
    (assert (= (fp.fma RTN x y z) (fp #b0 #b01 #b10)))
    (check-sat)
"#;

const FMA_23_UNSAT: &str = r#"
    (set-logic QF_FP)
    (declare-const x (_ FloatingPoint 2 3))
    (declare-const y (_ FloatingPoint 2 3))
    (declare-const z (_ FloatingPoint 2 3))
    (assert (= x (fp #b1 #b10 #b00)))
    (assert (= y (fp #b0 #b00 #b11)))
    (assert (= z (fp #b0 #b10 #b10)))
    (assert (not (= (fp.fma RTN x y z) (fp #b0 #b01 #b10))))
    (check-sat)
"#;

const UINT24_23_SAT: &str = r#"
    (set-logic QF_FPBV)
    (declare-const b (_ BitVec 24))
    (declare-const x (_ FloatingPoint 2 3))
    (assert (= b #x000001))
    (assert (= x ((_ to_fp_unsigned 2 3) RNE b)))
    (assert (= x (fp #b0 #b01 #b00)))
    (check-sat)
"#;

const UINT24_23_UNSAT: &str = r#"
    (set-logic QF_FPBV)
    (declare-const b (_ BitVec 24))
    (declare-const x (_ FloatingPoint 2 3))
    (assert (= b #x000001))
    (assert (= x ((_ to_fp_unsigned 2 3) RNE b)))
    (assert (not (= x (fp #b0 #b01 #b00))))
    (check-sat)
"#;

fn assert_exact_in_both_postures(script: &str, expected: &str) {
    for (posture, solve) in [
        (
            "generic",
            crate::common::solve_vec as fn(&str) -> Vec<String>,
        ),
        (
            "authored",
            crate::common::solve_authored_vec as fn(&str) -> Vec<String>,
        ),
    ] {
        let output = solve(script);
        assert_eq!(output, vec![expected], "{posture} posture: {script}");
    }
}

fn assert_fp22_opposite_controls(prelude: &str, expression: &str, expected: &str) {
    // General SMT-LIB `=` distinguishes the two signed zeros; `fp.eq` does not.
    let yes = format!("{prelude}\n(assert (= {expression} {expected}))\n(check-sat)");
    let no = format!("{prelude}\n(assert (not (= {expression} {expected})))\n(check-sat)");
    assert_exact_in_both_postures(&yes, "sat");
    assert_exact_in_both_postures(&no, "unsat");
}

#[test]
#[timeout(120_000)]
fn fp23_fma_and_uint24_conversion_have_decisive_opposite_controls() {
    // (-2)*(3/4)+3 = 3/2 exactly in FP(2,3). This is the D13 FMA witness.
    assert_exact_in_both_postures(FMA_23_SAT, "sat");
    assert_exact_in_both_postures(FMA_23_UNSAT, "unsat");
    // Unsigned 24-bit one converts to exact FP(2,3) one.
    assert_exact_in_both_postures(UINT24_23_SAT, "sat");
    assert_exact_in_both_postures(UINT24_23_UNSAT, "unsat");
}

#[test]
#[timeout(120_000)]
fn minimum_fp22_fma_ties_and_signed_zero_are_exact() {
    let half = "(fp #b0 #b00 #b1)";
    let pos_zero = "(_ +zero 2 2)";
    let neg_zero = "(_ -zero 2 2)";
    let neg_one = "(fp #b1 #b01 #b0)";
    for (x, y, z, rm, expected) in [
        // 1/2 * 1/2 + 0 = 1/4, halfway between +0 and the min subnormal.
        (half, half, pos_zero, "RNE", pos_zero),
        (half, half, pos_zero, "RNA", half),
        // +0 * -1 = -0; opposite-sign zeros add to +0 in these modes.
        (pos_zero, neg_one, pos_zero, "RNE", pos_zero),
        (pos_zero, neg_one, pos_zero, "RNA", pos_zero),
        (pos_zero, neg_one, pos_zero, "RTN", neg_zero),
    ] {
        let prelude = format!(
            "(set-logic QF_FP)
             (declare-const x (_ FloatingPoint 2 2))
             (declare-const y (_ FloatingPoint 2 2))
             (declare-const z (_ FloatingPoint 2 2))
             (assert (= x {x})) (assert (= y {y})) (assert (= z {z}))"
        );
        let expression = format!("(fp.fma {rm} x y z)");
        assert_fp22_opposite_controls(&prelude, &expression, expected);
    }
}

#[test]
#[timeout(120_000)]
fn minimum_fp22_division_underflow_respects_rtp() {
    // (1/2)/3 = 1/6, below the minimum positive FP(2,2) subnormal 1/2.
    // RTP rounds to +1/2; RNE instead rounds to +0.
    let half = "(fp #b0 #b00 #b1)";
    let three = "(fp #b0 #b10 #b1)";
    for (rm, expected) in [("RTP", half), ("RNE", "(_ +zero 2 2)")] {
        let prelude = format!(
            "(set-logic QF_FP)
             (declare-const x (_ FloatingPoint 2 2))
             (declare-const y (_ FloatingPoint 2 2))
             (assert (= x {half})) (assert (= y {three}))"
        );
        let expression = format!("(fp.div {rm} x y)");
        assert_fp22_opposite_controls(&prelude, &expression, expected);
    }
}

#[test]
#[timeout(120_000)]
fn minimum_fp22_fma_get_value_reports_functional_result() {
    let script = r#"
        (set-logic QF_FP)
        (set-option :produce-models true)
        (declare-const x (_ FloatingPoint 2 2))
        (assert (= x (fp #b0 #b00 #b1)))
        (check-sat)
        (get-value ((fp.fma RNA x x (_ +zero 2 2))))
    "#;
    for (posture, solve) in [
        (
            "generic",
            crate::common::solve_vec as fn(&str) -> Vec<String>,
        ),
        (
            "authored",
            crate::common::solve_authored_vec as fn(&str) -> Vec<String>,
        ),
    ] {
        let output = solve(script);
        assert_eq!(output.len(), 2, "{posture} posture: {output:?}");
        assert_eq!(output[0], "sat", "{posture} posture: {output:?}");
        assert!(
            output[1].contains("(fp #b0 #b00 #b1)"),
            "{posture} must evaluate the FMA expression to +1/2: {output:?}"
        );
    }
}
