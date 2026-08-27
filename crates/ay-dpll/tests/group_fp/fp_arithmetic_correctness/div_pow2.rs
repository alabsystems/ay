// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp_arithmetic_correctness` to preserve test FQNs.

// Division by a power of two is encoded as the reciprocal multiply
// (`ay_fp::div_pow2`, #fp-div-pow2). These tests pin the SEMANTICS of that
// substitution, which is the only thing about it that can be wrong: the
// circuit it replaces is 7.5x larger but computes the same function.
//
// Two independent kinds of evidence, because either alone is weak:
//
// * DIFFERENTIAL, over all `2^16` inputs at once. The divisor is written
//   twice — once as a literal, which the recogniser folds, and once as a
//   variable CONSTRAINED to that literal, which it cannot fold — and the two
//   results are asserted different. `unsat` means the reciprocal multiply and
//   the full divider agree on every Float16 input, NaN and subnormals
//   included. Nothing here depends on anyone's opinion of what the right
//   answer is.
// * GROUND, against values taken from bitwuzla 0.9.1 (SymFPU), an
//   independent implementation — not from AY. These pin the cases a naive
//   "just decrement the exponent" rewrite gets wrong: subnormal results that
//   round differently per mode, and overflow to infinity.

/// The divisor as a constrained VARIABLE defeats the syntactic recogniser, so
/// this really does compare the two encodings rather than one with itself.
/// Any input on which they disagree makes this `sat`.
fn assert_div_pow2_matches_full_divider(rm: &str, divisor: &str) {
    let smt = format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const d (_ FloatingPoint 5 11))
        (assert (= d {divisor}))
        (assert (not (= (fp.div {rm} x {divisor}) (fp.div {rm} x d))))
        (check-sat)
    "#
    );
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "reciprocal-multiply and full-divider encodings disagree for \
         rm={rm} divisor={divisor}"
    );
}

/// Every rounding mode, over every Float16 input, dividing by 2.0.
#[test]
#[timeout(300_000)]
fn test_fp_div_pow2_agrees_with_divider_all_rounding_modes() {
    for rm in ["RNE", "RNA", "RTP", "RTN", "RTZ"] {
        assert_div_pow2_matches_full_divider(rm, "(fp #b0 #b10000 #b0000000000)");
    }
}

/// Divisors across the exponent range and both signs, including the smallest
/// and largest for which the reciprocal is still normal.
#[test]
#[timeout(300_000)]
fn test_fp_div_pow2_agrees_with_divider_across_divisors() {
    for divisor in [
        "(fp #b0 #b01111 #b0000000000)", // 1.0  = 2^0
        "(fp #b0 #b01110 #b0000000000)", // 0.5  = 2^-1
        "(fp #b1 #b10000 #b0000000000)", // -2.0
        "(fp #b0 #b00001 #b0000000000)", // 2^-14, smallest normal
        "(fp #b0 #b11101 #b0000000000)", // 2^14,  reciprocal 2^-14 still normal
    ] {
        assert_div_pow2_matches_full_divider("RNE", divisor);
    }
}

/// The recogniser descends through `fp.mul` of two powers of two, which is how
/// `exp_loop` spells `1.0`. The compound divisor must behave exactly like the
/// full divider too.
#[test]
#[timeout(300_000)]
fn test_fp_div_pow2_agrees_with_divider_for_compound_constant_divisor() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const d (_ FloatingPoint 5 11))
        (assert (= d (fp.mul RNE (fp #b0 #b01110 #b0000000000)
                                 (fp #b0 #b10000 #b0000000000))))
        (assert (not (= (fp.div RNE x (fp.mul RNE (fp #b0 #b01110 #b0000000000)
                                                  (fp #b0 #b10000 #b0000000000)))
                        (fp.div RNE x d))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "compound constant divisor (fp.mul RNE 0.5 2.0) must divide like 1.0"
    );
}

/// `(assert (= (fp.div rm x c) expected))` must be `sat` with `x` and the
/// result pinned, i.e. the encoding computes exactly `expected`.
fn assert_div_value(rm: &str, x: &str, divisor: &str, expected: &str, what: &str) {
    let smt = format!(
        r#"
        (set-logic QF_FP)
        (declare-const r (_ FloatingPoint 5 11))
        (assert (= r (fp.div {rm} {x} {divisor})))
        (assert (not (= r {expected})))
        (check-sat)
    "#
    );
    let outputs = crate::common::solve_vec(&smt);
    assert_eq!(outputs, vec!["unsat"], "{what}");
}

/// Subnormal results, where the rounding mode decides the answer. `2^-24 / 2`
/// is exactly half of the smallest subnormal: RNE ties to even (zero), RTP
/// rounds up to `2^-24`, RTN rounds down to zero. Values from bitwuzla.
#[test]
#[timeout(300_000)]
fn test_fp_div_pow2_subnormal_rounding_is_mode_dependent() {
    let min_subnormal = "(fp #b0 #b00000 #b0000000001)";
    let two = "(fp #b0 #b10000 #b0000000000)";
    let zero = "(fp #b0 #b00000 #b0000000000)";
    assert_div_value(
        "RNE",
        min_subnormal,
        two,
        zero,
        "2^-24 / 2.0 under RNE ties to even, i.e. +0",
    );
    assert_div_value(
        "RTP",
        min_subnormal,
        two,
        min_subnormal,
        "2^-24 / 2.0 under RTP rounds up to 2^-24",
    );
    assert_div_value(
        "RTN",
        min_subnormal,
        two,
        zero,
        "2^-24 / 2.0 under RTN rounds down to +0",
    );
    // 3 * 2^-24 / 2 = 1.5 * 2^-24; RNE ties to even gives 2 * 2^-24.
    assert_div_value(
        "RNE",
        "(fp #b0 #b00000 #b0000000011)",
        two,
        "(fp #b0 #b00000 #b0000000010)",
        "3*2^-24 / 2.0 under RNE ties to even",
    );
}

/// Dividing by 0.5 doubles, so the largest normal OVERFLOWS: RNE gives
/// infinity, RTZ gives the largest normal back. Values from bitwuzla.
#[test]
#[timeout(300_000)]
fn test_fp_div_pow2_overflow_is_mode_dependent() {
    let max_normal = "(fp #b0 #b11110 #b1111111111)";
    let half = "(fp #b0 #b01110 #b0000000000)";
    assert_div_value(
        "RNE",
        max_normal,
        half,
        "(fp #b0 #b11111 #b0000000000)",
        "65504 / 0.5 under RNE overflows to +oo",
    );
    assert_div_value(
        "RTZ",
        max_normal,
        half,
        max_normal,
        "65504 / 0.5 under RTZ stays at the largest normal",
    );
}

/// Signs, zeros and non-finite inputs. Values from bitwuzla.
#[test]
#[timeout(300_000)]
fn test_fp_div_pow2_signs_zeros_and_infinities() {
    let two = "(fp #b0 #b10000 #b0000000000)";
    let neg_two = "(fp #b1 #b10000 #b0000000000)";
    assert_div_value(
        "RNE",
        "(fp #b0 #b10000 #b1000000000)",
        neg_two,
        "(fp #b1 #b01111 #b1000000000)",
        "3.0 / -2.0 = -1.5",
    );
    assert_div_value(
        "RNE",
        "(fp #b1 #b00000 #b0000000000)",
        two,
        "(fp #b1 #b00000 #b0000000000)",
        "-0.0 / 2.0 = -0.0",
    );
    assert_div_value(
        "RNE",
        "(fp #b0 #b11111 #b0000000000)",
        two,
        "(fp #b0 #b11111 #b0000000000)",
        "+oo / 2.0 = +oo",
    );
    assert_div_value(
        "RNE",
        "(fp #b1 #b11111 #b0000000000)",
        neg_two,
        "(fp #b0 #b11111 #b0000000000)",
        "-oo / -2.0 = +oo",
    );
}

/// NaN in, NaN out — the reciprocal multiply must not turn it into a number.
#[test]
#[timeout(300_000)]
fn test_fp_div_pow2_nan_propagates() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (fp.div RNE (fp #b0 #b11111 #b1000000000)
                                            (fp #b0 #b10000 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "NaN / 2.0 must be NaN");
}

/// The one divisor this rewrite must DECLINE: `2^14` at Float16 has a normal
/// reciprocal, but `2^15` (the largest normal power of two) does not — its
/// reciprocal `2^-15` is subnormal. Taking the rewrite anyway would compute a
/// different function, so the full divider has to run and still be right.
#[test]
#[timeout(300_000)]
fn test_fp_div_by_largest_normal_power_of_two_is_still_correct() {
    // 2^15 = exponent field 30 (bias 15). 2^15 / 2^15 = 1.0.
    assert_div_value(
        "RNE",
        "(fp #b0 #b11110 #b0000000000)",
        "(fp #b0 #b11110 #b0000000000)",
        "(fp #b0 #b01111 #b0000000000)",
        "2^15 / 2^15 = 1.0 through the full divider",
    );
    assert_div_pow2_matches_full_divider("RNE", "(fp #b0 #b11110 #b0000000000)");
}
