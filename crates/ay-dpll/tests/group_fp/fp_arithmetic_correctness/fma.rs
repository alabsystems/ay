// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `fp_arithmetic_correctness` to preserve test FQNs.

/// fp.fma: fma(2.0, 3.0, 4.0) = 10.0 (2*3+4 = 10, single rounding).
#[test]
#[timeout(60_000)]
fn test_fp_fma_two_three_four() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 5 11))
        (declare-const b (_ FloatingPoint 5 11))
        (declare-const c (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= a (fp #b0 #b10000 #b0000000000)))
        (assert (= b (fp #b0 #b10000 #b1000000000)))
        (assert (= c (fp #b0 #b10001 #b0000000000)))
        (assert (= z (fp.fma RNE a b c)))
        (assert (fp.eq z (fp #b0 #b10010 #b0100000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "fma(2.0, 3.0, 4.0) should equal 10.0");
}

/// fp.fma: fma(1.0, 1.0, 0.0) = 1.0 (identity-like).
#[test]
#[timeout(60_000)]
fn test_fp_fma_identity() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 5 11))
        (declare-const b (_ FloatingPoint 5 11))
        (declare-const c (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= a (fp #b0 #b01111 #b0000000000)))
        (assert (= b (fp #b0 #b01111 #b0000000000)))
        (assert (= c (_ +zero 5 11)))
        (assert (= z (fp.fma RNE a b c)))
        (assert (fp.eq z (fp #b0 #b01111 #b0000000000)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "fma(1.0, 1.0, 0.0) should equal 1.0");
}

/// fp.fma: fma(inf, 0, x) should be NaN.
#[test]
#[timeout(60_000)]
fn test_fp_fma_inf_times_zero_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const a (_ FloatingPoint 5 11))
        (declare-const b (_ FloatingPoint 5 11))
        (declare-const c (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= a (_ +oo 5 11)))
        (assert (= b (_ +zero 5 11)))
        (assert (= c (fp #b0 #b01111 #b0000000000)))
        (assert (= z (fp.fma RNE a b c)))
        (assert (fp.isNaN z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "fma(+inf, 0, 1.0) should be NaN");
}

/// fp.fma: fma(2.0, -3.0, 4.0) = -2.0 (negative product plus positive addend)
/// 2.0 * (-3.0) + 4.0 = -6.0 + 4.0 = -2.0
/// Float16: -3.0 = (fp #b1 #b10000 #b1000000000), -2.0 = (fp #b1 #b10000 #b0000000000)
#[test]
#[timeout(60_000)]
fn test_fp_fma_neg_product() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (fp #b0 #b10000 #b0000000000)
                (fp #b1 #b10000 #b1000000000)
                (fp #b0 #b10001 #b0000000000))
            (fp #b1 #b10000 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(2.0, -3.0, 4.0) should be -2.0");
}

/// fp.fma: fma(a, b, NaN) = NaN (NaN propagation from addend)
#[test]
#[timeout(60_000)]
fn test_fp_fma_nan_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (fp #b0 #b01111 #b0000000000)
                (fp #b0 #b10000 #b0000000000)
                (_ NaN 5 11)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(1.0, 2.0, NaN) should be NaN");
}

/// fp.fma: fma(+inf, 1.0, -inf) = NaN (inf + (-inf) cancellation)
#[test]
#[timeout(60_000)]
fn test_fp_fma_inf_cancel() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +oo 5 11)
                (fp #b0 #b01111 #b0000000000)
                (_ -oo 5 11)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(+inf, 1.0, -inf) should be NaN");
}

// =========================================================================
// fp.fma zero-factor rewrite (Z3 PR #9038 / issue #8185)
//
// When one multiplicand is a concrete FP zero, the fma bit-blast is
// replaced by a reduced encoding:
//   ite(isNaN(other) | isInf(other), NaN, add(product_zero, z))
// where product_zero's sign = sign(zero) XOR sign(other).
// =========================================================================

/// fma(+0, 2.0, 0.5) = 0.5 (0 * finite + c = c for nonzero c).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_pos_zero_times_finite() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(+0, 2.0, 0.5) should equal 0.5");
}

/// fma(-0, 2.0, 0.5) = 0.5 (sign(-0 * +2.0) = -0; -0 + 0.5 = 0.5).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_neg_zero_times_pos_finite() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ -zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(-0, 2.0, 0.5) should equal 0.5");
}

/// fma(+0, +inf, 0.5) = NaN (0 * inf = NaN, NaN + anything = NaN).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_zero_times_inf_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +zero 5 11)
                (_ +oo 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, +inf, 0.5) should be NaN (0 * inf = NaN)"
    );
}

/// fma(+0, NaN, 0.5) = NaN (NaN propagation through multiplication).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_zero_times_nan_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +zero 5 11)
                (_ NaN 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, NaN, 0.5) should be NaN (NaN propagation)"
    );
}

/// fma(+0, -1.0, +0) = +0 under RNE (sign(+0 * -1) = -0; -0 + +0 = +0).
/// IEEE 754 § 6.3: the sign of a sum of zeros of opposite sign is +0
/// under RNE, RNA, RTP, RTZ (only RTN gives -0).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_sign_rne() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ +zero 5 11)
                (fp #b1 #b01111 #b0000000000)
                (_ +zero 5 11))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, -1.0, +0) RNE: (-0)+(+0) = +0"
    );
}

/// fma(-0, -1.0, -0) = -0 (sign(-0 * -1) = +0; +0 + -0 = +0 under RNE, but
/// here addend is -0 and product is +0, so (+0)+(-0) = +0 under RNE.
/// We only check structural result: the sum is zero (not infinity/NaN).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_neg_zero_neg_finite_is_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isZero
            (fp.fma RNE
                (_ -zero 5 11)
                (fp #b1 #b01111 #b0000000000)
                (_ -zero 5 11)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(-0, -1.0, -0) should be zero (product is +0, +0+(-0)=+0)"
    );
}

/// fma(x, +0, 0.5) = 0.5 (symmetry: zero can be either multiplicand).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_finite_times_pos_zero() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (fp #b0 #b10000 #b0000000000)
                (_ +zero 5 11)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(2.0, +0, 0.5) should equal 0.5");
}

/// fma(-0, +0, +0) = +0 (both multiplicands zero, addend also +0).
/// product sign = sign(-0) XOR sign(+0) = 1 XOR 0 = 1 → product = -0.
/// Under RNE: (-0) + (+0) = +0.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_both_zero_multiplicands() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (_ -zero 5 11)
                (_ +zero 5 11)
                (_ +zero 5 11))
            (_ +zero 5 11))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(-0, +0, +0) RNE: product=-0, -0 + +0 = +0"
    );
}

/// fma(+0, -1.0, +0) under RTN = -0 (sign-of-sum special rule).
/// IEEE 754 § 6.3: `(+x) + (-x) = -0` only under RTN, `+0` under other modes.
/// Here product = -0, addend = +0, so sum is (-0) + (+0) = -0 under RTN.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_sign_rtn() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z
            (fp.fma RTN
                (_ +zero 5 11)
                (fp #b1 #b01111 #b0000000000)
                (_ +zero 5 11))))
        (assert (= z (_ -zero 5 11)))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "fma(+0, -1.0, +0) RTN: product=-0, -0 + +0 = -0"
    );
}

/// fma(+0, 2.0, 0.5) under RTZ = 0.5 (no rounding; 0 + 0.5 is exact).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_rtz_finite_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RTZ
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, 2.0, 0.5) RTZ should equal 0.5"
    );
}

/// fma(+0, 2.0, 0.5) under RTP = 0.5 (no rounding needed).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_rtp_finite_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RTP
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, 2.0, 0.5) RTP should equal 0.5"
    );
}

/// fma(+0, 2.0, 0.5) under RNA = 0.5 (ties away; 0+0.5 needs no rounding).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_rna_finite_addend() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNA
                (_ +zero 5 11)
                (fp #b0 #b10000 #b0000000000)
                (fp #b0 #b01110 #b0000000000))
            (fp #b0 #b01110 #b0000000000))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, 2.0, 0.5) RNA should equal 0.5"
    );
}

/// fma(+0, -inf, 0.5) = NaN (0 * -inf = NaN per IEEE-754).
/// Symmetric with test_fp_fma_zero_factor_zero_times_inf_is_nan but negative inf.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_zero_times_neg_inf_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ +zero 5 11)
                (_ -oo 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma(+0, -inf, 0.5) should be NaN (0 * -inf = NaN)"
    );
}

/// fma(-0, NaN, 0.5) = NaN (NaN propagates regardless of zero sign).
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_neg_zero_times_nan_is_nan() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN
            (fp.fma RNE
                (_ -zero 5 11)
                (_ NaN 5 11)
                (fp #b0 #b01110 #b0000000000)))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"], "fma(-0, NaN, 0.5) should be NaN");
}

/// Z3 #8185 reproducer core pattern: `fma(+0, finite, 0.5) = 0.5` exactly.
/// This is the simplification Z3 failed to apply in time, producing an invalid
/// model. The rewrite in `fma.rs::try_make_fma_zero_factor` catches this.
///
/// Note: the full #8185 benchmark uses an integer→real→fp chain; this test
/// exercises only the fma-zero rewrite, which is the specific Z3 fix target.
#[test]
#[timeout(60_000)]
fn test_fp_fma_zero_factor_z3_issue_8185_pattern() {
    let smt = r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 5 11))
        (declare-const z (_ FloatingPoint 5 11))
        (assert (= z (fp.fma RNE (_ +zero 5 11) x (fp #b0 #b01110 #b0000000000))))
        (assert (fp.isNormal z))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    // When x is finite, z = 0.5 (normal). When x is inf or NaN, z is NaN
    // (non-normal). The assertion fp.isNormal z is satisfiable via any finite
    // x; the rewriter must propagate z ≈ 0.5 for finite x.
    assert_eq!(
        outputs,
        vec!["sat"],
        "#8185 pattern: fma(+0, finite_x, 0.5) should be 0.5 (normal)"
    );
}

/// fp.fma single-rounding discrimination: fma(a, b, c) ≠ round(round(a*b) + c)
///
/// a = 1025/1024 = 1 + 2^(-10) = (fp #b0 #b01111 #b0000000001)
/// b = 1023/1024 = 1 - 2^(-10) = (fp #b0 #b01110 #b1111111110)
/// c = -(1023/1024)            = (fp #b1 #b01110 #b1111111110)
///
/// Exact a*b = 1 - 2^(-20) (21 sig bits; exceeds Float16's 11 sig bits)
/// round(a*b) = 1.0 (rounds up since trailing bits > 0.5 ULP)
///
/// Separate (double-round): round(1.0 + c) = round(1.0 - 1023/1024) = 2^(-10)
/// = (fp #b0 #b00101 #b0000000000)
///
/// Fused (single-round): exact a*b + c = (1 - 2^(-20)) - (1 - 2^(-10))
///   = 2^(-10) - 2^(-20) = 2^(-10) × (1 - 2^(-10))
///   = 1.111111111_0 × 2^(-11) = (fp #b0 #b00100 #b1111111110)
///
/// The fused result is smaller than the separate result by 2^(-20).
#[test]
#[timeout(120_000)]
fn test_fp_fma_single_rounding_discrimination() {
    // Verify fma gives the fused (single-round) result
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.eq
            (fp.fma RNE
                (fp #b0 #b01111 #b0000000001)
                (fp #b0 #b01110 #b1111111110)
                (fp #b1 #b01110 #b1111111110))
            (fp #b0 #b00100 #b1111111110))))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "fma should give single-round result (2^(-10) - 2^(-20)), not double-round (2^(-10))"
    );
}
