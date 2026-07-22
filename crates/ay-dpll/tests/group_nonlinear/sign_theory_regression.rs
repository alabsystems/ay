// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression suite for ay's Rat/Int **sign theory** — the valid sign
//! deductions the trust toolchain relies on.
//!
//! Each case below was cross-checked against z3 4.16. The decided cases use
//! strict `unsat` assertions so a regression (e.g. a wrong-SAT) fails loudly;
//! the single known-incomplete case (symbolic-divisor division sign) follows
//! the file-level strictness policy and accepts `unknown` alongside the correct
//! answer, with a `// NIA-INCOMPLETE:` rationale.
//!
//! Coverage: product sign (n-ary, integer and real), even-degree
//! non-negativity (squares), the neg×neg rule, constant-divisor `div`/`mod`
//! sign, and `abs` non-negativity.

use ntest::timeout;

/// Assert the formula is refuted (the sign deduction fires).
fn assert_unsat(smt: &str) {
    let out = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&out),
        Some("unsat"),
        "expected unsat from sign reasoning\nSMT2:\n{smt}\nOUTPUT:\n{out}"
    );
}

// ============================================================================
// Product sign — `product_sign` over factor signs (n-ary).
// ============================================================================

/// x>0 ∧ y>0 ∧ z>0 ⇒ x·y·z > 0 (ternary product sign).
#[test]
#[timeout(10_000)]
fn sign_product_ternary_positive() {
    assert_unsat(
        r#"
(set-logic QF_NIA)
(declare-const x Int)(declare-const y Int)(declare-const z Int)
(assert (> x 0))(assert (> y 0))(assert (> z 0))
(assert (< (* x y z) 0))
(check-sat)
"#,
    );
}

/// Four negative factors ⇒ product > 0 (even count of negatives).
#[test]
#[timeout(10_000)]
fn sign_product_four_negatives_positive() {
    assert_unsat(
        r#"
(set-logic QF_NIA)
(declare-const a Int)(declare-const b Int)(declare-const c Int)(declare-const d Int)
(assert (< a 0))(assert (< b 0))(assert (< c 0))(assert (< d 0))
(assert (< (* a b c d) 0))
(check-sat)
"#,
    );
}

/// x<0 ∧ y<0 ⇒ x·y > 0 (the neg×neg rule).
#[test]
#[timeout(10_000)]
fn sign_neg_times_neg_is_positive() {
    assert_unsat(
        r#"
(set-logic QF_NIA)
(declare-const x Int)(declare-const y Int)
(assert (< x 0))(assert (< y 0))
(assert (< (* x y) 0))
(check-sat)
"#,
    );
}

/// Real product sign: x>0 ∧ y<0 ⇒ x·y < 0.
#[test]
#[timeout(10_000)]
fn sign_product_real_mixed() {
    assert_unsat(
        r#"
(set-logic QF_NRA)
(declare-const x Real)(declare-const y Real)
(assert (> x 0.0))(assert (< y 0.0))
(assert (> (* x y) 0.0))
(check-sat)
"#,
    );
}

// ============================================================================
// Even-degree non-negativity — squares are ≥ 0.
// ============================================================================

/// x·x < 0 is unsatisfiable over the reals (even-degree non-negativity).
#[test]
#[timeout(10_000)]
fn sign_square_real_negative_unsat() {
    assert_unsat(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (< (* x x) 0.0))
(check-sat)
"#,
    );
}

// ============================================================================
// Constant-divisor `div`/`mod` sign (linear: solvable by LIA from the
// Euclidean bounds 0 ≤ mod < |k|, a = k·q + mod).
// ============================================================================

/// a>0 ⇒ div(a, 3) ≥ 0.
#[test]
#[timeout(10_000)]
fn sign_div_constant_divisor_nonnegative() {
    assert_unsat(
        r#"
(set-logic QF_NIA)
(declare-const a Int)
(assert (> a 0))
(assert (< (div a 3) 0))
(check-sat)
"#,
    );
}

/// mod(a, 5) ≥ 0 always (Euclidean remainder is non-negative).
#[test]
#[timeout(10_000)]
fn sign_mod_constant_divisor_nonnegative() {
    assert_unsat(
        r#"
(set-logic QF_NIA)
(declare-const a Int)
(assert (< (mod a 5) 0))
(check-sat)
"#,
    );
}

// ============================================================================
// `abs` non-negativity.
// ============================================================================

/// abs(x) ≥ 0 always.
#[test]
#[timeout(10_000)]
fn sign_abs_nonnegative() {
    assert_unsat(
        r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (< (abs x) 0))
(check-sat)
"#,
    );
}

// ============================================================================
// Symbolic-divisor division sign — KNOWN-INCOMPLETE.
// ============================================================================

/// a>0 ∧ b>0 ⇒ div(a, b) ≥ 0 with a SYMBOLIC divisor `b`.
///
/// NIA-INCOMPLETE: refuting this needs magnitude reasoning over the nonlinear
/// `a = b·q + r` (`b·q ≤ -b` when `q ≤ -1, b ≥ 1`), beyond pure sign reasoning.
/// ay soundly returns `unknown`; the symbolic mod/div elimination keeps the
/// full Euclidean constraint (never relaxes it to a sign-only over-approximation
/// that would risk a wrong-SAT). If NIA gains the magnitude step this should
/// tighten to `unsat`.
#[test]
#[timeout(10_000)]
fn sign_div_symbolic_divisor_known_incomplete() {
    let out = crate::common::solve(
        r#"
(set-logic QF_NIA)
(declare-const a Int)(declare-const b Int)
(assert (> a 0))(assert (> b 0))
(assert (< (div a b) 0))
(check-sat)
"#,
    );
    let r = crate::common::sat_result(&out);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "symbolic-divisor div sign must be unsat or (soundly) unknown, never sat; got {r:?}\n{out}"
    );
}
