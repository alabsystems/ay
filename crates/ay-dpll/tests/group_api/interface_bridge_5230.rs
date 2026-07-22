// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for #5230: pairwise value equality discovery in InterfaceBridge.
//!
//! Before this fix, the bridge only propagated `arith_term = const_term`
//! equalities. If two interface terms evaluated to the same value but that
//! value had no matching constant in the formula, no equality was discovered.

use ntest::timeout;

/// QF_UFLIA: Two UF applications equal via arithmetic, no matching constant.
///
/// `f(x)` with `x=3` evaluates `f(3)`, and `g(y)` with `y=3` evaluates `g(3)`.
/// EUF knows `f(3) = g(3)` by congruence. But the *result* values also matter:
/// we need the bridge to discover that the *output* of `f` and `g` are equal.
///
/// Here `(+ a 1)` and `(+ b 2)` both evaluate to 4 when `a=3, b=2`, but 4
/// is never a constant in the formula. The pairwise bridge discovers
/// `(+ a 1) = (+ b 2)` and propagates it to EUF.
#[test]
#[timeout(10_000)]
fn uflia_pairwise_bridge_no_constant_unsat() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (= a 3))
(assert (= b 2))
(assert (= (f (+ a 1)) 10))
(assert (not (= (f (+ b 2)) 10)))
(check-sat)
"#;
    // a=3 → a+1=4, b=2 → b+2=4. So f(4) = 10 and not(f(4) = 10) → UNSAT.
    // The bridge must discover that (+ a 1) and (+ b 2) both evaluate to 4
    // (which is NOT a constant in the formula) so EUF can identify f(4) = f(4).
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "QF_UFLIA: f(a+1) and f(b+2) should be equal when a+1=b+2=4, \
         even though 4 is not a constant in the formula"
    );
}

/// QF_UFLIA: Soundness guard — pairwise bridge must NOT equate terms with
/// different evaluated values.
///
/// `a+1=4` and `b+2=7` are different, so the bridge must NOT produce a
/// spurious `(+ a 1) = (+ b 2)` equality. With inequality constraints on the
/// UF outputs, f(4) > 0 and f(7) < 0 are simultaneously satisfiable.
#[test]
#[timeout(10_000)]
fn uflia_pairwise_bridge_different_values_sat() {
    let smt = r#"
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (= a 3))
(assert (= b 5))
(assert (> (f (+ a 1)) 0))
(assert (< (f (+ b 2)) 0))
(check-sat)
"#;
    // a=3 → a+1=4, b=5 → b+2=7. Different argument values → no pairwise equality.
    // f(4)>0 and f(7)<0 are satisfiable since f(4) and f(7) are independent.
    // If the bridge incorrectly equated (+ a 1) and (+ b 2), EUF would merge
    // f(4) and f(7), making f(4)>0 ∧ f(4)<0 unsatisfiable.
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "QF_UFLIA: f(a+1) and f(b+2) must NOT be equated when a+1=4 != b+2=7"
    );
}

/// QF_AUFLIRA: Mixed theory pairwise bridge — Int-sorted terms without
/// matching constant.
///
/// Exercises the pairwise bridge in AUFLIRA (arrays + UF + LIA + LRA), ensuring
/// the Int path works in a mixed-theory configuration. `(+ p 3)` and `(+ q 1)`
/// both evaluate to 5 when `p=2, q=4`. The bridge discovers the equality and
/// EUF derives `g(5) = g(5)`, making the negation UNSAT.
#[test]
#[timeout(10_000)]
fn auflira_pairwise_bridge_int_no_constant_unsat() {
    let smt = r#"
(set-logic QF_AUFLIRA)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun g (Int) Int)
(assert (= p 2))
(assert (= q 4))
(assert (= (g (+ p 3)) 100))
(assert (not (= (g (+ q 1)) 100)))
(check-sat)
"#;
    // p+3=5, q+1=5. g(5)=100 and not(g(5)=100) → UNSAT.
    // 5 is not a constant in the formula.
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "QF_AUFLIRA: g(p+3) and g(q+1) should be equal when both args evaluate to 5"
    );
}
