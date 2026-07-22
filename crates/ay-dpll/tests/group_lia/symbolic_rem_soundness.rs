// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression for symbolic/zero-divisor integer `rem`
//! (#nia-symbolic-rem-bypass).
//!
//! A non-constant-divisor `(rem x y)` is not soundly solvable on every theory
//! path: the NIA tentative-model patch treated it as a FREE integer and waved
//! through a model violating its defining bound — a wrong-SAT (e.g.
//! `y>0 ∧ (rem x y) >= y` returned `sat`). It is now degraded to a sound
//! `unknown` universally before any solver runs. These cases must therefore be
//! `unsat` or `unknown` — NEVER `sat` — under every logic. Constant-divisor
//! `rem` is folded by `mk_rem` and stays fully solvable (covered elsewhere).

use ntest::timeout;

/// Assert the formula is NOT satisfiable-claimed: a sound solver returns `unsat`
/// (the true answer for these bound-violations) or `unknown`, never `sat`.
fn assert_not_sat(smt: &str) {
    let out = crate::common::solve(smt);
    let r = crate::common::sat_result(&out);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "symbolic rem must be unsat or (soundly) unknown, never sat; got {r:?}\nSMT2:\n{smt}\nOUT:\n{out}"
    );
}

macro_rules! rem_bound_case {
    ($name:ident, $logic:literal, $constraint:literal) => {
        #[test]
        #[timeout(20_000)]
        fn $name() {
            assert_not_sat(&format!(
                "(set-logic {})\n(declare-const x Int)(declare-const y Int)\n\
                 (assert (> y 0))\n(assert {})\n(check-sat)\n",
                $logic, $constraint
            ));
        }
    };
}

// `y > 0 ⇒ 0 <= rem(x,y) < y`; each violation must not be `sat`, across logics.
rem_bound_case!(rem_ge_y_nia, "QF_NIA", "(>= (rem x y) y)");
rem_bound_case!(rem_ge_y_lia, "QF_LIA", "(>= (rem x y) y)");
rem_bound_case!(rem_ge_y_all, "ALL", "(>= (rem x y) y)");
rem_bound_case!(rem_ge_y_ufnia, "QF_UFNIA", "(>= (rem x y) y)");
rem_bound_case!(rem_lt_0_nia, "QF_NIA", "(< (rem x y) 0)");
rem_bound_case!(rem_le_neg1_nia, "QF_NIA", "(<= (rem x y) (- 1))");
rem_bound_case!(rem_gt_y_nia, "QF_NIA", "(> (rem x y) y)");
rem_bound_case!(rem_le_y_from_below_nia, "QF_NIA", "(<= y (rem x y))");

/// A feasible symbolic-rem equality is also degraded to `unknown` (sound; we do
/// not solve symbolic `rem`), never a wrong verdict.
#[test]
#[timeout(20_000)]
fn rem_feasible_symbolic_is_unknown_not_wrong() {
    let out = crate::common::solve(
        "(set-logic QF_NIA)\n(declare-const x Int)(declare-const y Int)\n\
         (assert (= y 5))\n(assert (= (rem x y) 3))\n(check-sat)\n",
    );
    // True answer is sat; we soundly return unknown (or sat), never unsat.
    assert!(matches!(
        crate::common::sat_result(&out),
        Some("sat") | Some("unknown")
    ));
}

/// Constant-divisor `rem` stays fully solved (folded by `mk_rem`), unaffected by
/// the symbolic-rem degradation: the Z3 remainder sign semantics hold.
#[test]
#[timeout(20_000)]
fn rem_constant_divisor_still_solved() {
    // rem(-7, 3) = 2, rem(7, -3) = -1 (sign follows the divisor).
    let out = crate::common::solve(
        "(set-logic QF_NIA)\n(assert (not (and (= (rem (- 7) 3) 2) (= (rem 7 (- 3)) (- 1)))))\n(check-sat)\n",
    );
    assert_eq!(crate::common::sat_result(&out), Some("unsat"));
}

/// Z3 #9140 stays satisfiable-or-unknown (never unsat): `(rem x 0)` and
/// `(mod x 0)` are independent under-specified values.
#[test]
#[timeout(20_000)]
fn rem_zero_divisor_distinct_from_mod_not_unsat() {
    let out = crate::common::solve(
        "(set-logic QF_NIA)\n(declare-const x Int)\n(assert (distinct (rem x 0) (mod x 0)))\n(check-sat)\n",
    );
    assert!(matches!(
        crate::common::sat_result(&out),
        Some("sat") | Some("unknown")
    ));
}
