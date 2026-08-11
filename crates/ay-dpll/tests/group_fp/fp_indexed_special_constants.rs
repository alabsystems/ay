// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Indexed FP special constants `(_ NaN eb sb)`, `(_ ±zero eb sb)`,
//! `(_ ±oo eb sb)` lose the SAT side of every query they appear in.
//!
//! These are *the* SMT-LIB spellings for the FP special values, so this is not
//! an exotic corner: it is the first thing any FP benchmark writes.
//!
//! # What is actually broken
//!
//! The bit-blaster handles these values CORRECTLY. Measured at
//! `142e9fbcfb`, every refuting query decides:
//!
//! ```text
//! (assert (not (fp.isNaN (_ NaN 11 53))))   -> unsat   CORRECT
//! (assert (fp.isNaN      (_ +zero 11 53)))  -> unsat   CORRECT
//! (assert (fp.isZero     (_ +oo 11 53)))    -> unsat   CORRECT
//! ```
//!
//! while every satisfiable query with the same constants degrades:
//!
//! ```text
//! (assert (fp.isNaN      (_ NaN 11 53)))    -> unknown WRONG (sat)
//! (assert (fp.isZero     (_ +zero 11 53)))  -> unknown WRONG (sat)
//! (assert (fp.isInfinite (_ +oo 11 53)))    -> unknown WRONG (sat)
//! ```
//!
//! A solver that can REFUTE `not (fp.isNaN NaN)` demonstrably knows the value.
//! The `sat` is computed and then discarded.
//!
//! Writing the identical value with the bit-triple constructor decides `sat`
//! normally, which isolates the defect to the indexed spelling rather than to
//! the FP theory:
//!
//! ```text
//! (assert (fp.isNaN (fp #b0 #b11111111111 #b1000…0))) -> sat  CORRECT
//! ```
//!
//! # Where it is NOT
//!
//! Ruled out by measurement rather than by reading:
//!
//! - **Not the bit-blaster.** It refutes these constants correctly, and
//!   `decompose_fp_app` dispatches on `sym.name()`, matching `Symbol::Indexed`.
//! - **Not model validation.** `--stats` reports
//!   `model_validation.checked 1`, `model_validation.total 1`,
//!   `:model-validation-failures 0` — the model is built and fully certified,
//!   and only then is the verdict replaced by `unknown`.
//! - **Not `check_fp_support` / `UnknownReason::Unsupported`.** The reported
//!   reason is `incomplete`, and the SAT solver runs to completion
//!   (`solve: sat num_vars=127`).
//! - **Not the constant-fold in `solve_fp`.** Extending
//!   `to_fp_const::fold_to_fp_real_constants` to rewrite these constants into
//!   the (known-good) 1-arg BV-reinterpret `to_fp` form was implemented and
//!   measured: zero change on every query above. So the degradation happens
//!   OUTSIDE `solve_fp`, downstream of a `sat` the FP lane already returned.
//! - **Not this session's UNSAT-certification work.** A CLI built at
//!   `ba2e39c8e4` — before the publication-funnel changes — reproduces every
//!   `unknown` above identically. This defect is older.
//!
//! # Scope
//!
//! 38 of the 115 `ay-dpll --lib` failures are FP, and the ones inspected
//! (`fp_sqrt_negative_zero_is_zero_bug14`, the `fp_to_fp_real_*` family, the
//! `test_fp_bv_bridge` classification tests) all assert `sat` on a query
//! containing one of these constants.
//!
//! These tests are RED. They encode the defect executably so the fix is
//! demonstrable rather than asserted.

use ntest::timeout;

/// `fp.isNaN` of the NaN literal is satisfiable — trivially, it is `true`.
///
/// The companion refutation `(not (fp.isNaN (_ NaN 11 53)))` already returns
/// `unsat`, so the solver holds the value; only the `sat` is dropped.
#[test]
#[timeout(30_000)]
fn indexed_nan_literal_is_sat_not_unknown() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.isNaN (_ NaN 11 53)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "fp.isNaN(NaN) is true, so this is sat; AY refutes the negation as \
         unsat, which proves it knows the value"
    );
}

/// The negation is already decided. Pinned so a fix cannot regress it.
#[test]
#[timeout(30_000)]
fn indexed_nan_literal_negation_stays_unsat() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (not (fp.isNaN (_ NaN 11 53))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "NaN is a NaN, so denying it is unsatisfiable"
    );
}

/// `(_ +zero eb sb)` — same defect, different constant.
#[test]
#[timeout(30_000)]
fn indexed_pos_zero_literal_is_sat_not_unknown() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.isZero (_ +zero 11 53)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// `(_ -zero eb sb)` must be both zero and negative.
#[test]
#[timeout(30_000)]
fn indexed_neg_zero_literal_is_zero_and_negative() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.isZero (_ -zero 11 53)))
        (assert (fp.isNegative (_ -zero 11 53)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// `(_ +oo eb sb)` — infinity is infinite.
#[test]
#[timeout(30_000)]
fn indexed_pos_infinity_literal_is_sat_not_unknown() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.isInfinite (_ +oo 11 53)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// `(_ -oo eb sb)` — negative infinity is negative.
#[test]
#[timeout(30_000)]
fn indexed_neg_infinity_literal_is_negative() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.isNegative (_ -oo 11 53)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// An ordering over two indexed constants, so the defect is shown not to
/// depend on a classification predicate.
#[test]
#[timeout(30_000)]
fn indexed_constants_compare_and_decide_sat() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.lt (_ +zero 11 53) (_ +oo 11 53)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), vec!["sat"]);
}

/// The SAME value written as a bit-triple already decides `sat`.
///
/// This is the control: it isolates the defect to the indexed spelling. If this
/// test ever fails, the FP theory itself has regressed and the tests above are
/// no longer measuring what they claim.
#[test]
#[timeout(30_000)]
fn bit_triple_nan_is_sat_control() {
    let smt = r#"
        (set-logic QF_FP)
        (assert (fp.isNaN
            (fp #b0 #b11111111111
                #b1000000000000000000000000000000000000000000000000000)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "control: the bit-triple spelling of NaN decides sat today"
    );
}
