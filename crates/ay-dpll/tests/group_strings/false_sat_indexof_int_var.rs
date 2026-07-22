// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for false SAT on str.indexof / str.to_int over a
//! constrained String variable whose integer result flows through an
//! intermediate Int variable.
//!
//! Root cause: when an integer-returning string function (str.indexof,
//! str.to_int, str.to_code) has a String argument that is a *variable*
//! (e.g. `(= s "ab")`) and its result is bound to a fresh Int variable
//! `(= x (str.indexof s "b" 0))`, the string core int-reduction pass
//! (extf_pass_int.rs::check_extf_int_reductions) only raises a conflict
//! when the const side resolves to a concrete Int. A free `x` never does,
//! so the theory combination (EUF+LIA) treats str.indexof as an
//! uninterpreted Int and freely assigns x = -1. Model validation then
//! rubber-stamps the definitively-false equality via the string-branch
//! SAT-fallback (observation.rs).
//!
//! str.indexof("ab", "b", 0) = 1 (z3 / z3-noodler zstring::indexofu),
//! so x must equal 1; asserting (not (= x 1)) is UNSAT.
//!
//! Correct answers: Unsat (complete fix) or Unknown (fail-closed). SAT is
//! the soundness bug.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use anyhow::Result;
use ntest::timeout;

#[test]
#[timeout(10_000)]
fn test_false_sat_indexof_found_via_int_var() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun x () Int)
(assert (= s "ab"))
(assert (= x (str.indexof s "b" 0)))
(assert (not (= x 1)))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        result == SolverOutcome::Unsat || result == SolverOutcome::Unknown,
        "SOUNDNESS BUG: str.indexof(\"ab\",\"b\",0) = 1, so (not (= x 1)) is UNSAT, got {result:?}",
    );
    Ok(())
}

#[test]
#[timeout(10_000)]
fn test_false_sat_indexof_wrong_value_via_int_var() -> Result<()> {
    // x is forced to 1 by indexof but asserted = 0.
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun x () Int)
(assert (= s "ab"))
(assert (= x (str.indexof s "b" 0)))
(assert (= x 0))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        result == SolverOutcome::Unsat || result == SolverOutcome::Unknown,
        "SOUNDNESS BUG: str.indexof(\"ab\",\"b\",0) = 1, not 0, got {result:?}",
    );
    Ok(())
}

#[test]
#[timeout(10_000)]
fn test_false_sat_to_int_via_int_var() -> Result<()> {
    // str.to_int("12") = 12; asserting != 12 is UNSAT.
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun x () Int)
(assert (= s "12"))
(assert (= x (str.to_int s)))
(assert (not (= x 12)))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        result == SolverOutcome::Unsat || result == SolverOutcome::Unknown,
        "SOUNDNESS BUG: str.to_int(\"12\") = 12, so (not (= x 12)) is UNSAT, got {result:?}",
    );
    Ok(())
}

/// Guard against over-firing: a genuinely-SAT instance must stay SAT.
/// str.indexof("abb","b",0) = 1, asserting x = 1 is SAT.
#[test]
#[timeout(10_000)]
fn test_indexof_int_var_genuinely_sat_unaffected() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun x () Int)
(assert (= s "abb"))
(assert (= x (str.indexof s "b" 0)))
(assert (= x 1))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        result == SolverOutcome::Sat || result == SolverOutcome::Unknown,
        "REGRESSION: genuinely-SAT indexof must not become Unsat, got {result:?}",
    );
    Ok(())
}
