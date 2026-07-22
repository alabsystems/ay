// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression: ground `str.is_digit` must never rubber-stamp a wrong model.
//!
//! Family of `false_sat_str_code_6263` (the `benchmarks/smt/regression/
//! soundness_qf_slia_fuzz/falsesat_isdigit_replace_fromcode.smt2` repro, found
//! by the multi-theory diff-fuzz). SMT-LIB `str.is_digit(s)` is true iff `s` is
//! exactly one ASCII digit '0'..'9'. When `s` ground-resolves to the empty
//! string, a multi-character string, or a single non-digit char, an asserted
//! `(str.is_digit s)` is DEFINITIVELY false — ground `str.is_digit` is decidable,
//! so a candidate model that keeps it must be rejected, never emitted as `sat`.
//!
//! Root cause (pre-fix): the independent model-check gate's definitive-false
//! `StringOracle` (`executor/model/validation/definitive_eval.rs`) covered
//! `str.in_re` / `str.contains` / `str.prefixof` / `str.suffixof` / `=` but NOT
//! `str.is_digit`, so inside a monolithic `(and (ite ...) (str.is_digit ...))`
//! the enclosing-`and` recursion found no definitively-false conjunct and the
//! evaluator returned `Unknown` — leaving the door open for the demotion path to
//! keep the wrong witness as `sat`. The fix adds the `str.is_digit` arm to the
//! oracle (using the SAME `ay_strings::eval::eval_str_is_digit` the model
//! evaluator uses), so the ground conjunct is authoritatively refuted.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use anyhow::Result;
use ntest::timeout;

/// Bare `(str.is_digit "ab")` — a 2-char string is not a single digit: UNSAT.
#[test]
#[timeout(10_000)]
fn test_isdigit_multichar_literal_unsat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.is_digit "ab"))
(check-sat)
"#;
    assert_eq!(
        run_executor_smt_with_timeout(smt, 5)?,
        SolverOutcome::Unsat,
        "str.is_digit of a 2-char literal is definitively false → UNSAT",
    );
    Ok(())
}

/// `str.is_digit` of the empty string produced by an invalid `str.from_code`
/// (a negative code point yields ""): UNSAT.
#[test]
#[timeout(10_000)]
fn test_isdigit_of_fromcode_invalid_is_empty_unsat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.is_digit (str.from_code (- 2))))
(check-sat)
"#;
    assert_eq!(
        run_executor_smt_with_timeout(smt, 5)?,
        SolverOutcome::Unsat,
        "str.from_code(-2) = \"\" and str.is_digit(\"\") is false → UNSAT",
    );
    Ok(())
}

/// The empty-needle `str.replace` prepends the replacement, giving a multi-char
/// string, so `str.is_digit` is false: UNSAT. Mirrors the nested-op shape of the
/// fuzz repro but with the replacement fully ground.
#[test]
#[timeout(10_000)]
fn test_isdigit_of_empty_needle_replace_unsat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(assert (str.is_digit (str.replace (str.++ " " "ab") "" "12")))
(check-sat)
"#;
    assert_eq!(
        run_executor_smt_with_timeout(smt, 5)?,
        SolverOutcome::Unsat,
        "str.replace(\" ab\", \"\", \"12\") = \"12 ab\" (multi-char) → str.is_digit false → UNSAT",
    );
    Ok(())
}

/// The monolithic-conjunction shape that hid the violation: an `ite` over a free
/// Bool `r` AND a ground-false `str.is_digit`. The oracle must recurse into the
/// `and` and refute the `str.is_digit` conjunct: UNSAT (was Unknown pre-fix).
#[test]
#[timeout(10_000)]
fn test_isdigit_inside_monolithic_and_unsat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun r () Bool)
(declare-fun s () String)
(declare-fun u () String)
(assert (and (ite (distinct s u) r r) (str.is_digit "ab")))
(check-sat)
"#;
    assert_eq!(
        run_executor_smt_with_timeout(smt, 5)?,
        SolverOutcome::Unsat,
        "the enclosing-and recursion must refute the ground str.is_digit conjunct → UNSAT",
    );
    Ok(())
}

/// The full fuzz repro (`:status unsat`). The `str.from_code`/`str.replace`
/// operands route through Int/String vars pinned by top-level equalities, which
/// the string oracle's evaluator does not yet resolve in the candidate model (a
/// known cross-theory model-completion gap), so AY currently answers `unknown`
/// here. This test pins the SOUNDNESS floor: it must NEVER be `sat`. (When the
/// model-completion gap is closed, tighten this to `Unsat`.)
#[test]
#[timeout(10_000)]
fn test_falsesat_isdigit_replace_fromcode_never_sat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun s () String)(declare-fun t () String)(declare-fun u () String)
(declare-fun w () String)(declare-fun m () Int)(declare-fun r () Bool)
(assert (= s " "))(assert (= t "9"))(assert (= w "a"))(assert (= m -2))
(assert (and (ite (str.< w (str.++ s "b" w)) (not (str.<= t "a")) (ite (distinct s u) r r))
             (str.is_digit (str.replace (str.++ " " "ab") (str.from_code m) (str.replace "12" t s)))))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert_ne!(
        result,
        SolverOutcome::Sat,
        "SOUNDNESS BUG: the fuzz repro is UNSAT (z3=unsat); AY must never answer sat here, got {result:?}",
    );
    Ok(())
}
