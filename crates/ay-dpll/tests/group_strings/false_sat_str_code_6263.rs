// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for false SAT on str-code-unsat-2.smt2.
//!
//! Introduced by commit 4c6abccc1 (W1:2119, Part of #6263): the model
//! validation trust-the-theory-solver bypass (mod.rs:4524-4555) allows the
//! executor to return SAT when string assertions evaluate to Unknown, even
//! when the model is actually invalid.
//!
//! The benchmark declares a length-1 string `x` and asserts that
//! `str.to_code(x)` is either < 0 or > 10^25. Since `str.to_code` of a
//! length-1 string returns a value in [0, 1114111], this is UNSAT.
//! Z3 correctly returns UNSAT. AY incorrectly returns SAT after the
//! model validation bypass was added.
//!
//! Root cause: The string theory solver's check() does not fully verify
//! str.to_code range constraints against LIA bounds. The model validation
//! layer was the safety net, and the #6263 bypass removed it.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use anyhow::Result;
use ntest::timeout;

/// str-code-unsat-2.smt2 from CVC5 regressions.
/// str.to_code of a length-1 string must be in [0, 1114111].
/// Asserting it's out of range makes the problem UNSAT.
#[test]
#[timeout(10_000)]
fn test_false_sat_str_to_code_range_unsat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 1))
(assert (or (< (str.to_code x) 0) (> (str.to_code x) 10000000000000000000000000000)))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        result == SolverOutcome::Unsat || result == SolverOutcome::Unknown,
        "SOUNDNESS BUG: str-code-unsat-2 must not be SAT, got {result:?}. \
         str.to_code of length-1 string is in [0, 1114111], \
         so the disjunction (< 0 or > 10^25) is unsatisfiable.",
    );
    Ok(())
}

/// Simpler variant: str.to_code(x) < 0 when len(x) = 1 is UNSAT.
#[test]
#[timeout(10_000)]
fn test_false_sat_str_to_code_negative_unsat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 1))
(assert (< (str.to_code x) 0))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        result == SolverOutcome::Unsat || result == SolverOutcome::Unknown,
        "SOUNDNESS BUG: str.to_code of length-1 string cannot be negative, got {result:?}",
    );
    Ok(())
}

/// str.to_code(x) > 1114111 when len(x) = 1 is UNSAT (Unicode max).
#[test]
#[timeout(10_000)]
fn test_false_sat_str_to_code_above_unicode_max_unsat() -> Result<()> {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 1))
(assert (> (str.to_code x) 1114111))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        result == SolverOutcome::Unsat || result == SolverOutcome::Unknown,
        "SOUNDNESS BUG: str.to_code of length-1 string cannot exceed 1114111, got {result:?}",
    );
    Ok(())
}
