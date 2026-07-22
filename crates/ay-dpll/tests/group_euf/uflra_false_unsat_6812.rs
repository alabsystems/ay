// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #6812: false-UNSAT on QF_UFLRA benchmark.
//!
//! The benchmark `cpachecker-induction.modulus_true-unreach-call.i.smt2` has
//! `:status sat` but ay previously returned UNSAT. Root cause: expression
//! split clauses (from N-O disequality enforcement) add hard constraints
//! derived from model evaluations, not from the formula itself. When the SAT
//! solver derives UNSAT from these added clauses, the result is unsound.
//!
//! Fix: escalate UNSAT to Unknown when the split loop has added expression
//! split clauses. The result should be `sat` or `unknown`, never `unsat`.
//!
//! Part of #6812

use crate::common::{
    run_executor_file_with_timeout, run_executor_smt_with_timeout, workspace_path, SolverOutcome,
};
use anyhow::Result;
use ntest::timeout;

/// Minimal inline QF_UFLRA test with uninterpreted functions + arithmetic.
/// The formula is satisfiable: f is uninterpreted, so f(x) can be anything.
/// The expression split mechanism should not cause a false UNSAT.
#[test]
#[timeout(10_000)]
fn test_uflra_uf_arith_interaction_not_false_unsat_6812() -> Result<()> {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (> x 0.0))
(assert (< y 10.0))
(assert (not (= (f x) (f y))))
(assert (= (+ x 1.0) y))
(check-sat)
"#;
    let outcome = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        matches!(outcome, SolverOutcome::Sat | SolverOutcome::Unknown),
        "#6812: UF+LRA interaction expected sat/unknown, got {outcome:?}"
    );
    Ok(())
}

/// Verify that genuine UNSAT in QF_UFLRA still works (no over-escalation).
/// f(x) = f(y) is forced by x = y (congruence), contradicting f(x) != f(y).
#[test]
#[timeout(10_000)]
fn test_uflra_genuine_unsat_still_works_6812() -> Result<()> {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let outcome = run_executor_smt_with_timeout(smt, 5)?;
    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "#6812: genuine congruence UNSAT must stay unsat"
    );
    Ok(())
}

/// QF_UFLRA with multiple UF applications and arithmetic constraints.
/// Satisfiable because f and g are uninterpreted.
#[test]
#[timeout(10_000)]
fn test_uflra_multi_uf_not_false_unsat_6812() -> Result<()> {
    let smt = r#"
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(declare-const a Real)
(declare-const b Real)
(assert (= (+ a b) 5.0))
(assert (> a 0.0))
(assert (> b 0.0))
(assert (not (= (f a) (g b))))
(assert (= (f a) 3.0))
(assert (= (g b) 7.0))
(check-sat)
"#;
    let outcome = run_executor_smt_with_timeout(smt, 5)?;
    assert!(
        matches!(outcome, SolverOutcome::Sat | SolverOutcome::Unknown),
        "#6812: multi-UF QF_UFLRA expected sat/unknown, got {outcome:?}"
    );
    Ok(())
}

/// Reproduce the exact cpachecker benchmark from #6812.
/// The soundness fix may conservatively return `unknown`, but it must never
/// regress to the original false `unsat`.
#[test]
#[timeout(10_000)]
fn test_uflra_cpachecker_benchmark_not_false_unsat_6812() -> Result<()> {
    let benchmark = workspace_path(
        "benchmarks/smt/QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.modulus_true-unreach-call.i.smt2",
    );
    let outcome = run_executor_file_with_timeout(&benchmark, 5)?;
    assert!(
        matches!(outcome, SolverOutcome::Sat | SolverOutcome::Unknown),
        "#6812: exact cpachecker benchmark expected sat/unknown, got {outcome:?}"
    );
    Ok(())
}
