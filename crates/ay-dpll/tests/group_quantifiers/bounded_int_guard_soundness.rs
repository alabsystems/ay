// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Soundness regression tests for bounded-Int `forall` finite-domain expansion
//! (#nnf-trap / #guard-must-bind).
//!
//! CONTEXT. `extract_bounded_int_forall` used to collect guard atoms ONLY from
//! `Not(cmp)`-wrapped disjuncts. After NNF the guards of the canonical shape
//! `(=> (and (>= i lo) (< i hi)) body)` arrive as BARE comparisons — the negation
//! is pushed INTO the comparison — so it found ZERO guards and bounded-Int
//! expansion never fired at all. That branch was dead code.
//!
//! Teaching it to read the NNF form is what makes expansion actually work, but it
//! also makes a LATENT FALSE-UNSAT reachable, which is what these tests pin.
//!
//! THE HAZARD. `extract_bounds_from_atoms` contributes nothing for a guard whose
//! bound is not an evaluable constant. If such a guard is silently dropped while
//! OTHER guards still supply `lo`/`hi`, the range `[lo,hi]` is a SUPERSET of the
//! region the guard actually constrains, and
//!
//!     AND_{i in [lo,hi]} body(i)
//!
//! is then STRICTLY STRONGER than the quantifier — it demands `body` at points the
//! dropped guard exempts. A satisfiable problem is reported UNSAT.
//!
//! Measured, with the `#guard-must-bind` bail removed, `test_unevaluable_guard_...`
//! below returns **unsat** where z3 returns **sat**. That is a wrong verdict, and
//! it is the reason expansion must bail whenever a recognized guard binds nothing.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// A guard the expander cannot evaluate must make it BAIL, never expand over the
/// superset. Dropping `(< i n)` would demand `(P i)` for every `i` in `[0,4]`,
/// including the `i >= n` the guard exempts — reporting UNSAT on a SAT problem.
///
/// True answer is SAT (z3 agrees): `n = 2`, so `(P 3)` is exempt and free to be
/// false. `unknown` is an acceptable (sound, incomplete) outcome here; `unsat`
/// is a WRONG VERDICT and must never be produced.
#[test]
fn test_unevaluable_guard_must_not_expand_over_superset() {
    let smt = r#"
(set-logic AUFLIA)
(declare-fun P (Int) Bool)
(declare-const n Int)
(assert (= n 2))
(assert (forall ((i Int)) (=> (and (>= i 0) (< i 5) (< i n)) (P i))))
(assert (not (P 3)))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 30).expect("execution should succeed");
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "#guard-must-bind: a guard whose bound is not evaluable was DROPPED and the \
         quantifier expanded over a SUPERSET of its guarded region, demanding the body \
         at points the guard exempts. This formula is SAT (n=2, so (P 3) is exempt). \
         Got: {result:?}"
    );
}

/// The positive control: with EVERY guard bound evaluable, expansion is exact and
/// the same shape is genuinely refuted. Guards `[0,5)` with `(not (P 3))` and
/// `(P i)` demanded across the whole range really is UNSAT.
#[test]
fn test_fully_bounded_guard_expands_and_refutes() {
    let smt = r#"
(set-logic AUFLIA)
(declare-fun P (Int) Bool)
(assert (forall ((i Int)) (=> (and (>= i 0) (< i 5)) (P i))))
(assert (not (P 3)))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 30).expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "a fully literal-bounded guard must expand exactly and refute: {result:?}"
    );
}

/// And the exemption must be RESPECTED, not just bailed on: outside the guarded
/// range the body is vacuous, so `(not (P 7))` is consistent with the same axiom.
#[test]
fn test_fully_bounded_guard_exempts_outside_range() {
    let smt = r#"
(set-logic AUFLIA)
(declare-fun P (Int) Bool)
(assert (forall ((i Int)) (=> (and (>= i 0) (< i 5)) (P i))))
(assert (not (P 7)))
(check-sat)
"#;
    let result = run_executor_smt_with_timeout(smt, 30).expect("execution should succeed");
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "7 is outside the guard [0,5), so (not (P 7)) is satisfiable; a WRONG UNSAT here \
         means the expansion demanded the body outside its guarded range: {result:?}"
    );
}
