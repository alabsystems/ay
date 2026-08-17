// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! WRONG SAT: `(default <dependent-lambda>)` escapes the model gate.
//!
//! AY answers `sat` for a formula that is contradictory REGARDLESS of what
//! `default` means:
//!
//! ```smt2
//! (define-fun a () (Array Int Int) (lambda ((x Int)) (+ x 1)))
//! (assert (= (default a) 0))
//! (assert (distinct (default a) 0))
//! ```
//!
//! `(= t 0)` and `(distinct t 0)` cannot both hold for any `t`. z3 4.15.4 says
//! `unsat`. No semantics for `default` needs adjudicating — this is a
//! reflexivity failure, and the sharper form below makes that explicit:
//! `(not (= (default a) (default a)))` is also answered `sat`.
//!
//! ISOLATED, by controlled variant. Only the dependent-lambda case is wrong:
//!
//! | array                                  | AY      | z3      |
//! |----------------------------------------|---------|---------|
//! | `(declare-fun b () (Array Int Int))`   | `unsat` | `unsat` |
//! | `((as const (Array Int Int)) 7)`       | `unsat` | `unsat` |
//! | `(lambda ((x Int)) (+ x 1))`           | **sat** | `unsat` |
//!
//! and `(not (= a a))` / `(not (= (select a 3) (select a 3)))` over the SAME
//! lambda are both correctly `unsat`, so the lambda itself hash-conses fine.
//!
//! WHY THE GATE DID NOT CATCH IT. `--stats` reports
//! `:model_check_gate.result "confirmed-sat"` and `--g3-gate-dump` reports
//! `n_false=0 n_uneval=0` — the gate evaluated ZERO assertions, and the
//! published model is literally `(model )`.
//!
//! `independent_gate_query_roots` (executor/model/independent_gate.rs:55) reads
//! `self_check_authored_assertions` IF SET, and otherwise falls back to
//! `ctx.assertions` — the PREPROCESSED set. In default mode an assertion
//! eliminated by preprocessing therefore never reaches the gate, and the gate
//! confirms a model it never checked against the authored problem. The gate's
//! own verdict function is sound (empty roots and unevaluable both yield
//! `CannotConfirm`); it is being handed the wrong roots.
//!
//! That is the general hole, and it is larger than this test: ANY unsound
//! elimination is invisible to the gate in default mode. Closing it means
//! always gating on the AUTHORED assertions, which is an architectural change
//! with a real completeness cost and needs its own measured campaign.
//!
//! KNOWN-RED. Do not weaken these to one-sided assertions — a one-sided pin is
//! exactly how a wrong `unsat` hid elsewhere in this suite for a whole session.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

fn verdict(smt: &str) -> SolverOutcome {
    run_executor_smt_with_timeout(smt, 30).expect("execution should succeed")
}

#[test]
#[timeout(30_000)]
fn default_of_dependent_lambda_contradiction_is_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(define-fun a () (Array Int Int) (lambda ((x Int)) (+ x 1)))
(assert (= (default a) 0))
(assert (distinct (default a) 0))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "(= t 0) and (distinct t 0) are contradictory for ANY t, whatever \
         `default` denotes; z3 answers unsat"
    );
}

#[test]
#[timeout(30_000)]
fn default_of_dependent_lambda_is_equal_to_itself() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(define-fun a () (Array Int Int) (lambda ((x Int)) (+ x 1)))
(assert (not (= (default a) (default a))))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "a term must equal itself — this is reflexivity, not a theory question"
    );
}

/// CONTROL: the same shape over a DECLARED array is already correct, so the
/// defect is specific to the dependent-lambda operand and this test must keep
/// passing.
#[test]
#[timeout(30_000)]
fn default_of_declared_array_contradiction_is_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic ALL)
(declare-fun b () (Array Int Int))
(assert (= (default b) 0))
(assert (distinct (default b) 0))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "control: declared-array default already refutes correctly"
    );
}
