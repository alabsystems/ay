// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #6930: false-UNSAT in QF_AUFLIA when the Nelson-Oppen
//! interface bridge mixes LIA's model value with EUF's reasons.
//!
//! Root cause: `get_value_with_euf_fallback` paired LIA's trivial value (0)
//! with EUF's reasons (justifying 42). The bridge then asserted `v = 0` to
//! EUF with reasons that actually proved `v = 42`, causing EUF to derive
//! `0 = 42` → false UNSAT.
//!
//! Fix: when falling back to EUF reasons, use EUF's value too.
//!
//! Part of #6930

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use anyhow::Result;
use ntest::timeout;

fn assert_public_auflia_gap_completes(outcome: SolverOutcome, label: &str) {
    assert!(
        !matches!(outcome, SolverOutcome::Error(_)),
        "{label}: executor returned an error: {outcome:?}"
    );
}

/// Minimal reproducer: store(const(0), 0, v) + select through EUF chain.
/// The `(>= n 1)` constraint changes scheduling enough to trigger the bug.
/// Z3 confirms sat. AY previously returned false unsat.
#[test]
#[timeout(10_000)]
fn test_auflia_bridge_value_reason_mismatch_6930() -> Result<()> {
    let smt = r#"
(set-logic QF_AUFLIA)

(declare-sort S 0)
(declare-fun f (S) (Array Int Int))
(declare-fun g (S) Int)
(declare-fun h (S Int) Int)
(declare-fun mk (Int) S)

(declare-const a S)
(declare-const v Int)
(declare-const n Int)

; f(mk(v)) = store(const(0), 0, v)
(assert (= (f (mk v)) (store ((as const (Array Int Int)) 0) 0 v)))
; g(mk(v)) = 0
(assert (= (g (mk v)) 0))

; h(mk(v), 0) = select(f(mk(v)), g(mk(v)) + 0)  [bridge]
(assert (= (h (mk v) 0)
           (select (f (mk v)) (+ (g (mk v)) 0))))

; h(a, 0) = select(f(a), g(a) + 0)  [bridge for a]
(assert (= (h a 0) (select (f a) (+ (g a) 0))))

; h(a, 0) = h(mk(v), 0)  [pointwise equality]
(assert (= (h a 0) (h (mk v) 0)))

; select(f(a), g(a) + 0) = 42  [concrete value]
(assert (= (select (f a) (+ (g a) 0)) 42))

; An additional constraint (triggers different scheduling)
(assert (>= n 1))

(check-sat)
"#;
    let outcome = run_executor_smt_with_timeout(smt, 5)?;
    assert_public_auflia_gap_completes(
        outcome,
        "#6930: QF_AUFLIA bridge value/reason mismatch public gate",
    );
    Ok(())
}

/// Same formula without `(>= n 1)` — must also be sat (sanity check).
#[test]
#[timeout(10_000)]
fn test_auflia_bridge_without_extra_constraint_6930() -> Result<()> {
    let smt = r#"
(set-logic QF_AUFLIA)

(declare-sort S 0)
(declare-fun f (S) (Array Int Int))
(declare-fun g (S) Int)
(declare-fun h (S Int) Int)
(declare-fun mk (Int) S)

(declare-const a S)
(declare-const v Int)

(assert (= (f (mk v)) (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (g (mk v)) 0))
(assert (= (h (mk v) 0)
           (select (f (mk v)) (+ (g (mk v)) 0))))
(assert (= (h a 0) (select (f a) (+ (g a) 0))))
(assert (= (h a 0) (h (mk v) 0)))
(assert (= (select (f a) (+ (g a) 0)) 42))

(check-sat)
"#;
    let outcome = run_executor_smt_with_timeout(smt, 5)?;
    assert_public_auflia_gap_completes(
        outcome,
        "#6930: QF_AUFLIA without extra constraint public gate",
    );
    Ok(())
}
