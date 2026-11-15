// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the QF_UFNRA Real-lane model completion
//! (#ufnra-real-lane): a Real UF application occurring only inside a Bool
//! predicate — e.g. `(m b (g a a))` — is never registered as an arithmetic
//! variable, and EUF's model extraction fabricates Int/BV class lanes but
//! no Real lane. The extracted model therefore committed no value for
//! `(g a a)`, the independent model gate could not confirm, and trivially
//! satisfiable goals answered `unknown` (SMT-LIB 2025 QF_UFNRA CLEARSY
//! 0004/00003 among them). `UfNraSolver::extract_models` now merges the
//! authoritative arith values and completes the remaining Real terms
//! class-consistently (`EufSolver::extract_real_term_values`, seeded by
//! the merged values). The gate still re-checks every assertion, so the
//! completion can only turn `unknown` into a verified `sat`, never into a
//! wrong one — the unsat guards below pin that direction.

use crate::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute succeeds")
}

/// `(f a) != b ∧ a != c` shape: the disequality the relaxation violates
/// must split, and the surviving model must commit a value for `(f a)`.
#[test]
#[timeout(30000)]
fn uf_real_app_under_disequality_is_sat() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun f (Real) Real)
        (declare-const a Real)
        (declare-const b Real)
        (declare-const c Real)
        (assert (not (= (f a) b)))
        (assert (not (= a c)))
        (check-sat)
    "#);
    assert_eq!(outputs[0], "sat");
}

/// A Real UF application nested as the argument of a Bool UF predicate:
/// neither side ever sees `(g a a)` as an arithmetic variable.
#[test]
#[timeout(30000)]
fn uf_real_app_nested_in_predicate_is_sat() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun m (Real Real) Bool)
        (declare-fun g (Real Real) Real)
        (declare-const a Real)
        (declare-const b Real)
        (assert (m b (g a a)))
        (check-sat)
    "#);
    assert_eq!(outputs[0], "sat");
}

/// CLEARSY-shaped goal: set-theoretic operators encoded as Real UFs, with
/// the goal a disequality between two Real UF applications.
#[test]
#[timeout(30000)]
fn uf_real_encoded_set_goal_is_sat() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun dom (Real) Real)
        (declare-fun set_prod (Real Real) Real)
        (declare-const g_s7_7 Real)
        (declare-const g_s1_0 Real)
        (assert (not (= (dom g_s7_7) (set_prod g_s1_0 g_s1_0))))
        (check-sat)
    "#);
    assert_eq!(outputs[0], "sat");
}

/// The completed values must respect EUF disequalities: two unpinned
/// classes claimed disequal need distinct fabricated values.
#[test]
#[timeout(30000)]
fn uf_real_completed_values_respect_disequality() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun g (Real) Real)
        (declare-const a Real)
        (declare-const b Real)
        (assert (not (= (g a) (g b))))
        (check-sat)
        (get-value ((g a) (g b)))
    "#);
    assert_eq!(outputs[0], "sat");
    assert!(
        !outputs[1].contains("(error"),
        "completed values must be readable: {}",
        outputs[1]
    );
}

/// A class with an arith-committed member inherits that member's value:
/// `(g a)` must read 5.0, not a fabricated fresh real.
#[test]
#[timeout(30000)]
fn uf_real_completed_value_inherits_arith_class_value() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun m (Real) Bool)
        (declare-fun g (Real) Real)
        (declare-const a Real)
        (declare-const b Real)
        (assert (= b 5.0))
        (assert (= (g a) b))
        (assert (m (g a)))
        (assert (not (= (g a) 3.0)))
        (check-sat)
        (get-value ((g a)))
    "#);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "(((g a) 5.0))");
}

/// Guard: congruence still refutes. Completion must never manufacture a
/// `sat` here — equal arguments force equal applications.
#[test]
#[timeout(30000)]
fn uf_real_congruence_violation_stays_unsat() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun g (Real) Real)
        (declare-const a Real)
        (declare-const b Real)
        (assert (= a b))
        (assert (not (= (g a) (g b))))
        (check-sat)
    "#);
    assert_eq!(outputs[0], "unsat");
}

/// Guard: arithmetic contradictions on a Real UF application stay unsat;
/// the arith side remains authoritative for registered terms.
#[test]
#[timeout(30000)]
fn uf_real_arith_contradiction_stays_unsat() {
    let outputs = run(r#"
        (set-logic QF_UFNRA)
        (declare-fun g (Real) Real)
        (declare-const a Real)
        (assert (< (g a) 0.0))
        (assert (> (g a) 0.0))
        (check-sat)
    "#);
    assert_eq!(outputs[0], "unsat");
}
