// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #dt-occurs-guard (with #dt-soft-conflict): a
//! bit-blast candidate model for a recursive datatype merged `d`,
//! `(f1 d)` and `(f2 d)` into one construction class (their blast
//! cells agreed). Under the class-uniform selector projection used at
//! validation, ANY class value carrying constructor `mk` then makes
//! every generated acyclicity (occurs-check) lemma evaluate true, so
//! construction could only fail closed to `unknown` on a goal z3
//! decides `sat` instantly. Two candidate-side relaxations fix the
//! construction; the validation gates are unchanged and authored
//! facts are never relaxed:
//!
//! * constructor evidence that is entirely candidate-soft (SAT
//!   readings on generated atoms, no authored-hard force/exclusion and
//!   no lane pin) may reset to a free choice instead of poisoning the
//!   class as conflicted (#dt-soft-conflict);
//! * a constructor whose field selector loops within the class (a
//!   selector application whose class equals its argument's class) is
//!   never chosen for that class: datatype acyclicity forbids it. A
//!   soft force of such a constructor drops to a free choice; an
//!   authored-hard force stays a genuine conflict (#dt-occurs-guard).

use crate::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute succeeds")
}

fn verdict(outputs: &[String]) -> &str {
    outputs
        .iter()
        .find_map(|line| match line.trim() {
            v @ ("sat" | "unsat" | "unknown") => Some(v),
            _ => None,
        })
        .unwrap_or("<none>")
}

/// The minimized Certora-family shape: a reified equality over a UF
/// application of a recursive BV-carrying datatype. z3: `sat`.
#[test]
#[timeout(30000)]
fn recursive_dt_bv_reified_equality_sat() {
    let outputs = run(r#"
        (set-logic QF_UFBVDT)
        (declare-datatypes ((D 0)) (((mk (f1 D) (f2 D) (v (_ BitVec 8))) (leaf (w (_ BitVec 8))))))
        (declare-fun g (D) (_ BitVec 8))
        (declare-const d D)
        (declare-const b (_ BitVec 8))
        (declare-const c Bool)
        (assert (= (= (g d) b) c))
        (check-sat)
    "#);
    assert_eq!(verdict(&outputs), "sat", "outputs: {outputs:?}");
}

/// The BV256 twin of the same shape. z3: `sat`.
#[test]
#[timeout(30000)]
fn recursive_dt_bv256_reified_equality_sat() {
    let outputs = run(r#"
        (set-logic QF_UFBVDT)
        (declare-datatypes ((D 0)) (((mk (f1 D) (f2 D) (v (_ BitVec 256))) (leaf (w (_ BitVec 256))))))
        (declare-fun g (D) (_ BitVec 256))
        (declare-const d D)
        (declare-const b (_ BitVec 256))
        (declare-const c Bool)
        (assert (= (= (g d) b) c))
        (check-sat)
    "#);
    assert_eq!(verdict(&outputs), "sat", "outputs: {outputs:?}");
}

/// An AUTHORED occurs-check violation is a genuine conflict and must
/// never be relaxed into a model: `d = (f1 d)` with `(is-mk d)` is
/// unsatisfiable by datatype acyclicity. z3: `unsat`.
#[test]
#[timeout(30000)]
fn authored_occurs_conflict_stays_fail_closed() {
    let outputs = run(r#"
        (set-logic QF_UFBVDT)
        (declare-datatypes ((D 0)) (((mk (f1 D) (f2 D) (v (_ BitVec 8))) (leaf (w (_ BitVec 8))))))
        (declare-const d D)
        (assert (= d (f1 d)))
        (assert ((_ is mk) d))
        (check-sat)
    "#);
    assert_eq!(verdict(&outputs), "unsat", "outputs: {outputs:?}");
}

/// Legitimate recursion is unaffected: an authored constructor value
/// with nested leaves projects its fields exactly. z3: `sat`,
/// `(v d) = #x02`, `(w (f2 d)) = #x01`.
#[test]
#[timeout(30000)]
fn authored_recursive_value_projects_fields() {
    let outputs = run(r#"
        (set-logic QF_UFBVDT)
        (declare-datatypes ((D 0)) (((mk (f1 D) (f2 D) (v (_ BitVec 8))) (leaf (w (_ BitVec 8))))))
        (declare-const d D)
        (assert (= d (mk (leaf #x00) (leaf #x01) #x02)))
        (check-sat)
        (get-value ((v d) (w (f2 d))))
    "#);
    assert_eq!(verdict(&outputs), "sat", "outputs: {outputs:?}");
    let joined = outputs.join("\n");
    assert!(
        joined.contains("((v d) #x02)") && joined.contains("((w (f2 d)) #x01)"),
        "outputs: {outputs:?}"
    );
}
