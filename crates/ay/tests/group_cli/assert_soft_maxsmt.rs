// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI integration tests for the Z3 `(assert-soft ...)` MaxSMT extension.
//!
//! Drives the `ay` binary on small weighted MaxSMT scripts via stdin and
//! verifies the parse+solve path: `check-sat` reports `sat` with a
//! weight-optimal model when the hard constraints are satisfiable, `unsat` only
//! when the HARD constraints are unsatisfiable, and `(get-objectives)` reports
//! the minimized total violated weight.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Run the `ay` binary in Z3 SMT-LIB stdin mode and return stdout.
fn run_ay(script: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut child = Command::new(ay_path)
        .arg("--z3-mode")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(script.as_bytes())
        .expect("write stdin");
    let output = child.wait_with_output().expect("wait ay");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// Extract the `__ay_soft_cost` value from `(get-objectives)` output.
fn soft_cost(stdout: &str) -> Option<u64> {
    let tag = "(__ay_soft_cost ";
    let start = stdout.find(tag)? + tag.len();
    let rest = &stdout[start..];
    let end = rest.find(')')?;
    // A `:approximate` qualifier may follow the value (resource-limited /
    // weight-incomplete results); take the leading numeric token.
    rest[..end].split_whitespace().next()?.parse::<u64>().ok()
}

#[test]
#[timeout(30_000)]
fn assert_soft_parses_and_solves_min_violated() {
    // Hard (or a b); soft (not a):1, (not b):1 => exactly one violated, cost 1.
    let out = run_ay(
        "(declare-const a Bool)\n\
         (declare-const b Bool)\n\
         (assert (or a b))\n\
         (assert-soft (not a) :weight 1)\n\
         (assert-soft (not b) :weight 1)\n\
         (check-sat)\n\
         (get-value (a b))\n\
         (get-objectives)\n",
    );
    let first = out.lines().next().unwrap_or("");
    assert_eq!(first, "sat", "expected sat, full output:\n{out}");
    assert_eq!(soft_cost(&out), Some(1), "min violated weight 1:\n{out}");
    // Exactly one of a/b true.
    let a_true = out.contains("(a true)");
    let b_true = out.contains("(b true)");
    assert!(a_true ^ b_true, "exactly one of a/b true:\n{out}");
}

#[test]
#[timeout(30_000)]
fn assert_soft_respects_weights() {
    // a (w5) and b (w1) mutually exclusive: satisfy a, violate b => cost 1.
    let out = run_ay(
        "(declare-const a Bool)\n\
         (declare-const b Bool)\n\
         (assert (or a b))\n\
         (assert (not (and a b)))\n\
         (assert-soft a :weight 5)\n\
         (assert-soft b :weight 1)\n\
         (check-sat)\n\
         (get-value (a b))\n\
         (get-objectives)\n",
    );
    assert_eq!(out.lines().next().unwrap_or(""), "sat", "{out}");
    assert_eq!(soft_cost(&out), Some(1), "{out}");
    assert!(out.contains("(a true)"), "weight-5 soft satisfied:\n{out}");
    assert!(out.contains("(b false)"), "weight-1 soft violated:\n{out}");
}

#[test]
#[timeout(30_000)]
fn assert_soft_all_satisfiable_zero_cost() {
    let out = run_ay(
        "(declare-const a Bool)\n\
         (declare-const b Bool)\n\
         (assert (or a b))\n\
         (assert-soft a :weight 3)\n\
         (assert-soft b :weight 2)\n\
         (check-sat)\n\
         (get-objectives)\n",
    );
    assert_eq!(out.lines().next().unwrap_or(""), "sat", "{out}");
    assert_eq!(
        soft_cost(&out),
        Some(0),
        "all softs satisfiable => 0:\n{out}"
    );
}

#[test]
#[timeout(30_000)]
fn assert_soft_hard_unsat_is_unsat() {
    // The HARD constraints are unsatisfiable: result must be unsat regardless
    // of any soft constraint.
    let out = run_ay(
        "(declare-const a Bool)\n\
         (assert a)\n\
         (assert (not a))\n\
         (assert-soft a :weight 1)\n\
         (check-sat)\n",
    );
    assert_eq!(out.lines().next().unwrap_or(""), "unsat", "{out}");
}

#[test]
#[timeout(30_000)]
fn assert_soft_default_weight_one() {
    // No :weight attribute => default weight 1. The two softs conflict, so the
    // optimum violates exactly one (cost 1).
    let out = run_ay(
        "(declare-const a Bool)\n\
         (assert (or a (not a)))\n\
         (assert-soft a)\n\
         (assert-soft (not a))\n\
         (check-sat)\n\
         (get-objectives)\n",
    );
    assert_eq!(out.lines().next().unwrap_or(""), "sat", "{out}");
    assert_eq!(soft_cost(&out), Some(1), "{out}");
}

#[test]
#[timeout(30_000)]
fn soft_plus_objective_never_reports_a_nonoptimal_objective() {
    // `(assert-soft ...)` AND `(maximize)`/`(minimize)` in one check-sat used to
    // run MaxSMT (ignoring the objective) and then report the objective term
    // evaluated at the arbitrary MaxSMT model as if it were the optimum — a WRONG
    // optimum with an otherwise-correct `sat`. Here the true max of x is 10, but
    // the soft constraint `q` is unrelated, so AY printed `(objectives (x 0))`.
    // Deleting the soft line gives the correct `(x 10)`, proving the soft line
    // alone flips it.
    //
    // AY now fails closed on the unsupported combination rather than fabricate an
    // optimum (zero-invalid-outputs). The one thing it must NEVER do is emit a
    // non-optimal `(objectives ...)` value.
    let out = run_ay(
        "(declare-const x Int)\n\
         (declare-const q Bool)\n\
         (assert (>= x 0))\n\
         (assert (<= x 10))\n\
         (maximize x)\n\
         (assert-soft q :weight 1)\n\
         (check-sat)\n\
         (get-objectives)\n",
    );
    assert!(
        !out.contains("(x 0)"),
        "must not report the non-optimal objective x=0 (true max is 10): {out}"
    );
    assert!(
        out.contains("error"),
        "the unsupported soft+objective combination must fail closed with an error: {out}"
    );

    // Control: the SAME problem without the soft line optimizes correctly.
    let control = run_ay(
        "(declare-const x Int)\n\
         (assert (>= x 0))\n\
         (assert (<= x 10))\n\
         (maximize x)\n\
         (check-sat)\n\
         (get-objectives)\n",
    );
    assert!(
        control.contains("(x 10)"),
        "maximize alone must still find the true optimum x=10: {control}"
    );
}

#[test]
#[timeout(30_000)]
fn assert_soft_qf_bv() {
    // assert-soft on Bool terms over QF_BV: the two equalities are mutually
    // exclusive, so the optimum violates exactly one (cost 1).
    let out = run_ay(
        "(set-logic QF_BV)\n\
         (declare-const x (_ BitVec 8))\n\
         (assert-soft (= x (_ bv0 8)) :weight 1)\n\
         (assert-soft (= x (_ bv1 8)) :weight 1)\n\
         (check-sat)\n\
         (get-objectives)\n",
    );
    assert_eq!(out.lines().next().unwrap_or(""), "sat", "{out}");
    assert_eq!(soft_cost(&out), Some(1), "{out}");
}
