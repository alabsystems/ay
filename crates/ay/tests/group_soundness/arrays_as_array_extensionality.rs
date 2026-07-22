// as-array <-> as-array equality extensionality false-SAT regression.
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates
//
// AY used to return `sat` on the pure-extensionality reproducer
//
//   (set-logic ALL)
//   (declare-fun f (Int) Int)
//   (declare-fun h (Int) Int)
//   (assert (= (_ as-array f) (_ as-array h)))
//   (assert (= (f 3) 10))
//   (assert (= (h 3) 20))
//   (check-sat)
//
// Z3 proves this UNSAT: equating the two arrays forces, by array
// extensionality, f(i) = h(i) for all i; in particular f(3) = h(3).
// The asserted f(3) = 10 and h(3) = 20 then give 10 = 20, a
// contradiction. No lambda is involved — this is pure array
// extensionality over `as-array` terms.
//
// Root cause (model validation, not solving): the `as-array[f]` term
// is a function-backed array that never normalizes to a (default,
// stores) form. `evaluate_array_equality`
// (crates/ay-dpll/src/executor/model/eval_array.rs) therefore could
// not decide the equality via `compare_array_models_normalized` nor
// `format_array_term_value`, and fell back to the SAT model's free
// truth value for the equality literal (assigned `true`) — circular
// self-validation. The array solver also never connects the two
// backing functions because the eager `select(as-array f, i) -> f(i)`
// rewrite removes any `select` term, leaving `check_array_equality`
// (which scans `parent_selects`) with nothing to fire on.
//
// Fix (fail-closed): `evaluate_array_equality` now detects a
// function-backed array operand and, instead of trusting the circular
// SAT value, probes the backing functions at concrete index points
// that already appear as applications. A provable disagreement returns
// `Bool(false)`; otherwise it returns `Unknown`, which the model
// validation pipeline degrades to `unknown`. SAT can no longer escape.
//
// These tests guard the fix: any `sat` result here is an SMT
// soundness bug. `unsat` (complete) or `unknown` (sound completeness
// limit) are both acceptable.

use ntest::timeout;
use std::io::Write;
use std::process::Command;

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

fn run_ay(smt2_src: &str) -> String {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("as_array_ext_case.smt2");
    let mut f = std::fs::File::create(&path).expect("create tmp smt2");
    f.write_all(smt2_src.as_bytes()).expect("write tmp smt2");
    drop(f);

    let mut cmd = Command::new(ay_bin());
    cmd.arg("-t:15000");
    cmd.arg(&path);

    let output = cmd.output().expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// The exact filed reproducer: two `as-array` terms equated with
/// conflicting reads. Z3 proves `unsat`; AY must never answer `sat`.
#[test]
#[timeout(30_000)]
fn as_array_eq_as_array_conflicting_reads_is_not_sat() {
    let result = run_ay(
        "(set-logic ALL)\
         (declare-fun f (Int) Int)\
         (declare-fun h (Int) Int)\
         (assert (= (_ as-array f) (_ as-array h)))\
         (assert (= (f 3) 10))\
         (assert (= (h 3) 20))\
         (check-sat)",
    );
    assert_ne!(
        result, "sat",
        "Soundness regression: AY reported 'sat' on a pure array-extensionality \
         instance that Z3 proves UNSAT ((= (_ as-array f) (_ as-array h)) with \
         f(3)=10, h(3)=20). Expected 'unsat' or 'unknown'. Got: {result:?}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output: {result:?}"
    );
}

/// Same contradiction routed through a shared array variable `b`:
/// `(= (_ as-array f) b)` and `(= (_ as-array h) b)`. Transitivity
/// equates the two as-array terms, so this is also UNSAT.
#[test]
#[timeout(30_000)]
fn as_array_eq_through_shared_var_is_not_sat() {
    let result = run_ay(
        "(set-logic ALL)\
         (declare-fun f (Int) Int)\
         (declare-fun h (Int) Int)\
         (declare-fun b () (Array Int Int))\
         (assert (= (_ as-array f) b))\
         (assert (= (_ as-array h) b))\
         (assert (= (f 3) 10))\
         (assert (= (h 3) 20))\
         (check-sat)",
    );
    assert_ne!(
        result, "sat",
        "Soundness regression: AY reported 'sat' on a transitive as-array \
         extensionality instance that is UNSAT. Got: {result:?}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output: {result:?}"
    );
}

/// Guard against over-correction: two `as-array` terms equated with
/// CONSISTENT reads (f(3)=10, h(3)=10) are genuinely satisfiable. The
/// fix must NOT turn this into `unsat`. `sat` or `unknown` are both
/// acceptable (never `unsat`).
#[test]
#[timeout(30_000)]
fn as_array_eq_consistent_reads_is_not_unsat() {
    let result = run_ay(
        "(set-logic ALL)\
         (declare-fun f (Int) Int)\
         (declare-fun h (Int) Int)\
         (assert (= (_ as-array f) (_ as-array h)))\
         (assert (= (f 3) 10))\
         (assert (= (h 3) 10))\
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "Over-correction: AY reported 'unsat' on a satisfiable as-array \
         instance (f(3)=h(3)=10). Got: {result:?}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output: {result:?}"
    );
}
