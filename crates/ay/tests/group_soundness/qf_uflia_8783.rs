// QF_UFLIA false-SAT soundness regression (#8783).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates
//
// AY used to return `sat` on the 5-line QF_UFLIA reproducer
//
//   (declare-fun f (Int) Int)
//   (declare-const x Int)
//   (assert (= (f x) (+ x 1)))
//   (assert (= (f x) x))
//   (check-sat)
//
// Z3 proves this UNSAT. EUF congruence gives `(f x) = (f x)`, so the
// two assertions combine to force `x = x + 1` which is obviously
// UNSAT. The #8783 auditor noted that replacing `(f x)` with a fresh
// constant `y` on the LIA side (so the reproducer becomes
// `y = x + 1 AND y = x`) made AY return UNSAT — pointing at broken
// EUF -> LIA shared-equality forwarding.
//
// Root cause (detect_algebraic_equalities in crates/ay-theories/lia/
// src/nelson_oppen.rs): the Gaussian elimination loop reduces shared
// equalities using accumulated var-to-var substitutions
// (`var_equalities`) and tight bounds (`tight_bound_values`). The
// loop explicitly handled `Case 1` (single variable left → tight
// bound) and `Case 2` (two variables with zero constant → var
// equality) but silently dropped the `0 = c` case (no variables left,
// non-zero constant). For this reproducer, EUF propagates
// `x = f(x)` first; then substituting into the second equation
// `f(x) = x + 1` reduces it to `0 = 1`, which is UNSAT — but the old
// code returned `Vec::new()` without flagging a conflict.
//
// Fix: added a `Case 0` guard in `detect_algebraic_equalities` that
// stores the accumulated `reasons` in `pending_shared_eq_conflict`.
// Two pickup points consume it: `propagate_equalities` (returns the
// conflict on the N-O round) and `check_inner` (returns
// `TheoryResult::Unsat` upfront when shared equalities are present).
//
// These tests guard the fix against regressions: any `sat` result on
// these QF_UFLIA instances is an SMT soundness bug.

use ntest::timeout;
use std::io::Write;
use std::process::Command;

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

fn run_ay(smt2_src: &str) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("qf_uflia_8783_case.smt2");
    let mut f = std::fs::File::create(&path).expect("create tmp smt2");
    f.write_all(smt2_src.as_bytes()).expect("write tmp smt2");
    drop(f);

    let mut cmd = Command::new(ay_bin());
    cmd.arg("-t:15000");
    cmd.arg(&path);

    let output = cmd.output().expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr)
}

fn first_line(stdout: &str) -> String {
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// The #8783 5-line reproducer exactly as filed in the ticket. Z3
/// proves `unsat`; AY used to return `sat` because the EUF -> LIA
/// shared-equality forwarding dropped the `0 = 1` contradiction after
/// Gaussian substitution of `x = f(x)` into `f(x) = x + 1`.
#[test]
#[timeout(30_000)]
fn qf_uflia_8783_minimal_reproducer_is_unsat() {
    let src = "(set-logic QF_UFLIA)\n\
               (declare-fun f (Int) Int)\n\
               (declare-const x Int)\n\
               (assert (= (f x) (+ x 1)))\n\
               (assert (= (f x) x))\n\
               (check-sat)\n\
               (exit)\n";
    let (stdout, stderr) = run_ay(src);
    let result = first_line(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8783): AY reported 'sat' on the QF_UFLIA \
         minimal reproducer `(f x) = x + 1 AND (f x) = x` (Z3 proves UNSAT). \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        result, "unsat",
        "Expected `unsat` on the #8783 reproducer; got {result:?}. \
         stdout:\n{stdout}"
    );
}

/// Variation: `(f x) = x + 2 AND (f x) = x`. Same Gaussian structure,
/// different non-zero constant after substitution (`0 = 2`). Guards
/// against a Case 0 handler that accidentally special-cases the
/// constant `1` instead of "non-zero".
#[test]
#[timeout(30_000)]
fn qf_uflia_8783_offset_2_variant_is_unsat() {
    let src = "(set-logic QF_UFLIA)\n\
               (declare-fun f (Int) Int)\n\
               (declare-const x Int)\n\
               (assert (= (f x) (+ x 2)))\n\
               (assert (= (f x) x))\n\
               (check-sat)\n\
               (exit)\n";
    let (stdout, stderr) = run_ay(src);
    let result = first_line(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8783 variant): AY reported 'sat' on \
         `(f x) = x + 2 AND (f x) = x` (Z3 proves UNSAT). \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        result, "unsat",
        "Expected `unsat` on the offset-2 variant; got {result:?}. \
         stdout:\n{stdout}"
    );
}

/// Variation: two-argument UF `g(x, x)` bound to two different LIA
/// terms. Exercises the same EUF -> LIA path with a different UF
/// arity; protects against a fix that only covers unary UFs.
#[test]
#[timeout(30_000)]
fn qf_uflia_8783_binary_uf_variant_is_unsat() {
    let src = "(set-logic QF_UFLIA)\n\
               (declare-fun g (Int Int) Int)\n\
               (declare-const x Int)\n\
               (assert (= (g x x) (+ x 1)))\n\
               (assert (= (g x x) x))\n\
               (check-sat)\n\
               (exit)\n";
    let (stdout, stderr) = run_ay(src);
    let result = first_line(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8783 binary-UF variant): AY reported 'sat' \
         on `(g x x) = x + 1 AND (g x x) = x` (Z3 proves UNSAT). \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        result, "unsat",
        "Expected `unsat` on the binary-UF variant; got {result:?}. \
         stdout:\n{stdout}"
    );
}

/// Sanity check: the auditor's `y` intermediate variant (fresh const
/// on the LIA side) was already UNSAT before the fix. This pins that
/// path so a future refactor cannot regress it while "fixing" the UF
/// case.
#[test]
#[timeout(30_000)]
fn qf_uflia_8783_fresh_const_intermediate_is_unsat() {
    let src = "(set-logic QF_LIA)\n\
               (declare-const x Int)\n\
               (declare-const y Int)\n\
               (assert (= y (+ x 1)))\n\
               (assert (= y x))\n\
               (check-sat)\n\
               (exit)\n";
    let (stdout, stderr) = run_ay(src);
    let result = first_line(&stdout);
    assert_eq!(
        result, "unsat",
        "Expected `unsat` on the `y` intermediate variant; got {result:?}. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
