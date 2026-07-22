// QF_AUFLIA array-model soundness regression (#8745).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates
//
// AY used to return `sat` on QF_AUFLIA formulas of the shape
//
//   (assert (= (select a0 0) 10))
//   (assert (= a1 (store a0 0 (+ (select a0 0) 1))))
//   (assert (< (select a1 0) 10))
//
// Z3 proves this UNSAT (a1[0] = a0[0] + 1 = 11, which cannot be < 10).
// The root cause lived in the AUFLIA array-model reconstruction
// (#8743): `minimize_array_interpretation` emptied the explicit
// stores of a single-store interpretation and promoted the value to
// `interp.default`, but `lookup_array_model` gated the default behind
// `!has_arith_model` and therefore returned `Unknown`, so the outer
// model validator fell through to the LIA model and reported a
// spurious SAT.
//
// The fix in commit 5e4b646e1 (Part of #8743) honors
// `interp.default` when the minimized interpretation has no stores.
// This test is a behavioral guard: both the full reproducer from the
// #8745 ticket (arrays + activation literals + `check-sat-assuming`)
// and the minimal inline variant must report `unsat`. Any `sat`
// result here is an SMT soundness regression and must never land.
//
// Related: #8734 (BMC spurious Unsafe on array CHCs was blocked on
// this SMT soundness fix; with this fix, BMC's array downgrade can be
// revisited).

use ntest::timeout;
use std::io::Write;
use std::process::Command;

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

fn run_ay(smt2_src: &str, extra_args: &[&str]) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("auflia_8745_case.smt2");
    let mut f = std::fs::File::create(&path).expect("create tmp smt2");
    f.write_all(smt2_src.as_bytes()).expect("write tmp smt2");
    drop(f);

    let mut cmd = Command::new(ay_bin());
    cmd.arg("-t:15000");
    for arg in extra_args {
        cmd.arg(arg);
    }
    cmd.arg(&path);

    let output = cmd.output().expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr)
}

fn first_line(stdout: &str) -> String {
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8745 full reproducer from the ticket: arrays + activation literals +
/// `check-sat-assuming`. Z3 says `unsat`. AY must not say `sat`.
#[test]
#[timeout(30_000)]
fn auflia_8745_full_reproducer_is_unsat() {
    let src = "(set-logic QF_AUFLIA)\n\
               (declare-const a0 (Array Int Int))\n\
               (declare-const i0 Int)\n\
               (declare-const p0 Bool)\n\
               (assert (=> p0 (and (= (select a0 0) 10) (= i0 0))))\n\
               (declare-const a1 (Array Int Int))\n\
               (declare-const i1 Int)\n\
               (declare-const p1 Bool)\n\
               (assert (=> p1 (or (and (= (select a1 0) 10) (= i1 0))\n\
                                   (and (= a1 (store a0 i0 (+ (select a0 i0) 1)))\n\
                                        (= i1 (+ i0 1))\n\
                                        p0\n\
                                        (< i0 5)))))\n\
               (declare-const q Bool)\n\
               (assert (=> q (and p1 (< (select a1 0) 10))))\n\
               (check-sat-assuming (q))\n\
               (exit)\n";
    let (stdout, stderr) = run_ay(src, &[]);
    let result = first_line(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8745): AY reported 'sat' on a QF_AUFLIA instance \
         that Z3 proves UNSAT (activation-literal reproducer). stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        result, "unsat",
        "Expected `unsat` on the #8745 reproducer; got {result:?}. stdout:\n{stdout}"
    );
}

/// Minimal inline variant that exercises the same array-model lookup
/// path without activation literals or `check-sat-assuming`. This
/// shrinks the #8745 reproducer down to the root-cause pattern:
/// `a1 = store(a0, 0, a0[0] + 1)` forces `a1[0] = 11`, contradicting
/// `a1[0] < 10`.
#[test]
#[timeout(30_000)]
fn auflia_8745_minimal_store_with_select_in_value_is_unsat() {
    let src = "(set-logic QF_AUFLIA)\n\
               (declare-const a0 (Array Int Int))\n\
               (declare-const a1 (Array Int Int))\n\
               (assert (= (select a0 0) 10))\n\
               (assert (= a1 (store a0 0 (+ (select a0 0) 1))))\n\
               (assert (< (select a1 0) 10))\n\
               (check-sat)\n\
               (exit)\n";
    let (stdout, stderr) = run_ay(src, &[]);
    let result = first_line(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8745): AY reported 'sat' on the minimal \
         QF_AUFLIA `store(a, 0, a[0]+1)` reproducer (Z3 proves UNSAT). \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        result, "unsat",
        "Expected `unsat` on the minimal #8745 reproducer; got {result:?}. stdout:\n{stdout}"
    );
}

/// Guard the `check-sat-assuming` entry point directly for the
/// minimal pattern. The #8745 ticket was filed against the BMC call
/// site which uses `check-sat-assuming`; this test confirms that the
/// assumption path (which routes through
/// `solve_auf_lia_with_assumptions`) also returns `unsat`.
#[test]
#[timeout(30_000)]
fn auflia_8745_minimal_check_sat_assuming_is_unsat() {
    let src = "(set-logic QF_AUFLIA)\n\
               (declare-const a0 (Array Int Int))\n\
               (declare-const a1 (Array Int Int))\n\
               (declare-const q Bool)\n\
               (assert (= (select a0 0) 10))\n\
               (assert (= a1 (store a0 0 (+ (select a0 0) 1))))\n\
               (assert (=> q (< (select a1 0) 10)))\n\
               (check-sat-assuming (q))\n\
               (exit)\n";
    let (stdout, stderr) = run_ay(src, &[]);
    let result = first_line(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8745): AY reported 'sat' on the minimal \
         QF_AUFLIA reproducer via `check-sat-assuming` (Z3 proves UNSAT). \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        result, "unsat",
        "Expected `unsat` on the #8745 check-sat-assuming reproducer; got {result:?}. \
         stdout:\n{stdout}"
    );
}
