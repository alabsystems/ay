// AUFLIA quantified array-extensionality soundness regression.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// AY returned `sat` (a wrong answer) on the AUFLIA extensionality formula
//
//   (assert (forall ((i Int)) (= (select a i) (select b i))))
//   (assert (not (= a b)))
//
// which Z3 proves UNSAT by array extensionality: if `a` and `b` agree at every
// index they are equal, contradicting `a != b`. AY's emitted model even
// violated its own `forall` (a[1]=5, b[1]=6).
//
// Root cause: the MBQI SAT->Unknown soundness guard only fired when a *binder*
// had an Array/FP/Seq/RegLan sort (`is_mbqi_unsafe_binder_sort`). Here the
// binder `i` is `Int`, so a `forall` that merely *indexes* arrays escaped the
// guard; the ground solver actually returned UNSAT, but CEGQI's Unsat->Sat
// disambiguation then flipped it into a spurious SAT. Fixed by (1) flagging a
// `forall` that reads/writes an array at a bound index as MBQI-unsafe
// (`forall_indexes_array_at_binder` in `quantifier_loop/mod.rs`) and (2)
// blocking the CEGQI Unsat->Sat disambiguation for MBQI-unsafe quantifiers
// (`quantifier_loop/result_mapping.rs`), degrading to `unknown`.
//
// Correctness policy: incomplete paths must prefer
// `unknown` over an unchecked sat/unsat") the correct answer is `unsat`, the
// acceptable interim answer is `unknown`, and `sat` is a soundness bug that
// must never land. This file pins the soundness contract (never `sat`) AND
// guards against over-demotion: a genuinely satisfiable array-quantifier
// instance must still return `sat`.

use ntest::timeout;
use std::io::Write;
use std::process::Command;

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

fn run_ay(smt2_src: &str) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("case.smt2");
    let mut f = std::fs::File::create(&path).expect("create tmp smt2");
    f.write_all(smt2_src.as_bytes()).expect("write tmp smt2");
    drop(f);

    let output = Command::new(ay_bin())
        .arg("-t:15000")
        .arg(&path)
        .output()
        .expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr)
}

fn verdict(stdout: &str) -> String {
    stdout
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("")
        .to_string()
}

/// The bug reproducer: `forall i. a[i] = b[i]` with `a != b` is UNSAT by
/// extensionality. AY must never report `sat` (it previously did, with a model
/// that violated its own `forall`). `unsat` or `unknown` are both acceptable.
#[test]
#[timeout(30_000)]
fn auflia_extensionality_forall_must_not_be_sat() {
    let src = "(set-logic AUFLIA)\n\
               (declare-fun a () (Array Int Int))\n\
               (declare-fun b () (Array Int Int))\n\
               (assert (forall ((i Int)) (= (select a i) (select b i))))\n\
               (assert (not (= a b)))\n\
               (check-sat)\n";
    let (stdout, stderr) = run_ay(src);
    let result = verdict(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression: AY reported 'sat' on AUFLIA array extensionality \
         `(forall i. a[i]=b[i]) AND a!=b`, which Z3 proves UNSAT. Correct is \
         'unsat', acceptable interim is 'unknown', never 'sat'. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Over-demotion guard: an explicit witness `a[k] != b[k]` together with
/// `a != b` is genuinely SATISFIABLE (the quantifier-free disequality is
/// consistent), so the fix must NOT degrade this to `unknown`/`unsat`.
#[test]
#[timeout(30_000)]
fn auflia_explicit_witness_disequality_is_sat() {
    let src = "(set-logic AUFLIA)\n\
               (declare-fun a () (Array Int Int))\n\
               (declare-fun b () (Array Int Int))\n\
               (declare-fun k () Int)\n\
               (assert (not (= (select a k) (select b k))))\n\
               (assert (not (= a b)))\n\
               (check-sat)\n";
    let (stdout, stderr) = run_ay(src);
    let result = verdict(&stdout);
    assert_eq!(
        result, "sat",
        "Over-demotion regression: AY failed to report 'sat' on a genuinely \
         satisfiable quantifier-free array disequality `a[k]!=b[k] AND a!=b`; \
         the extensionality soundness fix must not demote decidable QF instances. \
         got {result:?}. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
