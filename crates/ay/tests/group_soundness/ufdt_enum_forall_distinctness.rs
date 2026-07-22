// UFDT enum-datatype universal-quantifier soundness regression.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// AY returned `sat` (a wrong answer) on
//
//   (set-logic UFDT)
//   (declare-datatype E ((R) (S)))
//   (assert (forall ((c E)) (= c R)))
//   (check-sat)
//
// which is UNSAT: `E` is a two-element enum `{R, S}` with `R != S` by
// constructor distinctness (AY proves `(= R S)` UNSAT under UFDT at the ground
// level), so `c = S` is a witness that violates `(forall (c E) (= c R))`. The
// universal is therefore FALSE and asserting it is UNSAT.
//
// Root cause (two interacting parts):
//   1. `declare-datatype E ((R) (S))` surfaces `E` as `Sort::Uninterpreted("E")`,
//      and both `c` and the nullary constructor `R` elaborate to `TermData::Var`.
//      So the universal body `(= c R)` matched `same_sort_variable_equality`, and
//      `quantifier_supported_by_uf_completion` declared the `forall` a benign
//      UF-completion definition — the result-mapping gate then force-returned
//      `sat`. UF completion is sound for a genuinely uninterpreted sort (which may
//      be a singleton), but NOT for a datatype enum whose universe is forced
//      non-singleton by constructor distinctness.
//   2. The MBQI-unsafe binder gate matches `Sort::Datatype(_)`, but a declared
//      datatype is `Sort::Uninterpreted`, so the gate never fired for the enum;
//      stripping the `forall` and accepting the ground SAT was unsound.
//
// Fix: (1) `quantifier_supported_by_uf_completion` returns false when any binder
// ranges over a datatype with >= 2 constructors (`mbqi.rs`); (2)
// `process_quantifiers` flags a `forall` over a multi-constructor datatype as
// MBQI-unsafe (`quantifier_loop/mod.rs`) so the soundness gate degrades the
// ground SAT to `unknown`.
//
// Correctness policy: incomplete paths must prefer
// `unknown` over an unchecked sat/unsat") the correct answer is `unsat`, the
// acceptable interim answer is `unknown`, and `sat` is a soundness bug that must
// never land. This file pins the soundness contract (never `sat`) AND guards
// against over-demotion: a genuinely satisfiable enum existential must still be
// `sat`.

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

/// The bug reproducer: `forall c:E. c = R` over `E = {R, S}` is UNSAT (witness
/// `c = S`). AY must never report `sat` (it previously did). `unsat` or
/// `unknown` are both acceptable.
#[test]
#[timeout(30_000)]
fn ufdt_enum_forall_false_universal_must_not_be_sat() {
    let src = "(set-logic UFDT)\n\
               (declare-datatype E ((R) (S)))\n\
               (assert (forall ((c E)) (= c R)))\n\
               (check-sat)\n";
    let (stdout, stderr) = run_ay(src);
    let result = verdict(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression: AY reported 'sat' on the false universal \
         `(forall (c E) (= c R))` over enum `E = {{R, S}}`, which is UNSAT by \
         constructor distinctness (`c = S` is a witness). Correct is 'unsat', \
         acceptable interim is 'unknown', never 'sat'. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Same shape with a single-constructor field datatype: `forall p:P. (f p) = 0`
/// is FALSE (some `p` can have a nonzero field), so asserting it is UNSAT. AY
/// must never report `sat`.
#[test]
#[timeout(30_000)]
fn ufdt_struct_forall_false_field_universal_must_not_be_sat() {
    let src = "(set-logic UFDT)\n\
               (declare-datatype P ((mk (f Int))))\n\
               (assert (forall ((p P)) (= (f p) 0)))\n\
               (declare-const q P)\n\
               (assert (= (f q) 7))\n\
               (check-sat)\n";
    let (stdout, stderr) = run_ay(src);
    let result = verdict(&stdout);
    assert_ne!(
        result, "sat",
        "Soundness regression: AY reported 'sat' on `(forall (p P) (= (f p) 0))` \
         together with `(f q) = 7`, which is UNSAT (`q` violates the universal). \
         Correct is 'unsat', acceptable interim is 'unknown', never 'sat'. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Over-demotion guard: an enum *existential* `exists c:E. c = S` is genuinely
/// SATISFIABLE (Skolemized to a fresh constant equal to `S`). The forall-side
/// soundness fix must not perturb this decidable existential.
#[test]
#[timeout(30_000)]
fn ufdt_enum_exists_witness_is_sat() {
    let src = "(set-logic UFDT)\n\
               (declare-datatype E ((R) (S)))\n\
               (assert (exists ((c E)) (= c S)))\n\
               (check-sat)\n";
    let (stdout, stderr) = run_ay(src);
    let result = verdict(&stdout);
    assert_eq!(
        result, "sat",
        "Over-demotion regression: AY failed to report 'sat' on the genuinely \
         satisfiable enum existential `(exists (c E) (= c S))`. got {result:?}. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
