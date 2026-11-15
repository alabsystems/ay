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

/// Mechanism pin for [`ufdt_enum_exists_witness_is_sat`].
///
/// Since the quantified fail-closed model gate landed (ce801b029), a `sat`
/// with a quantified assertion publishes only on the gate's own `confirmed`.
/// An existential confirms only on a CLEAN check, and the nullary
/// constructor `S` (a `Var` in the term store) was collected as a free leaf
/// whose datatype value has no pin term, so the check was never clean
/// (`existential witness under partial pins`) and the genuine `sat` failed
/// closed to `unknown`. A nullary constructor is interpreted, like a literal,
/// and needs no pin: the gate must now confirm this existential itself.
#[test]
#[timeout(30_000)]
fn ufdt_enum_exists_witness_is_confirmed_by_the_quantified_gate() {
    let src = "(set-logic UFDT)\n\
               (declare-datatype E ((R) (S)))\n\
               (assert (exists ((c E)) (= c S)))\n\
               (check-sat)\n\
               (get-info :all-statistics)\n";
    let (stdout, stderr) = run_ay(src);
    assert_eq!(
        verdict(&stdout),
        "sat",
        "stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout
            .lines()
            .any(|line| line.contains(":model-check-gate.quantified ")
                && line.contains("\"confirmed\"")),
        "the quantified model gate itself must confirm the witness.\nstdout:\n{stdout}"
    );
}

/// Negative controls for the constructor-leaf rule: treating a nullary
/// constructor as interpreted must never let the gate confirm an existential
/// that is false. Each of these is UNSAT (z3 agrees); `sat` is a soundness bug.
#[test]
#[timeout(60_000)]
fn ufdt_enum_false_existentials_must_not_be_sat() {
    for body in [
        "(assert (exists ((c E)) (and (= c R) (= c S))))",
        "(declare-const d E)\n(assert (not (= d S)))\n\
         (assert (exists ((c E)) (and (= c d) (= c S))))",
        "(declare-fun g (E) Bool)\n(assert (not (g S)))\n\
         (assert (exists ((c E)) (and (g c) (= c S))))",
    ] {
        let src =
            format!("(set-logic UFDT)\n(declare-datatype E ((R) (S)))\n{body}\n(check-sat)\n");
        let (stdout, stderr) = run_ay(&src);
        assert_ne!(
            verdict(&stdout),
            "sat",
            "Soundness regression: a false enum existential reported `sat`.\n\
             input:\n{src}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

/// Wrong-UNSAT guard: satisfiable enum existentials under a logic with
/// arithmetic. `UFDTLIA` routes through the N-O UFLIA combiner. There the
/// finite-enum Skolem coverage (`add_enum_skolem_coverage`, 70959bd33) spells
/// each nullary constructor as a 0-ary application `(S)`, while the frontend
/// binds the same constructor to a `Var`; the D0 datatype pass's ground
/// structural-disequality rule (`ay-dt` `egraph_pass`, c95b28139) judged the
/// two spellings different ground values and emitted a fabricated
/// `ground-diseq` lemma, so AY answered `unsat` (z3: `sat`) in the default
/// posture. Every case below answered `unsat` before the fix. `unsat` is a
/// soundness bug; `sat` or `unknown` are acceptable.
#[test]
#[timeout(60_000)]
fn ufdtlia_enum_satisfiable_existentials_must_not_be_unsat() {
    for (decls, body) in [
        (
            "(declare-datatype E ((R) (S)))",
            "(assert (exists ((c E)) (= c S)))",
        ),
        (
            "(declare-datatype E ((R) (S) (T)))",
            "(assert (exists ((c E)) (= c T)))",
        ),
        (
            "(declare-datatype E ((R) (S)))\n(declare-const k Int)",
            "(assert (exists ((c E)) (= c R)))",
        ),
        (
            "(declare-datatype E ((R) (S) (T)))\n\
             (declare-datatype L ((nil) (cons (hd Int) (tl L))))",
            "(assert (exists ((c E) (e E)) (and (distinct c e) (distinct c R) (distinct e R))))",
        ),
    ] {
        let src = format!("(set-logic UFDTLIA)\n{decls}\n{body}\n(check-sat)\n");
        let (stdout, stderr) = run_ay(&src);
        assert_ne!(
            verdict(&stdout),
            "unsat",
            "Soundness regression: a satisfiable enum existential reported `unsat`.\n\
             input:\n{src}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}
