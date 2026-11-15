// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! z3 reads every subterm of a command before it simplifies anything, so it
//! raises errors and binds `:named` labels in the untaken branch of an `ite`
//! with a constant condition, in an unused `let` value and in a `match` case
//! that cannot be taken. ay does not elaborate those subterms into its term
//! store, and now checks them where z3 reads them. Each script is one of the
//! z3-mode conformance review's repros: ay gave the opposite sat/unsat
//! answer from z3 4.12.5 and 4.16. The expected answers are z3's or
//! `unknown`, in `--z3-mode` (stdin and file) and in plain mode.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

fn run_stdin(input: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["-q", "--z3-mode", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay -in");
    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB input");
    child.wait_with_output().expect("wait for ay -in")
}

fn run_file(input: &str, args: &[&str]) -> std::process::Output {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("input.smt2");
    std::fs::write(&path, input).expect("write SMT-LIB file");
    Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg(&path)
        .current_dir(dir.path())
        .output()
        .expect("run ay on a file")
}

fn answers(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

/// Check the answers in z3 mode (stdin and file) and in plain mode.
fn assert_answers(input: &str, z3_mode: &[&str], plain: &[&str]) {
    for (mode, output, expected) in [
        ("z3 stdin", run_stdin(input), z3_mode),
        ("z3 file", run_file(input, &["-q", "--z3-mode"]), z3_mode),
        ("plain file", run_file(input, &["-q"]), plain),
    ] {
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            answers(&stdout),
            expected,
            "{mode}: {input}\nstdout: {stdout}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

/// z3 answers unsat on each (repros ite_skipped_error_extra_label,
/// ite_skipped_error_extra_label2, let_skipped_error_extra_label and
/// match_skipped_error_extra_label): it rejects the first assertion at the
/// error in the skipped subterm, before label `a`, so it accepts
/// `(! (not p) :named a)`. ay rejected the first assertion only at label
/// `c`, kept `a`, rejected `(! (not p) :named a)` and answered sat. An error
/// that is not a label's leaves z3's labels unknown (z3 may not raise it,
/// see `z3_mode_label_reach`), so the answer is withheld.
#[test]
#[timeout(120_000)]
fn an_error_in_a_skipped_subterm_before_a_label_rejection() {
    for skipped in [
        "(ite true true undefined_sym)",
        "(ite true true (not p q))",
        "(let ((l0 undefined_sym)) true)",
        "(match (mk 1) (((mk v) true) (nothing undefined_sym)))",
    ] {
        let input = format!(
            "(declare-datatypes ((P 0)) (((mk (fst Int)) (nothing))))\n\
             (declare-const p Bool)\n(declare-const q Bool)\n(declare-const c Bool)\n\
             (assert (and {skipped} (! p :named a) (! q :named c)))\n\
             (assert (! (not p) :named a))\n(assert p)\n(check-sat)\n"
        );
        assert_answers(&input, &["unknown"], &["unknown"]);
    }
}

/// z3 5.1.0 answers sat on each: `bvumul_noovfl` is a z3 builtin, so z3
/// accepts the first assertion and binds `a`, then rejects
/// `(! (not p) :named a)`. ay reads `bvumul_noovfl` as an undefined symbol,
/// rejected the first assertion before `a`, accepted the second and answered
/// unsat in both modes, in a skipped subterm (this change) and in a live one
/// (older). A rejection before a label for any reason but the label now
/// withholds every later answer.
#[test]
#[timeout(120_000)]
fn a_z3_builtin_ay_lacks_before_a_label() {
    for unsupported in [
        "(ite true true (bvumul_noovfl b b))",
        "(match (mk 1) (((mk v) true) (nothing (bvumul_noovfl b b))))",
        "(bvumul_noovfl b b)",
    ] {
        let input = format!(
            "(declare-datatypes ((P 0)) (((mk (fst Int)) (nothing))))\n\
             (declare-const p Bool)\n(declare-const b (_ BitVec 8))\n\
             (assert (and {unsupported} (! p :named a)))\n\
             (assert (! (not p) :named a))\n(assert p)\n(check-sat)\n"
        );
        assert_answers(&input, &["unknown"], &["unknown"]);
    }
}

/// z3 answers sat (repro ite_skipped_label_exact): it binds `b` in the
/// skipped branch, rejects the first assertion at `c` and the second at `b`.
/// ay never bound `b`, accepted the second assertion and answered unsat.
/// Plain mode withholds `sat` after an assertion it dropped.
#[test]
#[timeout(60_000)]
fn a_label_in_a_skipped_subterm_before_a_label_rejection() {
    assert_answers(
        "(declare-const p Bool)\n(declare-const c Bool)\n\
         (assert (or (ite true true (! false :named b)) (! p :named c)))\n\
         (assert (or (! p :named b) (not p)))\n(assert (not b))\n(assert p)\n(check-sat)\n",
        &["sat"],
        &["unknown"],
    );
}

/// z3 answers sat (repros ite_error_accepted_preexisting and
/// let_error_accepted_preexisting, and the same for a definition): it
/// rejects the first command at the error in the skipped subterm. ay kept it
/// and answered unsat. A dropped assertion withholds `sat`.
#[test]
#[timeout(60_000)]
fn an_error_in_a_skipped_subterm_of_an_accepted_command() {
    for command in [
        "(assert (ite true p undefined_sym))",
        "(assert (let ((l0 undefined_sym)) p))",
        "(define-fun f () Bool (ite false undefined_sym p))\n(assert f)",
    ] {
        let input = format!("(declare-const p Bool)\n{command}\n(assert (not p))\n(check-sat)\n");
        assert_answers(&input, &["unknown"], &["unknown"]);
    }
}

/// Well-sorted skipped subterms change nothing. The first script rejects an
/// assertion at label `c` after binding `a`, as z3 does; both answer unsat.
#[test]
#[timeout(60_000)]
fn a_well_sorted_skipped_subterm_keeps_the_answer() {
    assert_answers(
        "(declare-const p Bool)\n(declare-const q Bool)\n(declare-const c Bool)\n\
         (declare-const x Int)\n\
         (assert (and (! p :named a) (ite true true (> x 0)) (! q :named c)))\n\
         (assert (not a))\n(assert p)\n(check-sat)\n",
        &["unsat"],
        &["unsat"],
    );
    assert_answers(
        "(declare-const p Bool)\n(declare-const x Int)\n(declare-const b (_ BitVec 8))\n\
         (assert (ite true p (and (> x 0) (= (bvadd b #x01) #x00))))\n\
         (assert (let ((l0 (bvadd b #x01)) (l1 x)) (not p)))\n(check-sat)\n",
        &["unsat"],
        &["unsat"],
    );
}

/// A dead `let` value that names an earlier dead binding is well sorted:
/// Verus writes these, and they must stay accepted.
#[test]
#[timeout(60_000)]
fn a_dead_value_naming_an_earlier_dead_binding_is_accepted() {
    assert_answers(
        "(declare-const p Bool)\n(declare-const x Int)\n(declare-const b (_ BitVec 8))\n\
         (assert (let ((t x) (s b)) (let ((u (+ t 1)) (v (bvadd s #x01))) p)))\n\
         (assert (not p))\n(check-sat)\n",
        &["unsat"],
        &["unsat"],
    );
}

/// Outside z3 mode the session differs from z3's only in the label names z3
/// binds and it did not, so a later command that mentions one withholds the
/// answers after it, and any other state z3 is in that this session is not
/// withholds every later answer. Each script got the opposite answer from
/// z3 4.12.5 in plain mode, before and after labels became definitions.
#[test]
#[timeout(60_000)]
fn plain_mode_withholds_where_its_labels_differ_from_z3() {
    for (input, z3_mode, plain) in [
        // z3 binds `c`, then rejects the assertion at `undefined_b`, so it
        // rejects `(! (not p) :named c)`; z3 answers sat.
        (
            "(declare-const p Bool)\n(assert (and (! p :named c) undefined_b))\n\
             (assert (! (not p) :named c))\n(assert p)\n(check-sat)\n",
            &["unknown"][..],
            &["unknown"][..],
        ),
        // z3 rejects the first assertion at label `b`, a declared Int, even
        // though it labels a `let`-bound name; z3 answers sat.
        (
            "(declare-const b Int)\n(declare-const x Int)\n(declare-const p Bool)\n\
             (assert (let ((z x)) (and p (= (! z :named b) 0))))\n(assert (not p))\n(check-sat)\n",
            &["sat"],
            &["unknown"],
        ),
        // z3 binds `a` over the `let`-bound name and rejects the definition
        // of `a`; z3 answers unsat.
        (
            "(declare-const x Int)\n(assert (let ((z x)) (! (> z 0) :named a)))\n\
             (define-fun a () Bool false)\n(assert (not a))\n(assert (> x 0))\n(check-sat)\n",
            &["unknown"],
            &["unknown"],
        ),
        // The label left unbound is never mentioned again: z3's answers.
        (
            "(declare-const x Int)\n(declare-const q Bool)\n\
             (assert (let ((z x)) (! (> z 0) :named a)))\n(assert (not q))\n(check-sat)\n\
             (assert (< x 0))\n(check-sat)\n",
            &["unknown", "unknown"],
            &["sat", "unsat"],
        ),
        // A mention written against a `;` comment is a mention; z3 answers
        // unsat. The token scan read `a;` as one symbol and answered sat.
        (
            "(declare-const x Int)\n(assert (let ((z x)) (! (> z 0) :named a)))\n\
             (declare-const a;\n Int)\n(assert (= a;\n 7))\n(check-sat)\n",
            &["unknown"],
            &["unknown"],
        ),
    ] {
        assert_answers(input, z3_mode, plain);
    }
}
