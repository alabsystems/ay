// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! z3 binds a `:named` label when it reads it and stops a command at its
//! first error, so a label's state in z3's session depends on z3 accepting
//! every subterm before it. Each script is a repro from the label-conformance
//! review of the skipped-subterm check: ay raised an error z3 4.12.5 does not
//! raise, or accepted a construct z3 rejects, before a label, and answered
//! the opposite of z3. The expected answers are z3's or `unknown`, in
//! `--z3-mode` (stdin and file) and in plain mode. Where z3 4.12.5 and z3 5
//! disagree (a Bool beside an Int), z3 mode rejects the construct, as z3
//! 4.12.5 does, and plain mode keeps it, as z3 5 does, but withholds the
//! answers after a label that follows it.

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
fn assert_answers(name: &str, input: &str, z3_mode: &str, plain: &str) {
    for (mode, output, expected) in [
        ("z3 stdin", run_stdin(input), z3_mode),
        ("z3 file", run_file(input, &["-q", "--z3-mode"]), z3_mode),
        ("plain file", run_file(input, &["-q"]), plain),
    ] {
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            answers(&stdout),
            [expected],
            "{name}, {mode}:\n{input}\nstdout: {stdout}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

/// Errors ay raises and z3 4.12.5 does not, before label `a`: z3 binds `a`
/// to `p`, rejects the later definition or label `a` and answers sat. ay
/// read its own error as z3's, left `a` free for the definition and answered
/// unsat. Any error that is not a label's now withholds the later answers.
#[test]
#[timeout(120_000)]
fn an_error_z3_does_not_raise_before_a_label() {
    let datatype = "(declare-datatypes ((P 0)) (((mk (fst Int)) (nothing))))\n";
    for (name, input) in [
        (
            "c1_skip_false_error_after_catchall",
            format!(
                "{datatype}(declare-const p Bool)\n(declare-const x Int)\n\
                 (assert (or (match nothing ((_ true) ((mk v) (> v)))) (! p :named a)))\n\
                 (define-fun a () Bool false)\n(assert a)\n(check-sat)\n"
            ),
        ),
        (
            "c1_skip_false_error_dead_let",
            "(declare-const p Bool)\n(declare-const r Real)\n(declare-const x Int)\n\
             (assert (or (let ((d (div r 2))) true) (! p :named a)))\n\
             (assert (! false :named a))\n(check-sat)\n"
                .to_string(),
        ),
        (
            "c1_skip_false_error_dead_match_case",
            format!(
                "{datatype}(declare-const p Bool)\n(declare-const b (_ BitVec 8))\n\
                 (assert (or (match (mk 1) (((mk v) true) (nothing (bvumul_noovfl b b)))) \
                 (! p :named a)))\n(define-fun a () Bool false)\n(assert a)\n(check-sat)\n"
            ),
        ),
        (
            "c1_skip_false_error_ite_then_label",
            "(declare-const p Bool)\n(declare-const x Int)\n\
             (assert (or (ite true true (> x)) (! p :named a)))\n\
             (assert (! false :named a))\n(check-sat)\n"
                .to_string(),
        ),
        (
            "c1_skip_false_error_strconcat1",
            "(declare-const p Bool)\n(declare-const s String)\n\
             (assert (or (ite false (= (str.++ s) s) true) (! p :named a)))\n\
             (assert (! false :named a))\n(check-sat)\n"
                .to_string(),
        ),
        (
            "c1_skip_unknown_builtin_definefun",
            "(declare-const p Bool)\n(declare-const b (_ BitVec 8))\n\
             (assert (or (ite true true (bvumul_noovfl b b)) (! p :named a)))\n\
             (define-fun a () Bool false)\n(assert a)\n(check-sat)\n"
                .to_string(),
        ),
        (
            "z3m_false_error_before_label_taken",
            "(declare-const p Bool)\n(declare-const b (_ BitVec 8))\n\
             (assert (or (bvumul_noovfl b b) (! p :named a)))\n\
             (define-fun a () Bool false)\n(assert a)\n(check-sat)\n"
                .to_string(),
        ),
        (
            "z3m_false_error_before_label_taken2",
            "(declare-const p Bool)\n(declare-const x Int)\n\
             (assert (or (> x) (! p :named a)))\n\
             (define-fun a () Bool false)\n(assert a)\n(check-sat)\n"
                .to_string(),
        ),
    ] {
        assert_answers(name, &input, "unknown", "unknown");
    }
}

/// Constructs every z3 rejects before label `a` (a quantifier with no bound
/// variable, a variable pattern): z3 never binds `a`, so `(assert a)` is an
/// error and z3 answers sat, and a later `(! p :named a)` binds `a`, so z3
/// answers unsat. ay bound `a` and answered the opposite. z3 mode now rejects
/// both constructs; both modes withhold the later answers.
#[test]
#[timeout(120_000)]
fn a_construct_every_z3_rejects_before_a_label() {
    for (name, input) in [
        (
            "c2_skip_label_after_empty_binders",
            "(declare-const p Bool)\n\
             (assert (or true (ite true true (and (exists () p) (! false :named a)))))\n\
             (assert a)\n(check-sat)\n",
        ),
        (
            "c2_skip_label_after_var_pattern",
            "(declare-const p Bool)\n\
             (assert (or true (ite true true (and (forall ((z Int)) (! p :pattern (z))) \
             (! false :named a)))))\n(assert a)\n(check-sat)\n",
        ),
        (
            "c2_wrong_sat_exact_after_empty_binders",
            "(declare-const p Bool)\n\
             (assert (or true (ite true true (and (exists () p) (! true :named a)))))\n\
             (assert (and (not p) (! p :named a)))\n(check-sat)\n",
        ),
        (
            "z3m_label_after_empty_binders_taken",
            "(declare-const p Bool)\n\
             (assert (or true (and (exists () p) (! false :named a))))\n(assert a)\n(check-sat)\n",
        ),
        (
            "z3m_wrong_sat_exact_taken",
            "(declare-const p Bool)\n\
             (assert (or true (and (exists () p) (! true :named a))))\n\
             (assert (and (not p) (! p :named a)))\n(check-sat)\n",
        ),
    ] {
        assert_answers(name, input, "unknown", "unknown");
    }
}

/// A Bool beside an Int before label `a`: z3 4.12.5 rejects the assertion,
/// z3 5 coerces and binds `a`, and they answer differently. Both modes
/// withhold the later answers.
#[test]
#[timeout(120_000)]
fn a_bool_beside_an_int_before_a_label() {
    assert_answers(
        "c2_skip_label_after_bool_int",
        "(declare-const p Bool)\n(declare-const x Int)\n\
         (assert (or true (ite false (and (distinct p 1) (! false :named a)) true)))\n\
         (assert a)\n(check-sat)\n",
        "unknown",
        "unknown",
    );
    assert_answers(
        "c2_wrong_sat_exact_after_bool_int",
        "(declare-const p Bool)\n(declare-const x Int)\n\
         (assert (or true (ite true true (and (distinct p 1) (! true :named a)))))\n\
         (assert (and (not p) (! p :named a)))\n(check-sat)\n",
        "unknown",
        "unknown",
    );
}

/// z3 mode rejects what z3 4.12.5 rejects, with no label involved: z3
/// rejects the assertion and answers sat. A rejected assertion withholds a
/// later sat. Plain mode keeps the assertion, whose answer is unsat.
#[test]
#[timeout(120_000)]
fn z3_mode_rejects_constructs_z3_rejects() {
    for (name, input, plain) in [
        (
            "z3m_divisible_accepted",
            "(declare-const p Bool)\n(declare-const x Int)\n(define-fun f ((y Int)) Int 0)\n\
             (define-fun g ((y Bool)) Bool true)\n\
             (declare-datatypes ((P 0)) (((mk (fst Int)) (nothing))))\n\
             (assert (and ((_ divisible 3) x) false))\n(check-sat)\n",
            "unsat",
        ),
        (
            "bool_beside_int",
            "(declare-const p Bool)\n(assert (and (= p 1) false))\n(check-sat)\n",
            "unsat",
        ),
        (
            "z3m_ubv_to_int_accepted",
            "(declare-const p Bool)\n(declare-const x Int)\n(define-fun f ((y Int)) Int 0)\n\
             (define-fun g ((y Bool)) Bool true)\n\
             (declare-datatypes ((P 0)) (((mk (fst Int)) (nothing))))\n\
             (assert (and (= (ubv_to_int #x01) 1) false))\n(check-sat)\n",
            "unsat",
        ),
        (
            "z3m_exists_empty_binders",
            "(declare-const p Bool)\n(assert (or false (and (exists () p) false)))\n(check-sat)\n",
            "unsat",
        ),
        (
            "z3m_pattern_bare_var",
            "(declare-const p Bool)\n\
             (assert (or false (and (forall ((z Int)) (! p :pattern (z))) false)))\n(check-sat)\n",
            "unsat",
        ),
    ] {
        assert_answers(name, input, "unknown", plain);
    }
}

/// z3 binds a label ay leaves unbound (a non-numeric sort, a builtin name,
/// an overload, a `let`-bound name), so a second label of that name in the
/// same assertion makes z3 reject the assertion, and z3 answers sat. ay
/// accepted the second label and the assertion and answered unsat in plain
/// mode (the review's plain_collision repros). It now rejects the assertion
/// as z3 does; the session lacks the first label, so the answer is withheld.
#[test]
#[timeout(120_000)]
fn a_label_left_unbound_collides_with_a_later_one() {
    for (name, input) in [
        (
            "plain_collision_array_sort",
            "(declare-const arr (Array Int Int))\n\
             (assert (and (= (! arr :named a) arr) (! false :named a)))\n(check-sat)\n",
        ),
        (
            "plain_collision_builtin_name",
            "(declare-const p Bool)\n(assert (and (! p :named and) (! false :named and)))\n\
             (check-sat)\n",
        ),
        (
            "plain_collision_overload",
            "(declare-const p Bool)\n(declare-const a Int)\n\
             (assert (and (! p :named a) (! false :named a)))\n(check-sat)\n",
        ),
        (
            "plain_collision_letbound_unbound",
            "(declare-const p Bool)\n(declare-const q Bool)\n\
             (assert (and (let ((y p)) (! y :named a)) (! q :named a) p))\n\
             (assert (not p))\n(check-sat)\n",
        ),
        (
            "plain_collision_skipped_letbound",
            "(declare-const p Bool)\n(declare-const q Bool)\n\
             (assert (and (ite true true (let ((y p)) (! y :named a))) (! false :named a)))\n\
             (check-sat)\n",
        ),
    ] {
        assert_answers(name, input, "unknown", "unknown");
    }
}

/// Outside z3 mode, a label z3 binds and this session does not withholds
/// the answers from the first command that mentions it. `a;x` is the symbol
/// `a` before a comment, so the definition below mentions `a` (the review's
/// plain_mention_guard_comment_bypass); z3 answers sat.
#[test]
#[timeout(60_000)]
fn a_mention_before_a_comment_is_a_mention() {
    assert_answers(
        "plain_mention_guard_comment_bypass",
        "(declare-const p Bool)\n(assert (let ((y p)) (! y :named a)))\n\
         (define-fun a;x\n () Bool false)\n(assert a;x\n)\n(check-sat)\n",
        "unknown",
        "unknown",
    );
}
