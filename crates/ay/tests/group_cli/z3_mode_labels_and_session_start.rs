// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Under `--z3-mode`, three things decide which names a later command sees,
//! and each has to match z3 4.12.5 or verdicts differ: which commands start
//! the session (after which `:global-declarations` is fixed), what a
//! `:global-declarations` value means, and `:named` labels, which z3 binds as
//! nullary definitions. The expected answers are z3 4.12.5's, in stdin and
//! file mode.

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

fn run_file(input: &str) -> std::process::Output {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("input.smt2");
    std::fs::write(&path, input).expect("write SMT-LIB file");
    Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["-q", "--z3-mode"])
        .arg(&path)
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

/// Check the answers in both input modes; returns the stdin transcript.
fn assert_answers(input: &str, expected: &[&str]) -> String {
    let mut first = None;
    for (mode, output) in [("stdin", run_stdin(input)), ("file", run_file(input))] {
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        assert_eq!(
            answers(&stdout),
            expected,
            "{mode} input: {input}\nstdout: {stdout}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        first.get_or_insert(stdout);
    }
    first.unwrap_or_default()
}

/// With global declarations `five` survives the pop and the redefinition is
/// rejected (`unsat`); with scoped ones it is redefined as 7 (`sat`).
const FIVE_AFTER_POP: &str = "(set-option :global-declarations true)\n(push)\n\
     (define-fun five () Int 5)\n(pop)\n(define-fun five () Int 7)\n\
     (assert (not (= five 5)))\n(check-sat)\n";

const AFTER_START: &str =
    "error setting ':global-decls', option value cannot be modified after initialization";

/// Each of these starts z3's session, so the option that follows is refused.
/// They used to leave it settable, and the redefinition then answered
/// `unsat` where z3 answers `sat`.
#[test]
#[timeout(120_000)]
fn commands_that_start_the_session_fix_global_declarations() {
    for (command, own_answers) in [
        ("(display 1)", &[][..]),
        ("(get-info :all-statistics)", &[]),
        ("(get-info :rlimit)", &[]),
        ("(apply simplify)", &[]),
        ("(get-objectives)", &[]),
        ("(model-add f () Int 1)", &[]),
        ("(help)", &[]),
        ("(get-consequences () ())", &["sat"]),
        ("(declare-map m (Int) Int)", &[]),
        ("(get-interpolant true false)", &[]),
        ("(get-value ())", &[]),
        ("(help-tactic)", &[]),
        ("(push 1)\n(pop 1)", &[]),
        ("(check-sat-using smt)", &["sat"]),
        ("(dbg-size 1)", &[]),
    ] {
        let mut expected = own_answers.to_vec();
        expected.push("sat");
        let stdout = assert_answers(&format!("{command}\n{FIVE_AFTER_POP}"), &expected);
        assert!(stdout.contains(AFTER_START), "{command}: {stdout}");
    }
}

/// These start nothing, even malformed, so the option still applies.
#[test]
#[timeout(120_000)]
fn commands_that_start_nothing_leave_global_declarations_settable() {
    for command in [
        "(echo \"e\")",
        "(get-info :name)",
        "(help echo)",
        "(push 0)",
        "(get-info :version)",
        "(get-objectives 1)",
        "(model-add)",
        "(declare-map m)",
        "(display)",
        "(get-model)",
        "(set-info :status sat)",
        "(frobnicate 1)",
    ] {
        let stdout = assert_answers(&format!("{command}\n{FIVE_AFTER_POP}"), &["unsat"]);
        assert!(!stdout.contains(AFTER_START), "{command}: {stdout}");
    }
}

/// A command ay cannot parse, and whose effect on z3's session depends on
/// what z3 makes of it, leaves the start unknown: a later change of the
/// option is refused and no later verdict is trusted.
#[test]
#[timeout(60_000)]
fn an_unclassified_failed_command_withholds_verdicts_after_an_option_change() {
    assert_answers(
        &format!("(apply no-such-tactic)\n{FIVE_AFTER_POP}"),
        &["unknown"],
    );
    // Setting the value it already has changes nothing either way.
    assert_answers(
        "(apply no-such-tactic)\n(set-option :global-declarations false)\n\
         (declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        &["sat"],
    );
}

/// `|true|` is the symbol `true`. The transcript said `true` while the
/// frontend kept declarations scoped, answering `sat`.
#[test]
#[timeout(60_000)]
fn a_quoted_true_enables_global_declarations() {
    let input = FIVE_AFTER_POP.replacen(
        ":global-declarations true",
        ":global-declarations |true|",
        1,
    );
    let stdout = assert_answers(
        &format!("{input}(get-option :global-declarations)\n"),
        &["unsat"],
    );
    assert!(stdout.lines().any(|line| line.trim() == "true"), "{stdout}");
}

/// z3 refuses any other value and keeps the one in force. The frontend used
/// to store it as a non-Boolean, which meant scoped declarations.
#[test]
#[timeout(60_000)]
fn an_invalid_value_keeps_global_declarations() {
    for (value, message) in [
        ("foo", "invalid option value, true/false expected"),
        ("\"true\"", "option value is not a string"),
        ("1", "option value is not a numeral"),
        ("(true)", "invalid option value"),
    ] {
        let input = format!(
            "(set-option :global-declarations true)\n(set-option :global-declarations {value})\n\
             {FIVE_AFTER_POP}"
        );
        let stdout = assert_answers(&input, &["unsat"]);
        assert!(stdout.contains(message), "{value}: {stdout}");
    }
}

/// A label is a nullary definition: a second label of the same name is
/// rejected with the assertion it names. This answered `unsat`.
#[test]
#[timeout(60_000)]
fn a_label_cannot_be_reused_in_its_scope() {
    let stdout = assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
         (assert (! (< x 0) :named a))\n(check-sat)\n",
        &["sat"],
    );
    assert!(
        stdout.contains("named expression already defined"),
        "{stdout}"
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named |a|))\n\
         (assert (! (< x 0) :named a))\n(check-sat)\n",
        &["sat"],
    );
    // Within one assertion the second label is rejected with the assertion,
    // and z3 keeps the first.
    assert_answers(
        "(declare-const x Int)\n(assert (and (! (> x 0) :named a) (! (< x 0) :named a)))\n\
         (check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (! (> x 0) :named a) :named a))\n\
         (assert (< x 0))\n(check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (and (! (> x 0) :named a) (! (< x 0) :named a)))\n\
         (declare-const a Bool)\n(assert (not a))\n(assert (> x 0))\n(check-sat)\n",
        &["unsat"],
    );
}

/// A query ay cannot route fails inside the executor, which is then rebuilt
/// from the session's log. The labels kept by a rejected assertion have to
/// be rebuilt too, or `a` could be declared afresh.
#[test]
#[timeout(120_000)]
fn labels_kept_by_a_rejected_assertion_survive_a_rebuild() {
    let input = "(declare-const x Int)\n\
         (assert (and (! (> x 0) :named a) (! (< x 0) :named a)))\n\
         (push)\n(assert (forall ((q Int)) (> (bv2nat ((_ int2bv 8) q)) (^ q 2))))\n\
         (check-sat)\n(pop)\n\
         (declare-const a Bool)\n(assert (not a))\n(assert (> x 0))\n(check-sat)\n";
    for output in [run_stdin(input), run_file(input)] {
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        assert_eq!(answers(&stdout).last(), Some(&"unsat"), "stdout: {stdout}");
    }
}

/// A definition or declaration of a label's name is rejected, so the name
/// keeps meaning the labeled term.
#[test]
#[timeout(60_000)]
fn a_label_blocks_later_definitions_of_its_name() {
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
         (define-fun a () Bool false)\n(assert a)\n(check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
         (declare-const a Bool)\n(assert (not a))\n(check-sat)\n",
        &["unsat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
         (define-fun-rec a () Bool false)\n(assert a)\n(check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n(push)\n\
         (define-fun a () Bool false)\n(assert a)\n(check-sat)\n(pop)\n(check-sat)\n",
        &["sat", "sat"],
    );
}

/// A label may not take the name of a nullary definition or of a nullary
/// declaration of its sort; the assertion is rejected. This answered
/// `unsat`.
#[test]
#[timeout(60_000)]
fn a_label_cannot_reuse_a_defined_name() {
    for declaration in [
        "(declare-const a Bool)",
        "(define-fun a () Bool true)",
        "(define-fun-rec a () Bool true)",
    ] {
        assert_answers(
            &format!(
                "{declaration}\n(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
                 (assert (< x 0))\n(check-sat)\n"
            ),
            &["sat"],
        );
    }
}

/// A label is a term once its `!` has closed.
#[test]
#[timeout(60_000)]
fn a_label_names_its_term() {
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n(assert (not a))\n(check-sat)\n",
        &["unsat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (and (! (> x 0) :named a) (not a)))\n(check-sat)\n",
        &["unsat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a :named b))\n(assert (not b))\n\
         (check-sat)\n",
        &["unsat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (forall ((y Int)) (or (> y 0) (! (> x 0) :named a))))\n\
         (assert (not a))\n(check-sat)\n",
        &["unsat"],
    );
    assert_answers(
        "(declare-const x Int)\n(push)\n(assert (! (= x 1) :named a))\n(pop)\n(assert a)\n\
         (check-sat)\n",
        &["unknown"],
    );
}

/// z3 rejects a label whose term has free variables, or whose value is not a
/// symbol, with its assertion. These answered `unsat`.
#[test]
#[timeout(60_000)]
fn a_malformed_label_rejects_its_assertion() {
    let stdout = assert_answers(
        "(declare-const x Int)\n(assert (forall ((y Int)) (! (> y 0) :named a)))\n(check-sat)\n",
        &["sat"],
    );
    assert!(
        stdout.contains("expression contains free variables"),
        "{stdout}"
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named 1))\n(assert (< x 0))\n(check-sat)\n",
        &["sat"],
    );
}

/// Under global declarations a label outlives the pop of its level. This
/// answered `unsat`.
#[test]
#[timeout(60_000)]
fn a_global_label_survives_pop() {
    assert_answers(
        "(set-option :global-declarations true)\n(declare-const x Int)\n(assert (= x 1))\n\
         (push)\n(assert (! (= x 1) :named a))\n(pop)\n(assert (! (= x 3) :named a))\n\
         (check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(set-option :global-declarations true)\n(declare-const x Int)\n(push)\n\
         (assert (! (= x 1) :named a))\n(pop)\n(assert (not a))\n(assert (= x 1))\n(check-sat)\n",
        &["unsat"],
    );
}

/// `(reset-assertions)` keeps definitions, labels included, at level 0 and
/// at a retained level until that level is popped. These answered `unsat`.
#[test]
#[timeout(60_000)]
fn a_label_survives_reset_assertions() {
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n(reset-assertions)\n\
         (assert (! (< x 0) :named a))\n(assert (> x 0))\n(check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(declare-const x Int)\n(push)\n(assert (! (> x 0) :named a))\n(reset-assertions)\n\
         (assert (! (< x 0) :named a))\n(assert (> x 0))\n(check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(declare-const x Int)\n(assert (! (> x 0) :named a))\n(reset-assertions)\n\
         (assert (not a))\n(assert (> x 0))\n(check-sat)\n",
        &["unsat"],
    );
    // z3 removes the label when the retained level is popped; the executor
    // made it permanent, so the verdict is withheld.
    assert_answers(
        "(declare-const x Int)\n(push)\n(assert (! (> x 0) :named a))\n(reset-assertions)\n\
         (pop)\n(assert (! (< x 0) :named a))\n(assert (> x 0))\n(check-sat)\n",
        &["unknown"],
    );
}

/// A label z3 would bind but ay does not (an overload, a label outside an
/// assertion, one over a `let`-bound name) withholds later verdicts.
#[test]
#[timeout(60_000)]
fn an_unbound_label_withholds_later_verdicts() {
    for input in [
        "(declare-const a Int)\n(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
         (assert (< x 0))\n(check-sat)\n",
        "(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n\
         (get-value ((! (> x 0) :named a)))\n(assert (not a))\n(check-sat)\n",
        "(declare-const x Int)\n(assert (let ((z x)) (! (> z 0) :named a)))\n(assert (not a))\n\
         (check-sat)\n",
    ] {
        let output = run_stdin(input);
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let got = answers(&stdout);
        assert_eq!(
            got.last(),
            Some(&"unknown"),
            "input: {input}\nstdout: {stdout}"
        );
    }
}

/// Outside `--z3-mode` nothing answers for z3's session state, so labels
/// withhold only what a dropped assertion withholds. A label this frontend
/// cannot bind leaves its assertion's meaning intact, and a label outside an
/// assertion changes nothing (a strict certificate for such a
/// `check-sat-assuming` literal is pinned in `group_soundness`). A label z3
/// rejects drops its assertion like any other refused assertion: a later
/// `sat` is withheld and a later `unsat` still stands.
#[test]
#[timeout(60_000)]
fn outside_z3_mode_labels_withhold_only_what_a_dropped_assertion_does() {
    for (input, expected) in [
        (
            "(declare-const x Int)\n(assert (let ((z x)) (! (> z 0) :named a)))\n\
             (assert (< x 0))\n(check-sat)\n",
            &["unsat"][..],
        ),
        (
            "(declare-const a Int)\n(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
             (assert (< x 0))\n(check-sat)\n",
            &["unsat"],
        ),
        (
            "(declare-const x Int)\n(assert (> x 0))\n\
             (check-sat-assuming ((! (< x 0) :named h)))\n(check-sat)\n",
            &["unsat", "sat"],
        ),
        (
            "(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
             (assert (! (< x 0) :named a))\n(check-sat)\n",
            &["unknown"],
        ),
        (
            "(declare-const x Int)\n(assert (! (> x 0) :named a))\n\
             (assert (! (< x 0) :named a))\n(assert (< x 0))\n(check-sat)\n",
            &["unsat"],
        ),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn ay --stdin");
        child
            .stdin
            .as_mut()
            .expect("child stdin")
            .write_all(input.as_bytes())
            .expect("write SMT-LIB input");
        let output = child.wait_with_output().expect("wait for ay --stdin");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            answers(&stdout),
            expected,
            "input: {input}\nstdout: {stdout}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
