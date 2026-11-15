// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Under `--z3-mode`, `(reset-assertions)` keeps z3's assertion levels, and
//! what is asserted or declared afterwards belongs to them: popping a level
//! removes it. The expected answers are z3 4.12.5's.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

fn run_z3_mode(input: &str) -> std::process::Output {
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

fn answers(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

fn assert_answers(input: &str, expected: &[&str]) -> String {
    let output = run_z3_mode(input);
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert_eq!(
        answers(&stdout),
        expected,
        "input: {input}\nstdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

/// `(pop 2)` closes the level pushed after the reset, and with it `x = 1`.
/// This answered `unsat`.
#[test]
#[timeout(60_000)]
fn a_pop_through_the_retained_level_removes_later_assertions() {
    assert_answers(
        "(declare-const x Int)\n(push)\n(reset-assertions)\n(push)\n(assert (= x 1))\n\
         (pop 2)\n(assert (= x 2))\n(check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(declare-const x Int)\n(push)\n(reset-assertions)\n(push)\n(assert (= x 1))\n\
         (push)\n(assert (> x 0))\n(pop 3)\n(assert (= x 2))\n(check-sat)\n",
        &["sat"],
    );
}

/// An assertion made at the retained level itself is removed by its pop.
/// This answered `unsat`.
#[test]
#[timeout(60_000)]
fn an_assertion_at_the_retained_level_is_popped_with_it() {
    assert_answers(
        "(declare-const x Int)\n(push)\n(reset-assertions)\n(assert (= x 1))\n(pop)\n\
         (assert (= x 2))\n(check-sat)\n",
        &["sat"],
    );
    assert_answers(
        "(set-option :global-declarations true)\n(declare-const x Int)\n(push)\n\
         (reset-assertions)\n(assert (= x 1))\n(pop)\n(assert (= x 2))\n(check-sat)\n",
        &["sat"],
    );
}

/// A definition made at the retained level is removed by its pop, so a new
/// definition of the name is accepted. This answered `unsat`.
#[test]
#[timeout(60_000)]
fn a_definition_at_the_retained_level_is_popped_with_it() {
    let stdout = assert_answers(
        "(push)\n(reset-assertions)\n(define-fun five () Int 5)\n(pop)\n\
         (define-fun five () Int 7)\n(assert (not (= five 5)))\n(check-sat)\n",
        &["sat"],
    );
    assert!(!stdout.contains("(error"), "stdout: {stdout}");
}

/// A definition made in a level before the reset outlives the reset in the
/// executor, but z3 removes it with the level. The session cannot model that,
/// so once the level is popped it withholds verdicts. This answered `unsat`,
/// where z3 answers `sat`.
#[test]
#[timeout(60_000)]
fn a_definition_from_before_the_reset_withholds_verdicts_once_its_level_is_popped() {
    assert_answers(
        "(declare-const x Int)\n(push)\n(define-fun five () Int 5)\n(reset-assertions)\n\
         (assert (= x five))\n(check-sat)\n(pop)\n(define-fun five () Int 7)\n\
         (assert (not (= five 5)))\n(check-sat)\n",
        &["sat", "unknown"],
    );
    // Under global declarations z3 keeps the definition too, so nothing is withheld.
    assert_answers(
        "(set-option :global-declarations true)\n(push)\n(define-fun five () Int 5)\n\
         (reset-assertions)\n(pop)\n(define-fun five () Int 7)\n(assert (not (= five 5)))\n\
         (check-sat)\n",
        &["unsat"],
    );
}

/// The unsat core names only assertions still in force: `a1` was popped.
#[test]
#[timeout(60_000)]
fn the_unsat_core_after_a_pop_through_the_retained_level() {
    let stdout = assert_answers(
        "(set-option :produce-unsat-cores true)\n(declare-const x Int)\n(push)\n\
         (reset-assertions)\n(push)\n(assert (! (= x 1) :named a1))\n(pop 2)\n\
         (assert (! (= x 2) :named a2))\n(assert (! (= x 3) :named a3))\n(check-sat)\n\
         (get-unsat-core)\n",
        &["unsat"],
    );
    assert!(stdout.contains("(a2 a3)"), "stdout: {stdout}");
}
