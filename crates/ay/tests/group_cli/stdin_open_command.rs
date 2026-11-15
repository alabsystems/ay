// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repros from the fifth label-conformance review. Stdin read a buffer as
//! soon as a plain count of `(` and `)` came out even, so a stray `)` before
//! a command left open at the end of a line, or a `\|` inside a quoted
//! symbol, read the line while that command was still open. Its open start
//! was dropped with no taint, and the rest of it on the next line became
//! stray text, while z3 reads the command on across the line. A `pop` or
//! `reset-assertions` split that way was lost and ay answered unsat where z3
//! answers sat. Stdin now runs the complete commands of a buffer and keeps
//! the open one to read on, reading the text as z3's scanner does. Each
//! repro has a twin that differs in one line. The expected answers are
//! z3 4.12.5's or `unknown`, on stdin and on a file, in z3 mode, plain mode
//! and the default posture, and on z3-mode stdin with
//! `--no-inc-linear-parse`.

use std::io::Write;
use std::process::{Command, Stdio};

use ntest::timeout;

use super::label_answer_lanes::{assert_script_pairs_on_every_input, Script};

fn z3_stdin_rescanning_every_line(input: &str) -> Vec<String> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["-q", "--z3-mode", "--no-inc-linear-parse", "-in"])
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
    let output = child.wait_with_output().expect("wait for ay -in");
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .map(str::to_string)
        .collect()
}

fn assert_pairs_on_every_input_and_rescan(pairs: &[(Script, Script)]) {
    assert_script_pairs_on_every_input(pairs);
    for (repro, twin) in pairs {
        for (name, input, z3_mode, _) in [repro, twin] {
            assert_eq!(
                z3_stdin_rescanning_every_line(input),
                *z3_mode,
                "{name}, z3 stdin with --no-inc-linear-parse:\n{input}"
            );
        }
    }
}

const A_COMMAND_OPEN_AFTER_A_STRAY_PAREN: &[(Script, Script)] = &[
    (
        (
            "split_pop_after_stray_paren",
            "(declare-const p Bool)\n(push 1) (assert false) ) (\npop 1)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
        (
            "split_pop_after_stray_paren_twin",
            "(declare-const p Bool)\n(push 1) (assert false) ) (\npop 2)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "split_reset_assertions_after_stray_paren",
            "(declare-const p Bool)\n(assert false) ) (\nreset-assertions)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
        (
            "split_reset_assertions_after_stray_paren_twin",
            "(declare-const p Bool)\n(assert false) ) (\nassert true)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "split_assert_after_stray_paren",
            "(declare-const p Bool)\n(assert p)) (\nassert false)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
        (
            "split_assert_after_stray_paren_twin",
            "(declare-const p Bool)\n(assert p)) (\nassert true)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "split_string_after_stray_paren",
            "(declare-const p Bool)\n(push 1) (assert false) ) (echo \"a\npop\") (pop 1)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
        (
            "split_string_after_stray_paren_twin",
            "(declare-const p Bool)\n(push 1) (assert false) ) (echo \"a\npop\") (pop 2)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "split_string2_after_stray_paren",
            "(declare-const p Bool)\n(push 1) (assert false) ) (echo \"a\n\") (pop 1)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
        (
            "split_string2_after_stray_paren_twin",
            "(declare-const p Bool)\n(push 1) (assert false) ) (echo \"a\n\") (pop 2)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
];

/// A command left open after a stray `)` is read on into the next line, as
/// z3 reads it: the `pop`, `reset-assertions` and `assert` run, and the pop
/// after a string that spans the line break runs too.
#[test]
#[timeout(300_000)]
fn a_command_open_after_a_stray_paren_is_read_on() {
    assert_pairs_on_every_input_and_rescan(A_COMMAND_OPEN_AFTER_A_STRAY_PAREN);
}

const A_CHECK_SAT_OPEN_AFTER_A_STRAY_PAREN: &[(Script, Script)] = &[(
    (
        "split_check_sat_after_stray_paren",
        "(declare-const p Bool)\n(assert p)) (\ncheck-sat)\n(assert (not p))\n(check-sat)\n",
        &["sat", "unsat"],
        &["sat", "unsat"],
    ),
    (
        "split_check_sat_after_stray_paren_twin",
        "(declare-const p Bool)\n(assert p)) (\ncheck-sat)\n(assert p)\n(check-sat)\n",
        &["sat", "sat"],
        &["sat", "sat"],
    ),
)];

/// A `check-sat` split across lines after a stray `)` is answered, so a
/// reader that pairs answers with queries in order reads each one right.
/// It went unanswered, and the second query's unsat was read as the first
/// one's.
#[test]
#[timeout(300_000)]
fn a_check_sat_open_after_a_stray_paren_is_answered() {
    assert_pairs_on_every_input_and_rescan(A_CHECK_SAT_OPEN_AFTER_A_STRAY_PAREN);
}

const AN_ESCAPED_BAR_IN_A_QUOTED_SYMBOL: &[(Script, Script)] = &[
    (
        (
            "escaped_bar_reads_line_early",
            "(declare-const p Bool)\n(push 1) (assert false) (get-info |a\\|)\n|) (pop 1)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
        (
            "escaped_bar_reads_line_early_twin",
            "(declare-const p Bool)\n(push 1) (assert false) (get-info |a\\|)\n|) (pop 2)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "escaped_bar_echo_reads_line_early",
            "(declare-const p Bool)\n(push 1) (assert false) (echo |a\\|)\n|) (pop 1)\n(check-sat)\n",
            &["sat"],
            &["sat"],
        ),
        (
            "escaped_bar_echo_reads_line_early_twin",
            "(declare-const p Bool)\n(push 1) (assert false) (echo |a\\|)\n|) (pop 2)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
    (
        (
            "quoted_symbol_open_at_the_end_of_input",
            "(declare-const p Bool)\n(echo \"x\")|\n(assert false)\n(check-sat)\n",
            &[],
            &[],
        ),
        (
            "quoted_symbol_open_at_the_end_of_input_twin",
            "(declare-const p Bool)\n(echo \"x\")\n(assert false)\n(check-sat)\n",
            &["unsat"],
            &["unsat"],
        ),
    ),
];

/// `\|` does not end a quoted symbol, so the symbol and its command run on
/// into the next line, and the `pop` after them runs. A `|` left open at
/// the end of a line makes the rest of the input one quoted symbol, as in
/// z3, which answers nothing.
#[test]
#[timeout(300_000)]
fn an_escaped_bar_keeps_a_quoted_symbol_open() {
    assert_pairs_on_every_input_and_rescan(AN_ESCAPED_BAR_IN_A_QUOTED_SYMBOL);
}

const A_SPLIT_POP_UNDER_GLOBAL_DECLARATIONS: &[(Script, Script)] = &[(
    (
        "split_pop_global_decls",
        "(declare-const x Int)\n(set-option :global-declarations true) (push 1) (define-fun d () Int 5) ) (\npop 1)\n(define-fun d () Int 6)\n(assert (= x d))\n(assert (= x 6))\n(check-sat)\n",
        &["sat"],
        &["unknown"],
    ),
    (
        "split_pop_global_decls_twin",
        "(declare-const x Int)\n(set-option :global-declarations true) (push 1) (define-fun d () Int 5) ) (\npop 1)\n(define-fun d () Int 6)\n(assert (= x d))\n(assert (= x 5))\n(check-sat)\n",
        &["unsat"],
        &["unknown"],
    ),
)];

/// z3 refuses `:global-declarations` once its session has started, so `d`
/// is popped and redefined as 6. z3 mode models the refusal; plain mode
/// takes the option at any point, so it withholds its answers once the
/// option changes after z3's session may have started.
#[test]
#[timeout(300_000)]
fn a_split_pop_under_global_declarations_is_read_on() {
    assert_pairs_on_every_input_and_rescan(A_SPLIT_POP_UNDER_GLOBAL_DECLARATIONS);
}
