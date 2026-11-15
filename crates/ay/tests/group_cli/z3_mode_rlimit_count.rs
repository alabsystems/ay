// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `:rlimit-count` is z3's session resource counter, and a driver reads it as
//! one. Verus's AIR reads it before a query's declarations, after its
//! assertion and after its `check-sat`, and subtracts successive readings as
//! `u64` (`air/src/smt_verify.rs:547-548`); a reading below an earlier one is
//! an arithmetic overflow panic, which aborts `rust_verify`. z3 4.12.5 and
//! 4.16.0 report one counter under `(get-info :rlimit)` and `:rlimit-count`;
//! it never decreases, `(reset-assertions)` keeps it, and `(reset)` starts a
//! new count. AY counts its own recorded solver work, beginning at zero;
//! upstream's numeric units are not an oracle for AY's work.
//!
//! ay reported the executor's own statistics after a query, which describe
//! that one check-sat and start again in the executor that a failed command
//! is replaced by: a failed query took the reading from 365 to 0 in
//! `examples::assorted_demo`.

use super::z3_mode_failed_command::{DECLS, FAILING_QUERY};
use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

const ALL_STATISTICS: &str = "(get-info :all-statistics)\n";
const EPOCH_MARKER: &str = "rlimit-epoch";

fn run_z3_mode(input: &str) -> (String, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["-q", "--z3-mode", "-smt2", "-in"])
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
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// One reading of the counter, in output order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reading {
    /// `:rlimit-count N` from `(get-info :all-statistics)`.
    Count(u64),
    /// `(:rlimit N)` from `(get-info :rlimit)`.
    Rlimit(u64),
    /// The echoed marker the instrumented sessions print after `(reset)`.
    Epoch,
}

fn readings(stdout: &str) -> Vec<Reading> {
    let number = |text: &str| -> u64 {
        let digits: String = text
            .trim_start()
            .chars()
            .take_while(char::is_ascii_digit)
            .collect();
        digits
            .parse()
            .unwrap_or_else(|_| panic!("no counter value in {text:?}"))
    };
    stdout
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            if line.trim_matches('"') == EPOCH_MARKER {
                return Some(Reading::Epoch);
            }
            if let Some(rest) = line.strip_prefix("(:rlimit ") {
                return Some(Reading::Rlimit(number(rest)));
            }
            let at = line.find(":rlimit-count ")?;
            Some(Reading::Count(number(&line[at + ":rlimit-count ".len()..])))
        })
        .collect()
}

fn answers(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

/// Split a script into its top-level commands.
fn commands(script: &str) -> Vec<String> {
    let mut out = Vec::new();
    let (mut depth, mut in_string, mut start) = (0usize, false, None);
    for (at, ch) in script.char_indices() {
        match ch {
            '"' => in_string = !in_string,
            '(' if !in_string => {
                if depth == 0 {
                    start = Some(at);
                }
                depth += 1;
            }
            ')' if !in_string => {
                depth -= 1;
                if depth == 0 {
                    let from = start.take().expect("command start");
                    out.push(script[from..=at].to_string());
                }
            }
            _ => {}
        }
    }
    assert_eq!(depth, 0, "unbalanced script: {script}");
    out
}

/// Read both keys after every command, and mark every `(reset)`.
fn instrument(script: &str) -> String {
    let mut out = String::new();
    for command in commands(script) {
        out.push_str(&command);
        out.push('\n');
        if command == "(reset)" {
            out.push_str(&format!("(echo \"{EPOCH_MARKER}\")\n"));
        }
        out.push_str(ALL_STATISTICS);
        out.push_str("(get-info :rlimit)\n");
    }
    out
}

/// Within a `(reset)` epoch the counter never decreases, the
/// epoch after a `(reset)` starts at zero, and `(get-info :rlimit)` reports the
/// same counter as `:rlimit-count`.
fn assert_counter_law(readings: &[Reading], context: &str) {
    let mut last: Option<u64> = None;
    let mut epoch_start = false;
    for (index, reading) in readings.iter().enumerate() {
        match *reading {
            Reading::Epoch => {
                last = None;
                epoch_start = true;
            }
            Reading::Count(count) => {
                if epoch_start {
                    assert_eq!(
                        count, 0,
                        "the first reading after (reset), #{index}: {context}"
                    );
                    epoch_start = false;
                }
                if let Some(previous) = last {
                    assert!(
                        count >= previous,
                        ":rlimit-count went from {previous} to {count} at reading #{index}: \
                         {context}"
                    );
                }
                last = Some(count);
            }
            Reading::Rlimit(rlimit) => assert_eq!(
                Some(rlimit),
                last,
                "(get-info :rlimit) must report the counter :rlimit-count just reported, \
                 reading #{index}: {context}"
            ),
        }
    }
}

/// AIR's three readings around a query that the executor refuses, and the
/// readings of the queries after it in the same session.
#[test]
#[timeout(120_000)]
fn rlimit_count_never_decreases_across_a_refused_query() {
    let failing_query =
        FAILING_QUERY.replace("(check-sat)", &format!("{ALL_STATISTICS}(check-sat)"));
    let input = format!(
        "{DECLS}{ALL_STATISTICS}(push)\n{ALL_STATISTICS}{failing_query}\
         (get-info :reason-unknown)\n{ALL_STATISTICS}(get-info :rlimit)\n(pop)\n\
         (push)\n{ALL_STATISTICS}(declare-const n Int)\n(assert (> n 3))\n{ALL_STATISTICS}\
         (check-sat)\n{ALL_STATISTICS}(get-info :rlimit)\n(pop)\n\
         (push)\n{ALL_STATISTICS}{failing_query}{ALL_STATISTICS}(pop)\n\
         {ALL_STATISTICS}(check-sat)\n{ALL_STATISTICS}"
    );
    let (stdout, stderr) = run_z3_mode(&input);
    assert_eq!(
        answers(&stdout),
        ["unknown", "sat", "unknown", "sat"],
        "both refusals must happen, or this proves nothing; stdout: {stdout}; stderr: {stderr}"
    );
    assert!(
        stdout.contains("(incomplete decision-execution-error"),
        "the unknowns are execution failures; stdout: {stdout}"
    );
    let readings = readings(&stdout);
    let counts = readings
        .iter()
        .filter(|reading| matches!(reading, Reading::Count(_)))
        .count();
    assert_eq!(
        counts, 12,
        "one count per (get-info :all-statistics): {readings:?}"
    );
    assert_counter_law(&readings, &stdout);
}

/// Reset-assertions preserves recorded work, while reset begins at zero.
#[test]
#[timeout(120_000)]
fn rlimit_count_follows_z3_across_reset_assertions_and_reset() {
    let input = "(declare-const x Int)\n(declare-const y Int)\n(assert (> (+ x y) 10))\n\
                 (assert (< x 3))\n(check-sat)\n(get-info :all-statistics)\n\
                 (reset-assertions)\n(get-info :all-statistics)\n(get-info :rlimit)\n\
                 (reset)\n(get-info :all-statistics)\n(get-info :rlimit)\n";
    let (stdout, stderr) = run_z3_mode(input);
    assert_eq!(
        answers(&stdout),
        ["sat"],
        "stdout: {stdout}; stderr: {stderr}"
    );
    use Reading::{Count, Rlimit};
    let readings = readings(&stdout);
    let [Count(query), Count(reset_assertions), Rlimit(rlimit), Count(reset), Rlimit(rlimit_reset)] =
        readings[..]
    else {
        panic!("five readings expected: {readings:?}; stdout: {stdout}");
    };
    assert_eq!(reset_assertions, query, "stdout: {stdout}");
    assert_eq!(rlimit, reset_assertions, "stdout: {stdout}");
    assert_eq!((reset, rlimit_reset), (0, 0), "stdout: {stdout}");
}

/// The law after every command of sessions shaped like the Verus fix queue's
/// reproducers: refusals at top level and inside a scope, a model asked for
/// after a refusal, sat and unsat answers, assumptions, and both resets.
#[test]
#[timeout(300_000)]
fn rlimit_count_obeys_the_z3_law_after_every_command() {
    let sessions = [
        format!(
            "{DECLS}(push)\n{FAILING_QUERY}(get-info :reason-unknown)\n(get-model)\n(pop)\n\
             (push)\n(assert (= a 7))\n(check-sat)\n(get-value (a))\n(pop)\n(check-sat)\n"
        ),
        format!("{DECLS}{FAILING_QUERY}(echo \"after-error\")\n(push)\n(assert false)\n(check-sat)\n(pop)\n(check-sat)\n"),
        "(set-option :produce-models true)\n(declare-const a Int)\n(assert (= a 3))\n\
         (push 1)\n(declare-const x (_ BitVec 8))\n(declare-const i Int)\n\
         (declare-const j Int)\n(assert (= (* i j) 7))\n(assert (= x #x01))\n(check-sat)\n\
         (pop 1)\n(check-sat)\n(get-value (a))\n"
            .to_string(),
        "(declare-const p Bool)\n(declare-const q Bool)\n(assert (=> p q))\n\
         (check-sat-assuming (p (not q)))\n(check-sat-assuming (p))\n(get-value (q))\n\
         (reset-assertions)\n(assert (and p (not p)))\n(check-sat)\n(reset)\n\
         (declare-const r Int)\n(assert (> r 0))\n(check-sat)\n(reset)\n(check-sat)\n"
            .to_string(),
        format!(
            "{DECLS}(declare-const x Int)\n(push)\n(assert (= x 1))\n{FAILING_QUERY}(pop)\n\
             (reset)\n{DECLS}(declare-const x Int)\n(push)\n{FAILING_QUERY}(pop)\n\
             (assert (= x 2))\n(check-sat)\n"
        ),
    ];
    let mut unknowns = 0;
    for session in &sessions {
        let (stdout, stderr) = run_z3_mode(&instrument(session));
        unknowns += answers(&stdout)
            .iter()
            .filter(|answer| **answer == "unknown")
            .count();
        let readings = readings(&stdout);
        let commands = commands(session).len();
        let counts = readings
            .iter()
            .filter(|reading| matches!(reading, Reading::Count(_)))
            .count();
        assert_eq!(
            counts, commands,
            "one count after each command; session:\n{session}\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert_counter_law(&readings, &format!("session:\n{session}\nstdout: {stdout}"));
    }
    assert!(
        unknowns >= 4,
        "the sessions must reach the refused query: {unknowns}"
    );
}
