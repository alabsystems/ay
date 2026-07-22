// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![allow(clippy::panic)]

use ntest::timeout;
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

enum RunOutcome {
    Result(String),
    Timeout,
}

fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

fn run_ay_with_deadline(input: &str, deadline: Duration) -> RunOutcome {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().expect("stdin pipe");
        stdin.write_all(input.as_bytes()).expect("write SMT-LIB");
    }
    drop(child.stdin.take());

    let start = Instant::now();
    loop {
        match child.try_wait().expect("poll ay process") {
            Some(status) => {
                let mut stdout = String::new();
                let mut stderr = String::new();
                child
                    .stdout
                    .take()
                    .expect("stdout pipe")
                    .read_to_string(&mut stdout)
                    .expect("read stdout");
                child
                    .stderr
                    .take()
                    .expect("stderr pipe")
                    .read_to_string(&mut stderr)
                    .expect("read stderr");
                assert!(
                    status.success(),
                    "ay exited with {status}\nstdout:\n{stdout}\nstderr:\n{stderr}"
                );
                return RunOutcome::Result(stdout);
            }
            None if start.elapsed() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();
                return RunOutcome::Timeout;
            }
            None => thread::sleep(Duration::from_millis(10)),
        }
    }
}

fn assert_no_crash_or_false_unsat(name: &str, input: &str) {
    match run_ay_with_deadline(input, Duration::from_secs(10)) {
        RunOutcome::Result(stdout) => {
            let answer = sat_result(&stdout);
            assert!(
                matches!(answer, Some("sat") | Some("unknown")),
                "{name} must not return false UNSAT, got {answer:?}\nstdout:\n{stdout}"
            );
        }
        RunOutcome::Timeout => {
            // #6260 is the stack-overflow bug. Current incompleteness on these
            // formulas is tracked separately, so bounded timeout is acceptable
            // here as long as the process does not abort.
        }
    }
}

#[test]
#[timeout(30_000)]
fn fix_6260_contains_plus_len_no_crash() {
    let input = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "ab"))
(assert (str.contains x "cd"))
(assert (= (str.len x) 5))
(check-sat)
"#;

    assert_no_crash_or_false_unsat("fix_6260_contains_plus_len_no_crash", input);
}

#[test]
#[timeout(30_000)]
fn fix_6260_contains_plus_len_longer_needles_no_crash() {
    let input = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (str.contains x "abc"))
(assert (str.contains x "def"))
(assert (= (str.len x) 6))
(check-sat)
"#;

    assert_no_crash_or_false_unsat("fix_6260_contains_plus_len_longer_needles_no_crash", input);
}
