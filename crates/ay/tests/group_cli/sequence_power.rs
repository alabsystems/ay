// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::spawn::OutputTimeout;
use std::process::Command;
use std::time::Duration;

#[test]
fn sequence_power_unbounded_exponent_models_survive_push_and_pop() {
    let input = br#"(set-logic ALL)
(declare-const n Int)
(assert (= (seq.power "ab" n) "ababab"))
(check-sat)
(get-value (n (seq.power "ab" n)))
(push 1)
(assert (> n 10))
(check-sat)
(pop 1)
(check-sat)
(get-value (n (seq.power "ab" n)))
"#;
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["--z3-mode", "-in", "-T:2", "-memory:256"])
        .output_timeout_with_stdin(input, Duration::from_secs(10))
        .expect("run sequence power session");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8 transcript");
    assert!(output.status.success(), "{stdout}");
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
    let statuses: Vec<_> = stdout
        .lines()
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(statuses, ["sat", "unsat", "sat"], "{stdout}");
    assert_eq!(stdout.matches("(n 3)").count(), 2, "{stdout}");
    assert_eq!(stdout.matches("\"ababab\"").count(), 2, "{stdout}");
}
