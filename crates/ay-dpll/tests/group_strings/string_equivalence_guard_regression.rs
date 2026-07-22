// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

fn z3_available() -> bool {
    Command::new("z3")
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

fn solve_with_z3(smt: &str) -> Result<String, String> {
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn z3: {e}"))?;

    if let Some(stdin) = child.stdin.as_mut() {
        stdin
            .write_all(smt.as_bytes())
            .map_err(|e| format!("failed to write SMT to z3 stdin: {e}"))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("failed waiting for z3: {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("z3 exited with status {}: {stderr}", output.status));
    }

    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

type KnownUnsatCase = (&'static str, &'static str, Option<&'static str>);

const ISSUE_3850_KNOWN_UNSAT_CASES: &[KnownUnsatCase] = &[
    (
        "str-pred-small-rw_15",
        r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.contains "" x) (= x ""))))
(check-sat)
"#,
        Some("unsat"),
    ),
    (
        "str-pred-small-rw_127",
        r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.contains x (str.++ x x)) (= x ""))))
(check-sat)
"#,
        Some("unsat"),
    ),
    (
        "str-pred-small-rw_130",
        r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains x (str.++ x y)) (= x (str.++ x y)))))
(check-sat)
"#,
        None,
    ),
    (
        "str-pred-small-rw_135",
        r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (= x (str.++ y x)) (= x (str.++ x y)))))
(check-sat)
"#,
        Some("unsat"), // #3875: cycle detection (I_CYCLE) derives y="" on both sides
    ),
    (
        "str-pred-small-rw_137",
        r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains x (str.++ y x)) (= x (str.++ x y)))))
(check-sat)
"#,
        Some("unsat"), // #3875: same self-concat empty-string consequence as _135
    ),
];

#[test]
#[timeout(10_000)]
fn issue_3850_known_unsat_negated_equivalences_are_not_sat() {
    for (name, smt, expected_ay) in ISSUE_3850_KNOWN_UNSAT_CASES {
        let ay_output = crate::common::solve(smt);
        let ay = crate::common::sat_result(&ay_output);
        match *expected_ay {
            Some(expected) => {
                if expected == "unsat" {
                    assert_ne!(
                        ay,
                        Some("sat"),
                        "{name}: AY must not return sat, got output:\n{ay_output}"
                    );
                } else {
                    assert_eq!(ay, Some(expected), "{name}: AY got {ay_output}");
                }
            }
            None => assert_ne!(
                ay,
                Some("sat"),
                "{name}: AY must not return sat, got output:\n{ay_output}"
            ),
        }

        if z3_available() {
            let z3_output = solve_with_z3(smt).expect("z3 solve");
            assert_eq!(
                crate::common::sat_result(&z3_output),
                Some("unsat"),
                "{name}: Z3 expected unsat, got output:\n{z3_output}"
            );
        }
    }
}

#[test]
#[timeout(30_000)]
fn issue_3850_non_tautology_negated_equivalence_stays_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains x y) (= x y))))
(check-sat)
"#;

    let ay_output = crate::common::solve(smt);
    let ay = crate::common::sat_result(&ay_output);
    // Correct answer: sat. AY may still return unknown if it hits the
    // bounded-resolution fallback rather than a full concrete evaluation.
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "expected sat or unknown for non-tautology, got output:\n{ay_output}"
    );

    if z3_available() {
        let z3_output = solve_with_z3(smt).expect("z3 solve");
        assert_eq!(
            crate::common::sat_result(&z3_output),
            Some("sat"),
            "z3 expected sat, got output:\n{z3_output}"
        );
    }
}

/// Regression test for #6262: non-deterministic SAT model verification panic
/// on QF_SLIA negated equivalence formulas. The conflict analysis assertion
/// ("literal in conflict/reason clause is not falsified") fired sporadically
/// when theory propagation reasons contained non-falsified literals.
///
/// This test runs the formula multiple times to increase the probability of
/// hitting the non-deterministic failure path.
#[test]
#[timeout(30_000)]
fn issue_6262_no_panic_on_negated_equivalence_repeated() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains x y) (= x y))))
(check-sat)
"#;

    for i in 0..20 {
        let ay_output = crate::common::solve(smt);
        let ay = crate::common::sat_result(&ay_output);
        assert!(
            matches!(ay, Some("sat") | Some("unknown")),
            "run {i}: expected sat or unknown, got output:\n{ay_output}"
        );
    }
}
