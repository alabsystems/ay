// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
// QF_LIA algebraic substitution regressions (#51).

use ntest::timeout;
use std::fs;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn run_ay_smt2(src: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock before UNIX_EPOCH")
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "ay_qf_lia_algebraic_substitution_{}_{}.smt2",
        std::process::id(),
        stamp
    ));
    fs::write(&path, src).expect("failed to write temporary SMT-LIB input");

    let output = Command::new(ay_path)
        .arg(path.as_os_str())
        .output()
        .expect("failed to spawn ay");
    let _ = fs::remove_file(&path);

    assert!(
        output.status.success(),
        "ay exited with {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8_lossy(&output.stdout)
        .trim()
        .lines()
        .next()
        .unwrap_or("")
        .to_string()
}

#[test]
#[timeout(30_000)]
fn test_qf_lia_affine_substitution_chain_unsat_issue_51() {
    let result = run_ay_smt2(
        r#"(set-logic QF_LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (= a (+ b 1)))
(assert (= b (- c 1)))
(assert (not (= a c)))
(check-sat)
"#,
    );
    assert_eq!(result, "unsat");
}

#[test]
#[timeout(30_000)]
fn test_qf_lia_affine_substitution_non_implied_offset_sat_issue_51() {
    let result = run_ay_smt2(
        r#"(set-logic QF_LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (= a (+ b 1)))
(assert (= b (- c 2)))
(assert (not (= a c)))
(check-sat)
"#,
    );
    assert_eq!(result, "sat");
}
