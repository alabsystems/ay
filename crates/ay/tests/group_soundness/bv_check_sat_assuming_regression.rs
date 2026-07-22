// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Regression test for issue #1539:
// check-sat-assuming with BV+ITE returned invalid SAT results.
//
// Root cause: BvSolver.process_assertion() didn't handle TermData::Ite,
// causing Bool-sorted ITEs to be silently ignored. Assumptions referencing
// such ITEs would be unconstrained, leading to incorrect SAT results.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// Issue #1539: check-sat-assuming with BV+ITE should return unsat
///
/// This test reproduces the exact minimal reproducer from issue #1539.
/// Before the fix, AY incorrectly returned SAT with an invalid model.
#[test]
#[timeout(60000)]
fn test_bv_check_sat_assuming_ite_regression_issue_1539() {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    // Minimal reproducer from issue #1539
    let test_input = r#"(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(check-sat-assuming (
  (not (ite (= (concat (concat (_ bv0 1) ((_ extract 3 2) a)) ((_ extract 6 5) a))
               ((_ extract 6 2) a))
            (= ((_ extract 6 2) a) (_ bv0 5))
            true))
))
"#;

    let temp_path = {
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time after unix epoch")
            .as_nanos();
        let pid = std::process::id();
        std::env::temp_dir().join(format!("ay_bv_check_sat_assuming_{pid}_{nanos}.smt2"))
    };

    std::fs::write(&temp_path, test_input).unwrap();

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output_timeout(Duration::from_secs(55))
        .expect("Failed to run ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("AY stdout: {stdout:?}");
    eprintln!("AY stderr: {stderr:?}");
    eprintln!("AY exit: {:?}", output.status);

    // Clean up temp file
    let _ = std::fs::remove_file(&temp_path);

    assert!(
        output.status.success(),
        "AY exited with {:?}",
        output.status
    );
    assert!(
        stdout.contains("unsat"),
        "Expected 'unsat' (check-sat-assuming with ITE should correctly find unsatisfiable), got: {stdout}"
    );
}

/// Verify that a simple BV ITE with assert (not check-sat-assuming) also works.
/// This is a sanity check that the ITE processing fix works for both paths.
#[test]
#[timeout(60000)]
fn test_bv_ite_assert_sanity_check() {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let test_input = r#"(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; ite(x < y, true, false) = p
; Then assert p != p (always false)
(define-fun p () Bool (ite (bvult x y) true false))
(assert (= p (not p)))
(check-sat)
"#;

    let temp_path = {
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time after unix epoch")
            .as_nanos();
        let pid = std::process::id();
        std::env::temp_dir().join(format!("ay_bv_ite_sanity_{pid}_{nanos}.smt2"))
    };

    std::fs::write(&temp_path, test_input).unwrap();

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output_timeout(Duration::from_secs(55))
        .expect("Failed to run ay");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Clean up temp file
    let _ = std::fs::remove_file(&temp_path);

    assert!(
        output.status.success(),
        "AY exited with {:?}",
        output.status
    );
    assert!(
        stdout.contains("unsat"),
        "Expected 'unsat' (p = not p is unsatisfiable), got: {stdout}"
    );
}
