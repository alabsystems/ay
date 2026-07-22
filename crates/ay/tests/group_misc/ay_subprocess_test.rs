// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Test for AY subprocess spawning
// Reproduces issue: https://docs.KANI_FAST_CRITICAL_AY_SIGKILL_BUG_2026-01-02.md

use ntest::timeout;
use std::process::Command;

#[test]
#[timeout(30_000)]
fn test_ay_subprocess_spawn() {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let test_input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;

    // Write to temp file using portable temp directory (#531)
    let temp_path =
        std::env::temp_dir().join(format!("ay_subprocess_test_{}.smt2", std::process::id()));
    std::fs::write(&temp_path, test_input).unwrap();
    // Clean up temp file when done (uses Drop guard)
    struct CleanupGuard(std::path::PathBuf);
    impl Drop for CleanupGuard {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _cleanup = CleanupGuard(temp_path.clone());

    // Spawn AY
    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("AY stdout: {stdout:?}");
    eprintln!("AY stderr: {stderr:?}");
    eprintln!("AY exit: {:?}", output.status);

    assert!(
        output.status.success(),
        "AY exited with {:?}",
        output.status
    );
    // Check first line equals exactly "sat" (not "unsat" which also contains "sat")
    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected 'sat', got: {stdout}");
}

#[test]
#[timeout(30_000)]
fn test_ay_stdin_spawn() {
    let ay_path = env!("CARGO_BIN_EXE_ay");

    let test_input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;

    // Spawn AY with stdin
    use std::io::Write;
    use std::process::Stdio;

    let mut child = Command::new(ay_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn ay");

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(test_input.as_bytes()).unwrap();
    }

    let output = child.wait_with_output().expect("Failed to wait on ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("AY stdin stdout: {stdout:?}");
    eprintln!("AY stdin stderr: {stderr:?}");
    eprintln!("AY stdin exit: {:?}", output.status);

    assert!(
        output.status.success(),
        "AY exited with {:?}",
        output.status
    );
    // Check first line equals exactly "sat" (not "unsat" which also contains "sat")
    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected 'sat', got: {stdout}");
}
