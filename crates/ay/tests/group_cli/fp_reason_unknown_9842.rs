// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #9842: unsupported FP operations must surface a stable consumer-facing
//! `reason-unknown unsupported` contract through the CLI.

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_fp_reason_unknown_9842_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp smt2");
    (path.clone(), CleanupGuard(path))
}

// NOTE: these tests originally used fp.rem on Float64 as the unsupported
// operation. fp.rem is now fully supported at every precision (exact bounded
// modular reduction, commit 143b360e4d; unit tests flipped in fe15d793d6), so
// the CLI contract is exercised with an operation that is still genuinely
// unsupported: (_ to_fp eb sb) applied to a non-ground Real term.

#[test]
#[timeout(30_000)]
fn unsupported_to_fp_real_reports_unsupported_reason_on_cli() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp(
        "(set-logic QF_FPLRA)\n\
         (declare-fun r () Real)\n\
         (declare-fun x () (_ FloatingPoint 11 53))\n\
         (assert (= ((_ to_fp 11 53) RNE r) x))\n\
         (check-sat)\n\
         (get-info :reason-unknown)\n\
         (exit)\n",
    );

    let output = Command::new(ay_path)
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.trim().lines().next().unwrap_or("").to_string();

    assert_eq!(
        output.status.code(),
        Some(0),
        "Expected CLI unsupported-FP regression to exit cleanly.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        first_line, "unknown",
        "Unsupported FP operation should return unknown on stdout.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("(:reason-unknown unsupported)"),
        "Expected explicit get-info reason on stdout for unsupported FP op.\nstdout:\n{stdout}"
    );
    assert!(
        stderr.contains("(:reason-unknown unsupported)"),
        "Expected CLI stderr reason for unsupported FP op.\nstderr:\n{stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn unsupported_to_fp_real_reports_unknown_result_in_stats_json() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp(
        "(set-logic QF_FPLRA)\n\
         (declare-fun r () Real)\n\
         (assert (fp.isNaN ((_ to_fp 11 53) RNE r)))\n\
         (check-sat)\n\
         (exit)\n",
    );

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--stats-json")
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.trim().lines().next().unwrap_or("").to_string();

    assert_eq!(
        output.status.code(),
        Some(0),
        "Expected stats-json unsupported-FP regression to exit cleanly.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        first_line, "unknown",
        "Unsupported FP operation should still report unknown on stdout.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("\"result\":\"unknown\""),
        "Stats JSON should report unknown, not sat.\nstderr:\n{stderr}"
    );
}

/// Guards the capability that made the original #9842 inputs stale: fp.rem on
/// Float64 is fully supported (commit 143b360e4d) and must answer sat, not
/// unknown, through the CLI.
#[test]
#[timeout(30_000)]
fn fp_rem_float64_is_supported_and_reports_sat_on_cli() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (input, _cleanup) = write_temp(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 11 53))\n\
         (declare-fun y () (_ FloatingPoint 11 53))\n\
         (assert (= (fp.rem x y) x))\n\
         (check-sat)\n\
         (exit)\n",
    );

    let output = Command::new(ay_path)
        .arg(&input)
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.trim().lines().next().unwrap_or("").to_string();

    assert_eq!(
        output.status.code(),
        Some(0),
        "Expected supported fp.rem Float64 solve to exit cleanly.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        first_line, "sat",
        "fp.rem Float64 is supported and this instance is trivially sat.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
