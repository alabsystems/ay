// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #chc25-crash: a solve-session child that dies from an abnormal abort must
//! never cost the harness record. The provenance wrapper converts the crash
//! into the fail-closed `unknown` verdict (stdout status line + clean exit 0),
//! mirroring the SIGTERM/hard-timeout fallbacks.
//!
//! Real-world producer: chc-comp25 SLayerCF BV towers at competition budgets
//! under machine-wide memory pressure — an allocation failure exits through
//! Rust's `rust_oom` fail-fast (`abort()`; exception 0xC0000409 on Windows,
//! SIGABRT on unix) before the in-process `process_memory_exceeded()`
//! checkpoints can trip. The `AY_INTERNAL_TEST_ABORT_SOLVE_CHILD` hook makes
//! the child take exactly that abort path deterministically.

use ntest::timeout;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

struct Cleanup(PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn write_temp_horn(tag: &str) -> (PathBuf, Cleanup) {
    let path = std::env::temp_dir().join(format!(
        "ay_wrapper_crash_{tag}_{}_{}.smt2",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after Unix epoch")
            .as_nanos()
    ));
    let formula = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 5)) false)))
(check-sat)
"#;
    fs::write(&path, formula).expect("write temp horn file");
    let cleanup = Cleanup(path.clone());
    (path, cleanup)
}

/// A crashed solve child (simulated `rust_oom` abort) is converted by the
/// wrapper into the fail-closed `unknown` verdict with a clean exit code.
#[test]
#[timeout(60_000)]
fn test_wrapper_converts_child_abort_to_unknown() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (path, _cleanup) = write_temp_horn("abort");

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg("--competition")
        .arg("--timeout")
        .arg("10000")
        .arg(&path)
        // Cargo sets CARGO_TARGET_TMPDIR for integration tests, which disables
        // the provenance wrapper; remove it so the wrapper engages as in a
        // real harness run.
        .env_remove("CARGO_TARGET_TMPDIR")
        .env("AY_INTERNAL_TEST_ABORT_SOLVE_CHILD", "1")
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("stdout: {stdout:?}");
    eprintln!("stderr: {stderr:?}");
    eprintln!("exit: {:?}", output.status);

    assert!(
        stdout.lines().any(|line| line.trim() == "unknown"),
        "wrapper must emit the fail-closed `unknown` verdict after a child \
         crash, got stdout={stdout:?} stderr={stderr:?}"
    );
    assert!(
        stderr.contains("aborted abnormally"),
        "wrapper must log the crash diagnostic on stderr, got: {stderr:?}"
    );
    assert!(
        stderr.contains("reason-unknown"),
        "wrapper must emit the reason-unknown line, got: {stderr:?}"
    );
    assert_eq!(
        output.status.code(),
        Some(0),
        "a crash converted to `unknown` must exit cleanly (0), got {:?}",
        output.status
    );
}

/// A DELIBERATE error exit must keep its error status: the crash classifier
/// only reinterprets abnormal aborts, never intentional nonzero exits. An
/// invalid CLI flag makes the wrapped child exit 2 (clap usage error) — the
/// wrapper must propagate that code untouched. (A missing input FILE is not
/// usable here: the CHC runner itself fails closed to `unknown`/exit 0 on
/// read errors, by design.)
#[test]
#[timeout(60_000)]
fn test_wrapper_propagates_deliberate_error_exit() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (path, _cleanup) = write_temp_horn("deliberate");

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg("--definitely-not-a-flag")
        .arg(&path)
        .env_remove("CARGO_TARGET_TMPDIR")
        .output()
        .expect("spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("stdout: {stdout:?}");
    eprintln!("stderr: {stderr:?}");
    eprintln!("exit: {:?}", output.status);

    assert_eq!(
        output.status.code(),
        Some(2),
        "a deliberate clap usage-error exit must stay exit 2, got {:?}",
        output.status
    );
    assert!(
        !stdout.lines().any(|line| line.trim() == "unknown"),
        "a deliberate error exit must not be rewritten to `unknown`, got \
         stdout={stdout:?}"
    );
    assert!(
        !stderr.contains("aborted abnormally"),
        "a deliberate error exit must not be classified as a crash, got: \
         {stderr:?}"
    );
}
