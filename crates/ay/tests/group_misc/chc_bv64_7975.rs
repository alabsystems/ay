// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV64 CHC integration tests (#7975).
//!
//! Validates that 64-bit bitvector harnesses no longer return Unknown due
//! to the BvToBool gate. These tests model the kind of CHC problems that
//! model-checker-consumer/verification-consumer produce for Rust verification of pointer/usize operations.

#![allow(clippy::panic)]

use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

/// BV64 safe benchmark: counter from 1, bounded by 10, property x != 0.
const BV64_COUNTER_SAFE: &str = r#"(set-logic HORN)
(declare-fun Inv ((_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)))
  (=> (= x #x0000000000000001) (Inv x))))
(assert (forall ((x (_ BitVec 64)) (xp (_ BitVec 64)))
  (=> (and (Inv x) (bvult x #x000000000000000A)
           (= xp (bvadd x #x0000000000000001)))
      (Inv xp))))
(assert (forall ((x (_ BitVec 64)))
  (=> (and (Inv x) (= x #x0000000000000000)) false)))
(check-sat)
"#;

/// BV64 unsafe benchmark: counter from 0, property x < 5 (reachable at step 5).
const BV64_COUNTER_UNSAFE: &str = r#"(set-logic HORN)
(declare-fun Inv ((_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)))
  (=> (= x #x0000000000000000) (Inv x))))
(assert (forall ((x (_ BitVec 64)) (xp (_ BitVec 64)))
  (=> (and (Inv x) (= xp (bvadd x #x0000000000000001)))
      (Inv xp))))
(assert (forall ((x (_ BitVec 64)))
  (=> (and (Inv x) (= x #x0000000000000005)) false)))
(check-sat)
"#;

/// BV64 with BV operations: bitwise AND mask, property (x & 0xF) < 16.
const BV64_BITWISE_SAFE: &str = r#"(set-logic HORN)
(declare-fun Inv ((_ BitVec 64)) Bool)
(assert (forall ((x (_ BitVec 64)))
  (=> (= x #x0000000000000000) (Inv x))))
(assert (forall ((x (_ BitVec 64)) (xp (_ BitVec 64)))
  (=> (and (Inv x)
           (bvult x #x0000000000000100)
           (= xp (bvadd x #x0000000000000001)))
      (Inv xp))))
(assert (forall ((x (_ BitVec 64)))
  (=> (and (Inv x) (bvuge (bvand x #x000000000000000F) #x0000000000000010)) false)))
(check-sat)
"#;

static TEMP_BENCHMARK_ID: AtomicUsize = AtomicUsize::new(0);

struct TempBenchmarkFile {
    path: PathBuf,
}

impl TempBenchmarkFile {
    fn new(name: &str, contents: &str) -> Self {
        let id = TEMP_BENCHMARK_ID.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("ay-{name}-{}-{id}.smt2", std::process::id()));
        std::fs::write(&path, contents).expect("should materialize benchmark fixture");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempBenchmarkFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

fn run_ay_chc(benchmark: &TempBenchmarkFile) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let timeout_ms = if cfg!(debug_assertions) {
        90_000
    } else {
        30_000
    };
    let mut failed_attempts = Vec::new();

    for attempt in 1..=2 {
        let output = Command::new(ay_path)
            .arg("--chc")
            .arg(benchmark.path())
            .arg(format!("-t:{timeout_ms}"))
            .output()
            .expect("failed to spawn ay on BV64 CHC benchmark");

        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        let first_line = stdout.lines().next().unwrap_or("").trim().to_string();

        if output.status.success() {
            return first_line;
        }

        failed_attempts.push(format!(
            "attempt {attempt}: status={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status, stdout, stderr
        ));
        if attempt == 1 {
            std::thread::sleep(Duration::from_millis(100));
        }
    }

    panic!(
        "Expected zero exit status from ay on {} after retry\n{}",
        benchmark.path().display(),
        failed_attempts.join("\n--- retry boundary ---\n")
    );
}

/// #7975: BV64 safe counter must not return Unknown.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_bv64_counter_safe_7975() {
    let benchmark = TempBenchmarkFile::new("bv64-counter-safe", BV64_COUNTER_SAFE);
    let result = run_ay_chc(&benchmark);
    assert_eq!(
        result, "sat",
        "BV64 safe counter should return sat (invariant x != 0), got {result}"
    );
}

/// #7975: BV64 unsafe counter must find counterexample.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_bv64_counter_unsafe_7975() {
    let benchmark = TempBenchmarkFile::new("bv64-counter-unsafe", BV64_COUNTER_UNSAFE);
    let result = run_ay_chc(&benchmark);
    assert_eq!(
        result, "unsat",
        "BV64 unsafe counter should return unsat (reaches x=5), got {result}"
    );
}

/// #7975: BV64 bitwise mask property must not return Unknown.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_bv64_bitwise_safe_7975() {
    let benchmark = TempBenchmarkFile::new("bv64-bitwise-safe", BV64_BITWISE_SAFE);
    let result = run_ay_chc(&benchmark);
    assert_eq!(
        result, "sat",
        "BV64 bitwise AND mask property should return sat, got {result}"
    );
}
