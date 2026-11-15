// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression: ay must NOT report UNSAFE (`unsat`) on the CHC-COMP
//! 2026 `vmt-chc/bv/pc_sfifo_2` system, which is SAFE.
//!
//! This solver's CHC-COMP 2026 submission answered `unsat` (a false
//! counterexample) on it. z3 (spacer) answers `sat` after about six minutes
//! (measured 2026-09-25, z3 -T:1200: sat in 350 s wall). The correct answer is
//! `sat`; `unknown` is the acceptable interim answer; `unsat` is the bug.
//!
//! Ported from the pre-publication history (a318e8b09d, 2026-05-16), which
//! kept the instance as a benchmark but never reached the published tree.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// Solver budget. The assertion is only "not `unsat`", so a short budget keeps
/// the test cheap without weakening it.
const SOLVE_SECONDS: u32 = 15;

#[test]
#[timeout(90_000)]
fn ay_must_not_report_false_unsafe_on_pc_sfifo_2() {
    let bench = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_soundness/fixtures/chc_pc_sfifo_2_bv.smt2");
    assert!(bench.exists(), "benchmark missing at {}", bench.display());
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--chc")
        .arg("--no-proof")
        .arg(format!("-T:{SOLVE_SECONDS}"))
        .arg(&bench)
        .output_timeout(Duration::from_secs(u64::from(SOLVE_SECONDS) + 30))
        .expect("failed to run ay");
    let verdict = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("")
        .to_string();
    assert_ne!(
        verdict, "unsat",
        "false-UNSAFE soundness bug: ay reported unsat on the safe pc_sfifo_2 \
         CHC system; correct answer is sat, acceptable interim is unknown"
    );
}
