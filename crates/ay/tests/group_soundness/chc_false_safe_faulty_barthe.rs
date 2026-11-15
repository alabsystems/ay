// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression: ay must NOT report SAFE (`sat`) on the CHC-COMP 2026
//! `llreve-bench/smt2/faulty__barthe!_000` pair.
//!
//! Both variants are UNSAFE (expected `unsat`): the benchmark metadata records
//! `expected_verdict: false`, and z3 (spacer) answers `unsat` on each fixture
//! in under a second. The clausified variant is the one this solver's CHC-COMP
//! 2026 submission answered `sat` on (a trivial `(= C G)` "invariant" whose
//! safety obligation was never checked), while every other entrant answered
//! `unsat`. The top-level variant is the same program before the ITE
//! clausifier split its transitions.
//!
//! This is a different program from `chc_false_safe_barthe.rs`
//! (`eldarica-misc/LIA/llreve/barthe_unsafe.c-1`). Ported from the
//! pre-publication history (abc99805ef, 2026-05-16), which never reached the
//! published tree. The correct answer is `unsat`; `unknown` is the acceptable
//! interim answer; `sat` is the bug.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// Solver budget per run. The assertion is only "not `sat`", so a short budget
/// keeps the test cheap without weakening it.
const SOLVE_SECONDS: u32 = 15;

fn chc_verdict(fixture: &str) -> String {
    let bench = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_soundness/fixtures")
        .join(fixture);
    assert!(bench.exists(), "benchmark missing at {}", bench.display());
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--chc")
        .arg("--no-proof")
        .arg(format!("-T:{SOLVE_SECONDS}"))
        .arg(&bench)
        .output_timeout(Duration::from_secs(u64::from(SOLVE_SECONDS) + 30))
        .expect("failed to run ay");
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("")
        .to_string()
}

#[test]
#[timeout(90_000)]
fn ay_must_not_report_false_safe_on_clausified_faulty_barthe() {
    let verdict = chc_verdict("chc_faulty_barthe_000_clausified.smt2");
    assert_ne!(
        verdict, "sat",
        "false-SAFE soundness bug: ay reported SAFE (sat) on the unsafe clausified \
         faulty__barthe!_000; correct answer is unsat, acceptable interim is unknown"
    );
}

#[test]
#[timeout(90_000)]
fn ay_must_not_report_false_safe_on_top_level_faulty_barthe() {
    let verdict = chc_verdict("chc_faulty_barthe_000_top.smt2");
    assert_ne!(
        verdict, "sat",
        "false-SAFE soundness bug: ay reported SAFE (sat) on the unsafe top-level \
         faulty__barthe!_000; correct answer is unsat, acceptable interim is unknown"
    );
}
