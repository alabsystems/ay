// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression: ay must NOT report SAFE (`sat`) on an UNSAFE CHC.
//!
//! `barthe_unsafe.c-1` (eldarica-misc/LIA/llreve, `set-logic HORN`) is an
//! expected-UNSAT (unsafe) benchmark: both z3 (`fp.engine=spacer`) and golem
//! return `unsat`. ay was found returning `sat` with a ";; AY CHC Certificate:
//! SAFE" it did not soundly verify — a false-SAFE, the most serious class of
//! solver bug (a wrong "safe" on an unsafe program). Found 2026-06-05 via the
//! CHC-COMP LIA-Lin differential; see the development design notes.
//!
//! Correctness policy: never trade solver soundness for
//! speed; incomplete paths must prefer `unknown` over an unchecked sat/unsat"),
//! the correct answer is `unsat`, and the acceptable interim answer is
//! `unknown` — but never `sat`. This test asserts ay does not emit a false-SAFE.

use ntest::timeout;
use std::process::Command;

fn run_chc(rel: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let manifest_dir = env!("CARGO_MANIFEST_DIR"); // crates/ay
    let bench = std::path::Path::new(manifest_dir)
        .join("..")
        .join("..")
        .join(rel);
    assert!(bench.exists(), "benchmark missing at {}", bench.display());
    let output = Command::new(ay_path)
        .arg("--chc")
        .arg(&bench)
        .output()
        .expect("failed to run ay");
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("")
        .to_string()
}

#[test]
#[timeout(120000)]
fn ay_must_not_report_false_safe_on_unsafe_chc() {
    let result = run_chc("crates/ay/tests/group_soundness/fixtures/chc_false_safe_barthe.smt2");
    assert_ne!(
        result, "sat",
        "false-SAFE soundness bug: ay reported SAFE (sat) on the unsafe \
         barthe_unsafe.c-1 CHC; correct answer is unsat, acceptable interim is \
         unknown, never sat"
    );
}
