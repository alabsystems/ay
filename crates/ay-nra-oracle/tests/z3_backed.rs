// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end regression for the differential oracle, driven through the real
//! libz3.
//!
//! Everything here needs the reference dylib, so the whole file no-ops (with a
//! printed notice) on a machine that does not have it — the oracle is a
//! development tool, not a build dependency. Where the dylib IS present, this
//! keeps four properties standing:
//!
//!   1. `probe` — the z3 binding still behaves the way the checks assume
//!      (root isolation, sign evaluation, and the `psc_0 == Res` mapping).
//!   2. `golden` — z3's own transliterated tests still pass, live.
//!   3. `selftest` — every check still DETECTS a corrupted AY answer. Without
//!      this, a future refactor could quietly turn a check into a no-op and
//!      the campaign would keep reporting a clean run.
//!   4. `fuzz` — a short campaign still finds nothing.

use std::path::PathBuf;
use std::process::Command;

/// Resolve the reference libz3 the same way the oracle binary does:
/// `AY_NRA_ORACLE_Z3` wins, else `$HOME/ay/reference/z3/5.0.0/bin/libz3.dylib`.
///
/// This was an absolute path with a username baked into it, so the whole
/// z3-backed suite silently skipped on every machine but one — including this
/// one — and it leaked a personal home directory into the public snapshot.
fn z3_dylib() -> PathBuf {
    match std::env::var("AY_NRA_ORACLE_Z3") {
        Ok(path) if !path.is_empty() => PathBuf::from(path),
        _ => PathBuf::from(std::env::var("HOME").unwrap_or_default())
            .join("ay/reference/z3/5.0.0/bin/libz3.dylib"),
    }
}

fn oracle(args: &[&str]) -> Option<std::process::Output> {
    let dylib = z3_dylib();
    if !dylib.exists() {
        eprintln!(
            "skipping: reference libz3 not present at {}",
            dylib.display()
        );
        return None;
    }
    Some(
        Command::new(env!("CARGO_BIN_EXE_ay-nra-oracle"))
            .args(args)
            .output()
            .expect("oracle binary runs"),
    )
}

fn run_ok(args: &[&str]) {
    let Some(out) = oracle(args) else { return };
    assert!(
        out.status.success(),
        "`{}` failed ({:?})\n--- stdout ---\n{}\n--- stderr ---\n{}",
        args.join(" "),
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
}

#[test]
fn z3_binding_behaves_as_the_checks_assume() {
    run_ok(&["probe"]);
}

#[test]
fn transliterated_z3_golden_tests_pass_live() {
    run_ok(&["golden", "--heavy"]);
}

#[test]
fn every_check_detects_a_corrupted_ay_answer() {
    let args = ["selftest", "--seed", "11", "--cases", "1600"];
    let Some(out) = oracle(&args) else { return };
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "a check went blind — a clean campaign would prove nothing for it\n{stdout}"
    );
    assert!(
        !stdout.contains("BLIND") && !stdout.contains("NEVER RAN"),
        "{stdout}"
    );
}

#[test]
fn short_campaign_finds_no_divergence() {
    let args = [
        "fuzz",
        "--seed",
        "424242",
        "--cases",
        "1200",
        "--progress",
        "0",
    ];
    let Some(out) = oracle(&args) else { return };
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "the oracle reported a divergence:\n{stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(stdout.contains("DIVERGENCES          0"), "{stdout}");
}
