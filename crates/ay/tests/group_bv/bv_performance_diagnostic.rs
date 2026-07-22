// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BV performance-gap diagnostic harness (#8698 Phase 1).
//!
//! **Purpose:** this is *not* a pass/fail gate. It is a diagnostic harness
//! that runs ay on a small BV corpus known to exhibit the performance /
//! soundness-guard gaps documented in
//! the development design notes, and prints per-benchmark
//! wall-clock timings + ay's answer on every failure mode. The `assert!`
//! bound is deliberately generous (30 s per benchmark) so CI stays green
//! while regressions remain visible in stderr.
//!
//! **How to read a failure:** if this test ever panics, it means ay took
//! longer than 30 s on a benchmark that Z3 and Bitwuzla solve in <1 s, or it
//! returned `unsat`/`sat` on a benchmark whose expected answer is the
//! opposite (soundness violation — hard failure).
//!
//! **Success signal for Phase 2:** running this test with
//! `cargo test -p ay --test group_bv -- --nocapture` should show
//! `z3_7526 => unsat (wall_ms=...)` instead of the current
//! `z3_7526 => unknown (wall_ms=...)`.

use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use wait_timeout::ChildExt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expected {
    Sat,
    Unsat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error(String),
}

impl std::fmt::Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat => write!(f, "sat"),
            Self::Unsat => write!(f, "unsat"),
            Self::Unknown => write!(f, "unknown"),
            Self::Timeout => write!(f, "timeout"),
            Self::Error(e) => write!(f, "error({e})"),
        }
    }
}

struct Bench {
    rel_path: &'static str,
    expected: Expected,
    note: &'static str,
}

fn workspace_root() -> PathBuf {
    let manifest = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest)
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn has_phase1_design_doc(root: &Path) -> bool {
    root.join("the development design notes").exists()
}

fn run_ay(path: &Path, budget: Duration) -> (Outcome, Duration) {
    let ay = env!("CARGO_BIN_EXE_ay");
    let start = Instant::now();
    let mut child = match Command::new(ay)
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => return (Outcome::Error(format!("spawn: {e}")), start.elapsed()),
    };

    match child.wait_timeout(budget) {
        Ok(Some(_status)) => {
            let mut out = Vec::new();
            if let Some(mut s) = child.stdout.take() {
                let _ = s.read_to_end(&mut out);
            }
            let stdout = String::from_utf8_lossy(&out);
            let first = stdout.lines().next().unwrap_or("").trim();
            let elapsed = start.elapsed();
            let outcome = match first {
                "sat" => Outcome::Sat,
                "unsat" => Outcome::Unsat,
                "unknown" => Outcome::Unknown,
                other => Outcome::Error(format!("unexpected stdout: {other:?}")),
            };
            (outcome, elapsed)
        }
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            (Outcome::Timeout, budget)
        }
        Err(e) => (Outcome::Error(format!("wait: {e}")), start.elapsed()),
    }
}

fn run_ay_stdin(input: &str, budget: Duration) -> (Outcome, Duration) {
    let ay = env!("CARGO_BIN_EXE_ay");
    let start = Instant::now();
    let mut child = match Command::new(ay)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(error) => return (Outcome::Error(format!("spawn: {error}")), start.elapsed()),
    };
    if let Some(mut stdin) = child.stdin.take() {
        if let Err(error) = stdin.write_all(input.as_bytes()) {
            let _ = child.kill();
            let _ = child.wait();
            return (Outcome::Error(format!("stdin: {error}")), start.elapsed());
        }
    }

    match child.wait_timeout(budget) {
        Ok(Some(_status)) => {
            let mut out = Vec::new();
            if let Some(mut stdout) = child.stdout.take() {
                let _ = stdout.read_to_end(&mut out);
            }
            let stdout = String::from_utf8_lossy(&out);
            let outcome = match stdout.lines().next().unwrap_or("").trim() {
                "sat" => Outcome::Sat,
                "unsat" => Outcome::Unsat,
                "unknown" => Outcome::Unknown,
                other => Outcome::Error(format!("unexpected stdout: {other:?}")),
            };
            (outcome, start.elapsed())
        }
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            (Outcome::Timeout, budget)
        }
        Err(error) => (Outcome::Error(format!("wait: {error}")), start.elapsed()),
    }
}

/// Regression for the ExternalCodegen Faulhaber identity that previously spent over a
/// minute bit-blasting each 64-bit multiply by 2/3/4/5 as a generic multiplier.
#[test]
fn external_codegen_faulhaber_small_constant_multipliers() {
    let input = r#"(set-logic QF_BV)
(set-option :timeout 5000)
(declare-const acc (_ BitVec 64))
(declare-const a2 (_ BitVec 64))
(declare-const a1 (_ BitVec 64))
(declare-const a0 (_ BitVec 64))
(assert (not (= (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (bvmul (_ bv2 64) a1) (bvmul (_ bv4 64) a2)) a0) a0) a0) a1) a2) acc) (bvadd (bvadd (bvadd (bvmul (_ bv3 64) a0) (bvmul (_ bv3 64) a1)) (bvmul (_ bv5 64) a2)) acc))))
(check-sat)
(exit)
"#;
    let (outcome, elapsed) = run_ay_stdin(input, Duration::from_secs(5));
    assert_eq!(
        outcome,
        Outcome::Unsat,
        "ExternalCodegen Faulhaber regression did not close in {:?}",
        elapsed
    );
}

fn benches() -> Vec<Bench> {
    vec![
        Bench {
            rel_path: "benchmarks/smt/z3-perf-cliffs/z3_7038.smt2",
            expected: Expected::Sat,
            note: "wide mul SAT (BV-perf-cliff)",
        },
        Bench {
            rel_path: "benchmarks/smt/z3-perf-cliffs/z3_7526.smt2",
            expected: Expected::Unsat,
            note: "mul-overflow UNSAT; currently returns unknown via #8373 fallback",
        },
        Bench {
            rel_path: "benchmarks/smt/QF_ABV/wide_div_array_sat.smt2",
            expected: Expected::Sat,
            note: "wide UDIV in array; ~1.8x slower than bitwuzla",
        },
    ]
}

/// Diagnostic harness — reports wall-clock timings and answers for a small
/// BV corpus. Hard-fails only on:
///   (a) wall time > 30 s (indicates a real regression or hang), or
///   (b) definite wrong answer (soundness violation — sat vs unsat).
/// "Unknown" is tolerated for now (z3_7526 returns unknown today — see
/// the development design notes).
#[test]
fn bv_phase1_diagnostic() {
    let root = workspace_root();
    // The publish snapshot omits repo-local design docs. In that environment
    // this harness should not run, because it is a source-tree diagnostic tied
    // to the Phase 1 design packet rather than a portable crate contract.
    if !has_phase1_design_doc(&root) {
        eprintln!("skipping bv_phase1_diagnostic outside full source checkout");
        return;
    }
    let budget = Duration::from_secs(30);
    let mut rows: Vec<(String, String, u128, &'static str)> = Vec::new();
    let mut soundness_bugs: Vec<String> = Vec::new();

    for b in benches() {
        let path = root.join(b.rel_path);
        assert!(path.exists(), "missing benchmark: {}", path.display());

        let (outcome, wall) = run_ay(&path, budget);
        let wall_ms = wall.as_millis();

        // Hard failure on wrong definite answer.
        let is_soundness = matches!(
            (b.expected, &outcome),
            (Expected::Sat, Outcome::Unsat) | (Expected::Unsat, Outcome::Sat)
        );
        if is_soundness {
            soundness_bugs.push(format!(
                "  SOUNDNESS BUG: {} expected {:?}, got {}",
                b.rel_path, b.expected, outcome
            ));
        }

        rows.push((b.rel_path.to_string(), outcome.to_string(), wall_ms, b.note));
    }

    // Always print the diagnostic table to stderr so `cargo test -- --nocapture`
    // surfaces it; also printed on assertion failure.
    eprintln!();
    eprintln!("==== BV Phase 1 diagnostic (issue #8698) ====");
    eprintln!(
        "  {:<60} {:<10} {:>8}  note",
        "benchmark", "answer", "wall_ms"
    );
    for (bench, ans, ms, note) in &rows {
        eprintln!("  {bench:<60} {ans:<10} {ms:>6}ms  {note}");
    }
    eprintln!("=============================================");

    // Hard fail: soundness violations.
    assert!(
        soundness_bugs.is_empty(),
        "BV soundness violations:\n{}",
        soundness_bugs.join("\n")
    );

    // Hard fail: any row over 30 s.
    for (bench, _, ms, _) in &rows {
        assert!(
            *ms < 30_000,
            "BV diagnostic regression: {bench} took {ms}ms (> 30s budget)"
        );
    }
}
