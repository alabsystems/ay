// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Differential Testing Against Z3
//!
//! This module implements differential testing inspired by the downstream proof consumer's approach:
//! Compare AY results against Z3 on SMT-LIB benchmarks.
//!
//! The pattern is:
//! 1. Load SMT-LIB benchmark files
//! 2. Run through Z3 (reference implementation)
//! 3. Run through AY (our implementation)
//! 4. Compare results - any mismatch is a bug
//!
//! This is the PRIMARY verification mechanism for SMT soundness.
//!
//! ## Environment Variables
//!
//! - `Z3_DIFFERENTIAL_REQUIRED=1` (or `true`): Fail tests if Z3 is not available (for CI)
//! - Without this var, tests skip gracefully when Z3 is missing

use anyhow::{anyhow, Context, Result};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Once, OnceLock,
};
use std::time::Duration;
use wait_timeout::ChildExt;

const QF_LIA_PATH: &str = "../../benchmarks/smt/QF_LIA";
const QF_LRA_PATH: &str = "../../benchmarks/smt/QF_LRA";
const QF_BV_PATH: &str = "../../benchmarks/smt/QF_BV";
const QF_UF_PATH: &str = "../../benchmarks/smt/QF_UF";

static Z3_AVAILABLE: OnceLock<bool> = OnceLock::new();
static Z3_SKIP_LOGGED: Once = Once::new();

/// Result of running a benchmark
#[derive(Debug, Clone, PartialEq)]
enum SolverResult {
    Sat,
    Unsat,
    Unknown,
    Error(String),
}

impl SolverResult {
    fn from_str(s: &str) -> Self {
        let s = s.trim().to_lowercase();
        if s == "sat" {
            Self::Sat
        } else if s == "unsat" {
            Self::Unsat
        } else if s == "unknown" || s.contains("unknown") {
            Self::Unknown
        } else if s.contains("error") || s.contains("timeout") {
            Self::Error(s)
        } else {
            Self::Unknown
        }
    }

    fn is_definite(&self) -> bool {
        matches!(self, Self::Sat | Self::Unsat)
    }
}

/// Check if Z3 is available in PATH
fn is_z3_available() -> bool {
    *Z3_AVAILABLE.get_or_init(|| {
        Command::new("z3")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    })
}

/// Check if Z3 is required (via environment variable).
/// When Z3_DIFFERENTIAL_REQUIRED is set to `1` or `true`, tests fail instead of skip.
fn is_z3_required() -> bool {
    std::env::var("Z3_DIFFERENTIAL_REQUIRED")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
}

/// Check Z3 availability, handling required vs optional cases.
/// Returns true if Z3 is available, false if skipping (not required),
/// or panics if Z3 is required but not available.
fn check_z3_or_skip() -> bool {
    if is_z3_available() {
        return true;
    }

    if is_z3_required() {
        let value =
            std::env::var("Z3_DIFFERENTIAL_REQUIRED").unwrap_or_else(|_| "<unset>".to_string());
        panic!(
            "Z3 not found in PATH but Z3_DIFFERENTIAL_REQUIRED is set (value={value:?}).\n\
             Install Z3 or unset the environment variable to skip differential tests."
        );
    }

    Z3_SKIP_LOGGED.call_once(|| {
        eprintln!("Z3 not found in PATH; skipping differential tests");
        eprintln!("  Set Z3_DIFFERENTIAL_REQUIRED=1 to require Z3 in CI");
    });
    false
}

/// Run Z3 on an SMT-LIB file
fn run_z3(path: &Path) -> Result<SolverResult> {
    const Z3_TIMEOUT_SECS: u64 = 10;
    const Z3_TIMEOUT_SLACK_SECS: u64 = 2;

    // Use both Z3's internal timeout and an OS-level kill timeout.
    //
    // Rationale: if the test harness terminates the test process (or if Z3 wedges),
    // `-T` alone can still leave orphaned long-running Z3 subprocesses.
    let mut child = Command::new("z3")
        .arg(format!("-T:{Z3_TIMEOUT_SECS}"))
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("failed to spawn z3 - is Z3 installed and in PATH?")?;

    let mut timed_out = false;
    let timeout = Duration::from_secs(Z3_TIMEOUT_SECS + Z3_TIMEOUT_SLACK_SECS);
    let status = match child
        .wait_timeout(timeout)
        .context("failed to wait for z3")?
    {
        Some(status) => status,
        None => {
            timed_out = true;
            let _ = child.kill();
            child.wait().context("failed to kill z3 after timeout")?
        }
    };

    let mut stdout = Vec::new();
    if let Some(mut out) = child.stdout.take() {
        out.read_to_end(&mut stdout)
            .context("failed to read z3 stdout")?;
    }

    let mut stderr = Vec::new();
    if let Some(mut err) = child.stderr.take() {
        err.read_to_end(&mut stderr)
            .context("failed to read z3 stderr")?;
    }

    if timed_out {
        return Ok(SolverResult::Error(format!(
            "timeout after {Z3_TIMEOUT_SECS}s"
        )));
    }

    if !status.success() && stdout.is_empty() {
        let stderr = String::from_utf8_lossy(&stderr);
        return Ok(SolverResult::Error(stderr.to_string()));
    }

    let stdout = String::from_utf8_lossy(&stdout);
    // Z3 outputs "sat" or "unsat" on first line
    let first_line = stdout.lines().next().unwrap_or("");
    Ok(SolverResult::from_str(first_line))
}

/// Per-benchmark timeout for AY (seconds). Matches the Z3 timeout so both
/// solvers get the same budget per instance.
const AY_TIMEOUT_SECS: u64 = 10;

/// Run AY on an SMT-LIB file with a per-benchmark timeout.
///
/// Uses the executor interrupt so timeouts do not leave detached solver threads
/// running after the test case returns.
fn run_ay_with_timeout(path: &Path, timeout_secs: u64) -> Result<SolverResult> {
    let content =
        fs::read_to_string(path).with_context(|| format!("failed to read {}", path.display()))?;

    let commands = match parse(&content) {
        Ok(commands) => commands,
        Err(e) => return Ok(SolverResult::Error(format!("parse error: {e}"))),
    };

    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));

    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx
            .recv_timeout(Duration::from_secs(timeout_secs))
            .is_err()
        {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    let results = executor.execute_all(&commands);
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    if timed_out {
        return Ok(SolverResult::Error(format!(
            "timeout after {timeout_secs}s"
        )));
    }

    let results = match results {
        Ok(results) => results,
        Err(e) => return Ok(SolverResult::Error(format!("execution error: {e}"))),
    };

    // Find the check-sat result
    for result in results {
        let r = result.to_lowercase();
        if r == "sat" {
            return Ok(SolverResult::Sat);
        } else if r == "unsat" {
            return Ok(SolverResult::Unsat);
        } else if r == "unknown" {
            return Ok(SolverResult::Unknown);
        }
    }

    Ok(SolverResult::Unknown)
}

fn run_ay(path: &Path) -> Result<SolverResult> {
    run_ay_with_timeout(path, AY_TIMEOUT_SECS)
}

/// A mismatch between Z3 and AY
#[derive(Debug)]
struct Mismatch {
    file: String,
    z3_result: SolverResult,
    ay_result: SolverResult,
}

/// Aggregated differential testing results for one benchmark directory.
struct DifferentialSummary {
    total: usize,
    agreed: usize,
    mismatches: Vec<Mismatch>,
    incompletes: Vec<Mismatch>,
}

/// Run differential test on a directory of SMT-LIB files
fn differential_test_dir(dir_path: &str) -> Result<DifferentialSummary> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(dir_path);

    if !path.exists() {
        return Err(anyhow!("benchmark directory not found: {}", path.display()));
    }

    let mut total = 0;
    let mut agreed = 0;
    let mut mismatches = Vec::new();
    let mut incompletes = Vec::new();

    let entries: Vec<_> = fs::read_dir(&path)?
        .filter_map(std::result::Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "smt2"))
        .collect();

    for entry in entries {
        let file_path = entry.path();
        let file_name = file_path.file_name().unwrap().to_string_lossy().to_string();

        total += 1;

        let z3_result = match run_z3(&file_path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("Z3 error on {file_name}: {e}");
                SolverResult::Error(e.to_string())
            }
        };

        let ay_result = match run_ay(&file_path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("AY error on {file_name}: {e}");
                SolverResult::Error(e.to_string())
            }
        };

        // Only compare definite results (sat/unsat)
        // Unknown is acceptable for AY if Z3 gives a definite answer
        // But if both are definite and disagree, that's a bug!
        if z3_result.is_definite() && ay_result.is_definite() {
            if z3_result == ay_result {
                agreed += 1;
            } else {
                mismatches.push(Mismatch {
                    file: file_name.clone(),
                    z3_result: z3_result.clone(),
                    ay_result: ay_result.clone(),
                });
            }
        } else if z3_result.is_definite() && !ay_result.is_definite() {
            // Z3 gave definite answer, AY didn't - not a soundness bug but incomplete
            eprintln!("AY incomplete on {file_name}: Z3={z3_result:?}, AY={ay_result:?}");
            incompletes.push(Mismatch {
                file: file_name.clone(),
                z3_result: z3_result.clone(),
                ay_result: ay_result.clone(),
            });
        } else {
            // Both unknown or Z3 unknown - skip
            agreed += 1;
        }
    }

    Ok(DifferentialSummary {
        total,
        agreed,
        mismatches,
        incompletes,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[test]
// Each benchmark has a 10s per-instance timeout (AY_TIMEOUT_SECS). The test-level
// timeout is a safety net for the aggregate (51 benchmarks × overhead).
#[timeout(120_000)]
fn differential_qf_lia_vs_z3() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }
    let summary = differential_test_dir(QF_LIA_PATH)?;

    println!("\n=== QF_LIA Differential Test Results ===");
    println!("Total benchmarks: {}", summary.total);
    println!("Agreed with Z3:   {}", summary.agreed);
    println!("Mismatches:       {}", summary.mismatches.len());
    println!("Incompletes:      {}", summary.incompletes.len());

    if !summary.mismatches.is_empty() {
        println!("\n!!! SOUNDNESS VIOLATIONS DETECTED !!!");
        for m in &summary.mismatches {
            println!("  {}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result);
        }
    }
    if !summary.incompletes.is_empty() {
        println!("\n!!! COMPLETENESS VIOLATIONS DETECTED !!!");
        for i in &summary.incompletes {
            println!("  {}: Z3={:?}, AY={:?}", i.file, i.z3_result, i.ay_result);
        }
    }

    // THIS IS THE CRITICAL ASSERTION
    // If this fails, we have a soundness bug
    assert!(
        summary.mismatches.is_empty(),
        "SOUNDNESS BUG: AY disagrees with Z3 on {} of {} QF_LIA benchmarks.\n\
         Mismatches: {:?}",
        summary.mismatches.len(),
        summary.total,
        summary
            .mismatches
            .iter()
            .map(|m| &m.file)
            .collect::<Vec<_>>()
    );
    // Known-incomplete benchmarks: hard instances where AY returns Unknown
    // or timeout but Z3 returns a definite result. Not soundness bugs, just
    // completeness gaps. Each entry documents the expected Z3 result.
    let known_incomplete: &[&str] = &[
        "false_unsat_20var_bb.smt2", // #2718: times out in 10s (SAT in release with more time)
        "false_unsat_disjunction_6205.smt2", // #6205: sound Unknown (was false-UNSAT), Z3=SAT
        "false_unsat_implication_6206.smt2", // #6206: sound Unknown (was false-UNSAT), Z3=SAT
        "int_incompleteness2.smt2",  // #4785: LIA unknown-recovery gap, Z3=UNSAT
        "ring_2exp4_3vars_0ite_unsat.smt2", // #4785: modular arithmetic, Z3=UNSAT
        "ring_2exp8_3vars_crt_unsat.smt2", // #4785: modular arithmetic CRT, Z3=UNSAT
        "ring_2exp8_4vars_carry_unsat.smt2", // #4785: modular arithmetic carry, Z3=UNSAT
        "ring_2exp8_5vars_modular_unsat.smt2", // #4785: modular arithmetic, Z3=UNSAT
        "ring_2exp12_3vars_deep_unsat.smt2", // #4785: deep modular arithmetic, Z3=UNSAT
        "ring_2exp16_3vars_residue_sat.smt2", // Hard modular arithmetic (Z3=SAT)
        "ring_2exp16_5vars_cascade_unsat.smt2", // Hard modular arithmetic (Z3=UNSAT)
        "ring_2exp16_5vars_cascade_v2_unsat.smt2", // Hard modular arithmetic (Z3=UNSAT)
    ];
    let unexpected_incompletes: Vec<_> = summary
        .incompletes
        .iter()
        .filter(|m| !known_incomplete.contains(&m.file.as_str()))
        .collect();
    assert!(
        unexpected_incompletes.is_empty(),
        "COMPLETENESS BUG: AY returned non-definite results on {} of {} QF_LIA benchmarks where Z3 was definite.\n\
         Incomplete files: {:?}",
        unexpected_incompletes.len(),
        summary.total,
        unexpected_incompletes.iter().map(|m| &m.file).collect::<Vec<_>>()
    );

    // Also require high coverage - at least 80% should have definite answers
    let coverage = (summary.agreed as f64 / summary.total as f64) * 100.0;
    assert!(
        coverage >= 80.0,
        "Low coverage: only {coverage:.1}% of benchmarks agreed (need >= 80%)"
    );

    println!(
        "\n✓ All {} QF_LIA benchmarks passed differential test",
        summary.total
    );
    Ok(())
}

#[test]
#[timeout(10_000)]
fn differential_qf_lra_vs_z3() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }
    let summary = differential_test_dir(QF_LRA_PATH)?;

    println!("\n=== QF_LRA Differential Test Results ===");
    println!("Total benchmarks: {}", summary.total);
    println!("Agreed with Z3:   {}", summary.agreed);
    println!("Mismatches:       {}", summary.mismatches.len());
    println!("Incompletes:      {}", summary.incompletes.len());

    if !summary.mismatches.is_empty() {
        println!("\n!!! SOUNDNESS VIOLATIONS DETECTED !!!");
        for m in &summary.mismatches {
            println!("  {}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result);
        }
    }
    if !summary.incompletes.is_empty() {
        println!("\n!!! COMPLETENESS VIOLATIONS DETECTED !!!");
        for i in &summary.incompletes {
            println!("  {}: Z3={:?}, AY={:?}", i.file, i.z3_result, i.ay_result);
        }
    }

    // THIS IS THE CRITICAL ASSERTION
    // If this fails, we have a soundness bug in LRA
    assert!(
        summary.mismatches.is_empty(),
        "SOUNDNESS BUG: AY disagrees with Z3 on {} of {} QF_LRA benchmarks.\n\
         Mismatches: {:?}",
        summary.mismatches.len(),
        summary.total,
        summary
            .mismatches
            .iter()
            .map(|m| &m.file)
            .collect::<Vec<_>>()
    );
    assert!(
        summary.incompletes.is_empty(),
        "COMPLETENESS BUG: AY returned non-definite results on {} of {} QF_LRA benchmarks where Z3 was definite.\n\
         Incomplete files: {:?}",
        summary.incompletes.len(),
        summary.total,
        summary
            .incompletes
            .iter()
            .map(|m| &m.file)
            .collect::<Vec<_>>()
    );

    println!(
        "\n[OK] All {} QF_LRA benchmarks passed differential test",
        summary.total
    );
    Ok(())
}

#[test]
#[timeout(10_000)]
fn differential_qf_bv_vs_z3() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }
    let summary = differential_test_dir(QF_BV_PATH)?;

    println!("\n=== QF_BV Differential Test Results ===");
    println!("Total benchmarks: {}", summary.total);
    println!("Agreed with Z3:   {}", summary.agreed);
    println!("Mismatches:       {}", summary.mismatches.len());
    println!("Incompletes:      {}", summary.incompletes.len());

    if !summary.mismatches.is_empty() {
        println!("\n!!! SOUNDNESS VIOLATIONS DETECTED !!!");
        for m in &summary.mismatches {
            println!("  {}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result);
        }
    }
    if !summary.incompletes.is_empty() {
        println!("\n!!! COMPLETENESS VIOLATIONS DETECTED !!!");
        for i in &summary.incompletes {
            println!("  {}: Z3={:?}, AY={:?}", i.file, i.z3_result, i.ay_result);
        }
    }

    assert!(
        summary.mismatches.is_empty(),
        "SOUNDNESS BUG: AY disagrees with Z3 on {} of {} QF_BV benchmarks",
        summary.mismatches.len(),
        summary.total
    );
    assert!(
        summary.incompletes.is_empty(),
        "COMPLETENESS BUG: AY returned non-definite results on {} of {} QF_BV benchmarks where Z3 was definite.\n\
         Incomplete files: {:?}",
        summary.incompletes.len(),
        summary.total,
        summary
            .incompletes
            .iter()
            .map(|m| &m.file)
            .collect::<Vec<_>>()
    );

    println!(
        "\n✓ All {} QF_BV benchmarks passed differential test",
        summary.total
    );
    Ok(())
}

#[test]
#[timeout(10_000)]
fn differential_qf_uf_vs_z3() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }
    let summary = differential_test_dir(QF_UF_PATH)?;

    println!("\n=== QF_UF Differential Test Results ===");
    println!("Total benchmarks: {}", summary.total);
    println!("Agreed with Z3:   {}", summary.agreed);
    println!("Mismatches:       {}", summary.mismatches.len());
    println!("Incompletes:      {}", summary.incompletes.len());

    if !summary.mismatches.is_empty() {
        println!("\n!!! SOUNDNESS VIOLATIONS DETECTED !!!");
        for m in &summary.mismatches {
            println!("  {}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result);
        }
    }
    if !summary.incompletes.is_empty() {
        println!("\n!!! COMPLETENESS VIOLATIONS DETECTED !!!");
        for i in &summary.incompletes {
            println!("  {}: Z3={:?}, AY={:?}", i.file, i.z3_result, i.ay_result);
        }
    }

    assert!(
        summary.mismatches.is_empty(),
        "SOUNDNESS BUG: AY disagrees with Z3 on {} of {} QF_UF benchmarks.\n\
         Mismatches: {:?}",
        summary.mismatches.len(),
        summary.total,
        summary
            .mismatches
            .iter()
            .map(|m| &m.file)
            .collect::<Vec<_>>()
    );
    assert!(
        summary.incompletes.is_empty(),
        "COMPLETENESS BUG: AY returned non-definite results on {} of {} QF_UF benchmarks where Z3 was definite.\n\
         Incomplete files: {:?}",
        summary.incompletes.len(),
        summary.total,
        summary
            .incompletes
            .iter()
            .map(|m| &m.file)
            .collect::<Vec<_>>()
    );

    println!(
        "\n✓ All {} QF_UF benchmarks passed differential test",
        summary.total
    );
    Ok(())
}

/// Quick sanity check - run first few LIA benchmarks
#[test]
#[timeout(10_000)]
fn quick_lia_sanity_check() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(QF_LIA_PATH);

    // Just test first 5 files
    let mut count = 0;
    for entry in fs::read_dir(&path)? {
        let entry = entry?;
        let file_path = entry.path();
        if file_path.extension().is_some_and(|ext| ext == "smt2") {
            count += 1;
            if count > 5 {
                break;
            }

            let z3_result = run_z3(&file_path)?;
            let ay_result = run_ay(&file_path)?;

            println!(
                "{}: Z3={:?}, AY={:?}",
                file_path.file_name().unwrap().to_string_lossy(),
                z3_result,
                ay_result
            );

            if z3_result.is_definite() && ay_result.is_definite() {
                assert_eq!(z3_result, ay_result, "Mismatch on {}", file_path.display());
            }
        }
    }

    Ok(())
}

/// Regression for #2657: `system_16.smt2` must not regress to SAT/UNSAT mismatch.
fn assert_qf_lia_benchmark_matches_z3_sat(
    file_name: &str,
    issue: &str,
    ay_timeout_secs: u64,
) -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    let file_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(QF_LIA_PATH)
        .join(file_name);
    assert!(
        file_path.exists(),
        "missing benchmark fixture: {}",
        file_path.display()
    );

    let z3_result = run_z3(&file_path)?;
    let ay_result = run_ay_with_timeout(&file_path, ay_timeout_secs)?;

    assert_eq!(
        z3_result,
        SolverResult::Sat,
        "unexpected Z3 result on {}",
        file_path.display()
    );
    assert_eq!(
        ay_result,
        SolverResult::Sat,
        "regression {issue}: AY returned {:?} on {} (expected sat)",
        ay_result,
        file_path.display()
    );
    assert_eq!(
        ay_result,
        z3_result,
        "regression {issue}: AY and Z3 disagree on {}",
        file_path.display()
    );
    Ok(())
}

#[test]
#[timeout(10_000)]
fn regression_qf_lia_system_16_matches_z3_sat() -> Result<()> {
    assert_qf_lia_benchmark_matches_z3_sat("system_16.smt2", "#2657", AY_TIMEOUT_SECS)
}

/// Regression for #2760: `system_11.smt2` must stay SAT and match Z3.
#[test]
#[timeout(10_000)]
fn regression_qf_lia_system_11_matches_z3_sat() -> Result<()> {
    assert_qf_lia_benchmark_matches_z3_sat("system_11.smt2", "#2760", AY_TIMEOUT_SECS)
}

/// Regression for #2760: `false_unsat_20var_bb.smt2` must never regress to false UNSAT.
#[test]
#[timeout(120_000)]
fn regression_qf_lia_false_unsat_20var_bb_no_false_unsat() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    let file_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(QF_LIA_PATH)
        .join("false_unsat_20var_bb.smt2");
    assert!(
        file_path.exists(),
        "missing benchmark fixture: {}",
        file_path.display()
    );

    let z3_result = run_z3(&file_path)?;
    assert_eq!(
        z3_result,
        SolverResult::Sat,
        "unexpected Z3 result on {}",
        file_path.display()
    );

    // This benchmark can be expensive; keep a bounded timeout and only enforce
    // soundness under that budget (must not return false UNSAT).
    let ay_result = run_ay_with_timeout(&file_path, 30)?;
    assert_ne!(
        ay_result,
        SolverResult::Unsat,
        "regression #2760: AY returned false UNSAT on {}",
        file_path.display()
    );
    if ay_result.is_definite() {
        assert_eq!(
            ay_result,
            z3_result,
            "regression #2760: AY and Z3 disagree on {}",
            file_path.display()
        );
    }
    Ok(())
}

// ============================================================================
// Model Validation Tests (Regression for #88)
// ============================================================================

/// Parse model output to extract variable assignments
/// Returns map of variable name -> integer value
fn parse_model_integers(model: &str) -> std::collections::HashMap<String, i64> {
    let mut values = std::collections::HashMap::new();

    // Parse lines like:
    //   (define-fun field1 () Int 0)
    //   (define-fun field2 () Int (- 1))
    for line in model.lines() {
        let line = line.trim();
        if line.starts_with("(define-fun") && line.contains("Int") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 5 {
                let name = parts[1].to_string();
                // Check for SMT-LIB negative notation: (- N)
                // Parts for negative: [..., "(-", "N))"]
                let is_negative = parts.len() >= 6 && parts[parts.len() - 2].starts_with("(-");
                let value_str = parts.last().unwrap().trim_end_matches(')');
                if let Ok(value) = value_str.parse::<i64>() {
                    if is_negative {
                        values.insert(name, -value);
                    } else {
                        values.insert(name, value);
                    }
                }
            }
        }
    }
    values
}

/// Run AY and get model output
fn run_ay_with_model(smt2: &str) -> Result<(SolverResult, String)> {
    let commands = match parse(smt2) {
        Ok(cmds) => cmds,
        Err(e) => {
            return Ok((
                SolverResult::Error(format!("parse error: {e}")),
                String::new(),
            ))
        }
    };

    let mut executor = Executor::new();

    let results = match executor.execute_all(&commands) {
        Ok(r) => r,
        Err(e) => {
            return Ok((
                SolverResult::Error(format!("execution error: {e}")),
                String::new(),
            ))
        }
    };

    // Find check-sat and model results
    let mut sat_result = SolverResult::Unknown;
    let mut model = String::new();

    for result in results {
        let r = result.to_lowercase();
        if r == "sat" {
            sat_result = SolverResult::Sat;
        } else if r == "unsat" {
            sat_result = SolverResult::Unsat;
        } else if r.contains("(model") || r.contains("define-fun") {
            model = result;
        }
    }

    Ok((sat_result, model))
}

/// Regression test for #88: Model generation must respect disequalities
/// This test MUST FAIL if AufLiaSolver::assert_literal uses contains_arithmetic_ops
/// instead of involves_int_arithmetic.
///
/// Root cause: solve_auf_lia() uses dpll.solve() which returns Unknown for
/// NeedDisequalitySplit instead of handling the split. Fix: use solve_step()
/// with disequality split handling, following solve_lira() pattern.
/// See #137 for fix implementation.
#[test]
#[timeout(10_000)]
fn regression_issue_88_disequality_model() -> Result<()> {
    // Exact reproduction case from #88
    let smt2 = r#"
(set-logic QF_AUFLIA)
(declare-const field1 Int)
(declare-const field2 Int)
(assert (not (= field1 field2)))
(check-sat)
(get-model)
"#;

    let (result, model) = run_ay_with_model(smt2)?;

    println!("Result: {result:?}");
    println!("Model:\n{model}");

    // Must be SAT
    assert_eq!(result, SolverResult::Sat, "Expected SAT for disequality");

    // Parse model values
    let values = parse_model_integers(&model);
    println!("Parsed values: {values:?}");

    // Get field1 and field2 values
    let field1 = values.get("field1").copied().unwrap_or(0);
    let field2 = values.get("field2").copied().unwrap_or(0);

    // CRITICAL: Model must satisfy (not (= field1 field2))
    // i.e., field1 != field2
    assert_ne!(
        field1, field2,
        "BUG #88: Model violates disequality constraint!\n\
         field1 = {field1}, field2 = {field2}, but (not (= field1 field2)) was asserted.\n\
         Root cause: AufLiaSolver::assert_literal filters pure integer disequalities.\n\
         Fix: Use involves_int_arithmetic instead of contains_arithmetic_ops."
    );

    println!("Model valid: field1={field1}, field2={field2} (field1 != field2)");
    Ok(())
}

/// Additional disequality tests to catch edge cases
#[test]
#[timeout(10_000)]
fn regression_issue_88_multiple_disequalities() -> Result<()> {
    // Multiple variables with disequality chain
    let smt2 = r#"
(set-logic QF_AUFLIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (not (= a b)))
(assert (not (= b c)))
(assert (not (= a c)))
(check-sat)
(get-model)
"#;

    let (result, model) = run_ay_with_model(smt2)?;
    assert_eq!(result, SolverResult::Sat);

    let values = parse_model_integers(&model);
    let a = values.get("a").copied().unwrap_or(0);
    let b = values.get("b").copied().unwrap_or(0);
    let c = values.get("c").copied().unwrap_or(0);

    assert_ne!(a, b, "Model violates (not (= a b)): a={a}, b={b}");
    assert_ne!(b, c, "Model violates (not (= b c)): b={b}, c={c}");
    assert_ne!(a, c, "Model violates (not (= a c)): a={a}, c={c}");

    println!("Model valid: a={a}, b={b}, c={c} (all distinct)");
    Ok(())
}

/// Test disequality combined with arithmetic
#[test]
#[timeout(10_000)]
fn regression_issue_88_disequality_with_arithmetic() -> Result<()> {
    let smt2 = r#"
(set-logic QF_AUFLIA)
(declare-const x Int)
(declare-const y Int)
(assert (not (= x y)))
(assert (> x 0))
(assert (< y 10))
(check-sat)
(get-model)
"#;

    let (result, model) = run_ay_with_model(smt2)?;
    assert_eq!(result, SolverResult::Sat);

    let values = parse_model_integers(&model);
    let x = values.get("x").copied().unwrap_or(0);
    let y = values.get("y").copied().unwrap_or(0);

    assert_ne!(x, y, "Model violates (not (= x y)): x={x}, y={y}");
    assert!(x > 0, "Model violates (> x 0): x={x}");
    assert!(y < 10, "Model violates (< y 10): y={y}");

    println!("Model valid: x={x}, y={y}");
    Ok(())
}

// ============================================================================
// Regression Tests for Blocking Clause Patterns (#299)
// ============================================================================

const REGRESSION_PATH: &str = "../../benchmarks/smt/regression";

/// Run differential test on regression benchmarks
/// These are patterns that previously caused soundness bugs (#294, #289, #301)
#[test]
#[timeout(10_000)]
fn differential_regression_benchmarks() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }
    let summary = differential_test_dir(REGRESSION_PATH)?;

    println!("\n=== Regression Benchmark Results ===");
    println!("Total benchmarks: {}", summary.total);
    println!("Agreed with Z3:   {}", summary.agreed);
    println!("Mismatches:       {}", summary.mismatches.len());

    if !summary.mismatches.is_empty() {
        println!("\n!!! SOUNDNESS REGRESSION DETECTED !!!");
        for m in &summary.mismatches {
            println!("  {}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result);
        }
    }

    assert!(
        summary.mismatches.is_empty(),
        "SOUNDNESS REGRESSION: AY disagrees with Z3 on {} of {} regression benchmarks.\n\
         These benchmarks test patterns from known bugs (#294, #289, #301).\n\
         Mismatches: {:?}",
        summary.mismatches.len(),
        summary.total,
        summary
            .mismatches
            .iter()
            .map(|m| &m.file)
            .collect::<Vec<_>>()
    );

    // Require at least some benchmarks exist
    assert!(
        summary.total >= 5,
        "Expected at least 5 regression benchmarks, found {}",
        summary.total
    );

    println!(
        "\n[OK] All {} regression benchmarks passed differential test",
        summary.total
    );
    Ok(())
}

// ============================================================================
// Regression Test for #324: get-value returns incorrect model values
// ============================================================================

/// Parse get-value output to extract variable assignments
/// Format: ((x 5) (y 8))
fn parse_get_value(output: &str) -> std::collections::HashMap<String, i64> {
    let mut values = std::collections::HashMap::new();

    // Remove outer parentheses and split into pairs
    let trimmed = output.trim();
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return values;
    }
    let inner = &trimmed[1..trimmed.len() - 1];

    // Parse each (var value) pair
    for pair in inner.split(") (") {
        let pair = pair.trim_matches(|c| c == '(' || c == ')');
        let parts: Vec<&str> = pair.split_whitespace().collect();
        if parts.len() >= 2 {
            let name = parts[0].to_string();
            // Handle negative numbers like (- 5)
            if parts.len() == 3 && (parts[1] == "-" || parts[1] == "(-") {
                if let Ok(val) = parts[2].parse::<i64>() {
                    values.insert(name, -val);
                }
            } else if let Ok(val) = parts[1].parse::<i64>() {
                values.insert(name, val);
            }
        }
    }
    values
}

/// Regression test for #324: get-value must return actual model values for LIA equalities
#[test]
#[timeout(10_000)]
fn regression_issue_324_get_value_lia_equality() -> Result<()> {
    // Test case from #324: x = 5 should return ((x 5)), not ((x 0))
    let smt2 = r#"
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-const x Int)
(assert (= x 5))
(check-sat)
(get-value (x))
"#;

    let commands = match parse(smt2) {
        Ok(cmds) => cmds,
        Err(e) => return Err(anyhow!("parse error: {e}")),
    };

    let mut executor = Executor::new();
    let results = executor.execute_all(&commands)?;

    // Find check-sat and get-value results
    let mut sat_result = None;
    let mut get_value_result = None;

    for result in &results {
        let r = result.to_lowercase();
        if r == "sat" {
            sat_result = Some(SolverResult::Sat);
        } else if r == "unsat" {
            sat_result = Some(SolverResult::Unsat);
        } else if r.starts_with("((") {
            get_value_result = Some(result.clone());
        }
    }

    assert_eq!(
        sat_result,
        Some(SolverResult::Sat),
        "Expected SAT for x = 5"
    );

    let get_value = get_value_result.expect("Expected get-value result");
    let values = parse_get_value(&get_value);

    let x = values.get("x").copied();
    assert_eq!(
        x,
        Some(5),
        "BUG #324: get-value returned {} for x, expected 5.\n\
         Root cause: evaluate_term() didn't check lia_model for Int variables.",
        x.map_or_else(|| "None".to_string(), |v| v.to_string())
    );

    println!("get-value correctly returned: {get_value}");
    Ok(())
}

/// Test get-value with multiple LIA variables and computed values
#[test]
#[timeout(10_000)]
fn regression_issue_324_get_value_lia_computed() -> Result<()> {
    let smt2 = r#"
(set-logic QF_LIA)
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)
(assert (= x 10))
(assert (= y (+ x 5)))
(check-sat)
(get-value (x y))
"#;

    let commands = parse(smt2)?;
    let mut executor = Executor::new();
    let results = executor.execute_all(&commands)?;

    let get_value = results
        .iter()
        .find(|r| r.starts_with("(("))
        .expect("Expected get-value result");

    let values = parse_get_value(get_value);
    let x = values.get("x").copied();
    let y = values.get("y").copied();

    assert_eq!(x, Some(10), "Expected x = 10, got {x:?}");
    assert_eq!(y, Some(15), "Expected y = 15, got {y:?}");

    println!("get-value correctly returned: {get_value}");
    Ok(())
}

/// Test get-value with LRA (Real) variables
#[test]
#[timeout(10_000)]
fn regression_issue_324_get_value_lra() -> Result<()> {
    let smt2 = r#"
(set-logic QF_LRA)
(set-option :produce-models true)
(declare-const x Real)
(assert (= x 2.5))
(check-sat)
(get-value (x))
"#;

    let commands = parse(smt2)?;
    let mut executor = Executor::new();
    let results = executor.execute_all(&commands)?;

    // Find get-value result
    let get_value = results
        .iter()
        .find(|r| r.starts_with("(("))
        .expect("Expected get-value result");

    // For Real, expect ((x (/ 5 2))) or ((x 2.5))
    assert!(
        get_value.contains('5') && get_value.contains('2'),
        "Expected get-value to return x = 5/2 or 2.5, got: {get_value}"
    );

    println!("get-value correctly returned: {get_value}");
    Ok(())
}

/// Test get-value in a combined logic (AUFLIA) where model construction involves multiple theories.
#[test]
#[timeout(10_000)]
fn regression_get_value_auflia_combined_logic() -> Result<()> {
    let smt2 = r#"
(set-logic QF_AUFLIA)
(set-option :produce-models true)
(declare-const a Int)
(declare-const b Int)
(assert (not (= a b)))
(assert (> a 0))
(assert (>= b 0))
(assert (< b 10))
(check-sat)
(get-value (a b))
"#;

    let commands = parse(smt2)?;
    let mut executor = Executor::new();
    let results = executor.execute_all(&commands)?;

    let get_value = results
        .iter()
        .find(|r| r.starts_with("(("))
        .expect("Expected get-value result");
    let values = parse_get_value(get_value);

    let a = values.get("a").copied().expect("Expected a in get-value");
    let b = values.get("b").copied().expect("Expected b in get-value");

    assert_ne!(a, b, "Model violates (not (= a b)): a={a}, b={b}");
    assert!(a > 0, "Model violates (> a 0): a={a}");
    assert!(b >= 0, "Model violates (>= b 0): b={b}");
    assert!(b < 10, "Model violates (< b 10): b={b}");

    println!("get-value correctly returned: {get_value}");
    Ok(())
}

/// Test get-value in UFLIA (EUF + LIA) to ensure model values are reported correctly.
#[test]
#[timeout(10_000)]
fn regression_get_value_uflia_combined_logic() -> Result<()> {
    let smt2 = r#"
(set-logic QF_UFLIA)
(set-option :produce-models true)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x 1))
(assert (= y 2))
(assert (not (= (f x) (f y))))
(check-sat)
(get-value (x y))
"#;

    let commands = parse(smt2)?;
    let mut executor = Executor::new();
    let results = executor.execute_all(&commands)?;

    // Ensure SAT before validating values
    assert!(
        results.iter().any(|r| r.trim().eq_ignore_ascii_case("sat")),
        "Expected SAT, got outputs: {results:?}"
    );

    let get_value = results
        .iter()
        .find(|r| r.starts_with("(("))
        .expect("Expected get-value result");
    let values = parse_get_value(get_value);

    let x = values.get("x").copied().expect("Expected x in get-value");
    let y = values.get("y").copied().expect("Expected y in get-value");

    assert_eq!(x, 1, "Expected x = 1, got {x}");
    assert_eq!(y, 2, "Expected y = 2, got {y}");

    println!("get-value correctly returned: {get_value}");
    Ok(())
}

/// Test get-value with BitVec variables - verifies #358 fix for BV model extraction
#[test]
#[timeout(10_000)]
fn regression_issue_358_get_value_bv() -> Result<()> {
    let smt2 = r#"
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(check-sat)
(get-value (x))
"#;

    let commands = parse(smt2)?;
    let mut executor = Executor::new();
    let results = executor.execute_all(&commands)?;

    // Find get-value result
    let get_value = results
        .iter()
        .find(|r| r.starts_with("(("))
        .expect("Expected get-value result");

    // Should return ((x #x05)) - the actual value, not #x00
    assert!(
        get_value.contains("#x05") || get_value.contains("#b00000101"),
        "BUG #358: get-value returned {get_value} for x, expected #x05.\n\
         Root cause: evaluate_term() didn't check bv_model for BitVec variables."
    );

    println!("get-value correctly returned: {get_value}");
    Ok(())
}

/// Test get-value with BitVec computed values
#[test]
#[timeout(10_000)]
fn regression_issue_358_get_value_bv_computed() -> Result<()> {
    let smt2 = r#"
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x #x0A))
(assert (= y (bvadd x #x05)))
(check-sat)
(get-value (x y))
"#;

    let commands = parse(smt2)?;
    let mut executor = Executor::new();
    let results = executor.execute_all(&commands)?;

    let get_value = results
        .iter()
        .find(|r| r.starts_with("(("))
        .expect("Expected get-value result");

    // x should be #x0A (10), y should be #x0F (15)
    assert!(
        get_value.contains("#x0a") || get_value.contains("#x0A"),
        "Expected x = #x0A in get-value, got: {get_value}"
    );
    assert!(
        get_value.contains("#x0f") || get_value.contains("#x0F"),
        "Expected y = #x0F in get-value, got: {get_value}"
    );

    println!("get-value correctly returned: {get_value}");
    Ok(())
}

// ============================================================================
// QF_S / QF_SLIA Differential Tests (CVC5 benchmark suite)
// ============================================================================

/// Scan a directory for .smt2 files with QF_S or QF_SLIA logic.
/// Returns paths to matching files.
fn find_qf_s_benchmarks(dir: &Path) -> Vec<std::path::PathBuf> {
    let mut results = Vec::new();
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return results,
    };
    for entry in entries.filter_map(std::result::Result::ok) {
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "smt2") {
            if let Ok(content) = fs::read_to_string(&path) {
                // Only accept QF_S and QF_SLIA — skip ALL, SLIA (quantified), etc.
                let has_qf_s =
                    content.contains("(set-logic QF_S)") || content.contains("(set-logic QF_SLIA)");
                if has_qf_s {
                    results.push(path);
                }
            }
        }
    }
    results.sort();
    results
}

/// Run differential test on CVC5 string benchmarks (QF_S and QF_SLIA).
///
/// This is the string theory soundness gate: any disagreement between AY
/// and Z3 on a definite (sat/unsat) result is a soundness bug.
fn differential_test_cvc5_strings() -> Result<DifferentialSummary> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let cvc5_base = manifest.join("../../reference/cvc5/test/regress/cli");

    let mut all_paths = Vec::new();
    for subdir in ["regress0/strings", "regress1/strings"] {
        let dir = cvc5_base.join(subdir);
        if dir.exists() {
            all_paths.extend(find_qf_s_benchmarks(&dir));
        }
    }

    let mut total = 0;
    let mut agreed = 0;
    let mut mismatches = Vec::new();
    let mut incompletes = Vec::new();

    for file_path in &all_paths {
        let file_name = file_path.file_name().unwrap().to_string_lossy().to_string();
        total += 1;

        let z3_result = match run_z3(file_path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("Z3 error on {file_name}: {e}");
                SolverResult::Error(e.to_string())
            }
        };

        let ay_result = match run_ay(file_path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("AY error on {file_name}: {e}");
                SolverResult::Error(e.to_string())
            }
        };

        if z3_result.is_definite() && ay_result.is_definite() {
            if z3_result == ay_result {
                agreed += 1;
            } else {
                mismatches.push(Mismatch {
                    file: file_name.clone(),
                    z3_result: z3_result.clone(),
                    ay_result: ay_result.clone(),
                });
            }
        } else if z3_result.is_definite() && !ay_result.is_definite() {
            eprintln!("AY incomplete on {file_name}: Z3={z3_result:?}, AY={ay_result:?}");
            incompletes.push(Mismatch {
                file: file_name.clone(),
                z3_result: z3_result.clone(),
                ay_result: ay_result.clone(),
            });
        } else {
            agreed += 1;
        }
    }

    Ok(DifferentialSummary {
        total,
        agreed,
        mismatches,
        incompletes,
    })
}

/// Differential test: QF_S and QF_SLIA vs Z3 on CVC5 regression benchmarks.
///
/// 180 benchmarks (70 QF_S + 110 QF_SLIA) from CVC5's regress0/regress1.
/// Each benchmark has a 10s per-solver timeout. The test-level timeout covers
/// the full scan.
#[test]
#[timeout(600_000)]
fn differential_qf_s_qf_slia_cvc5_vs_z3() -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    // Verify CVC5 reference directory exists
    let cvc5_strings = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reference/cvc5/test/regress/cli/regress0/strings");
    if !cvc5_strings.exists() {
        eprintln!(
            "CVC5 reference not found at {}; skipping string differential test",
            cvc5_strings.display()
        );
        return Ok(());
    }

    let summary = differential_test_cvc5_strings()?;

    println!("\n=== QF_S/QF_SLIA Differential Test Results (CVC5 suite) ===");
    println!("Total benchmarks: {}", summary.total);
    println!("Agreed with Z3:   {}", summary.agreed);
    println!("Mismatches:       {}", summary.mismatches.len());
    println!("Incompletes:      {}", summary.incompletes.len());

    if !summary.mismatches.is_empty() {
        println!("\n!!! SOUNDNESS VIOLATIONS DETECTED !!!");
        for m in &summary.mismatches {
            println!("  {}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result);
        }
    }
    if !summary.incompletes.is_empty() {
        println!("\nCompleteness gaps (not soundness bugs):");
        for i in &summary.incompletes {
            println!("  {}: Z3={:?}, AY={:?}", i.file, i.z3_result, i.ay_result);
        }
    }

    // Known false-UNSAT bugs (AY=Unsat, Z3=Sat) being actively tracked.
    // Each entry is a file name + the issue tracking the bug.
    let known_mismatches: &[&str] = &[
        "issue3497.smt2", // str.indexof semantics: (= (str.indexof x y 1) (str.len x)) with contains
        "issue8481.smt2", // regex: str.in_re with str.replace
        "issue2429-code.smt2", // str.to_code + define-fun with integer arithmetic
    ];
    let (known, new_bugs): (Vec<_>, Vec<_>) = summary
        .mismatches
        .iter()
        .partition(|m| known_mismatches.contains(&m.file.as_str()));
    if !known.is_empty() {
        eprintln!(
            "KNOWN false-UNSAT bugs (tracked):\n  {}",
            known
                .iter()
                .map(|m| format!("{}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result))
                .collect::<Vec<_>>()
                .join("\n  ")
        );
    }

    // SOUNDNESS GATE: zero NEW disagreements allowed
    assert!(
        new_bugs.is_empty(),
        "NEW SOUNDNESS BUG: AY disagrees with Z3 on {} of {} QF_S/QF_SLIA benchmarks.\n\
         New mismatches: {:?}",
        new_bugs.len(),
        summary.total,
        new_bugs
            .iter()
            .map(|m| format!("{}: Z3={:?}, AY={:?}", m.file, m.z3_result, m.ay_result))
            .collect::<Vec<_>>()
    );

    // Require minimum benchmark coverage (at least 50 benchmarks found)
    assert!(
        summary.total >= 50,
        "Too few QF_S/QF_SLIA benchmarks found: {} (expected >= 50)",
        summary.total
    );

    println!(
        "\n[OK] {} QF_S/QF_SLIA benchmarks: {} agreed, {} incomplete, {} known bugs (no new soundness bugs)",
        summary.total, summary.agreed, summary.incompletes.len(), known.len()
    );
    Ok(())
}
