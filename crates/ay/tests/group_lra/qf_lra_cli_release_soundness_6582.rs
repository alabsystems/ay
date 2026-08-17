// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Release-only CLI soundness canaries for #6582's strict interval endpoints.
//!
//! The `ay-dpll` regression covers the in-process `Executor` path. This file
//! exercises the shipped `ay` binary so the subprocess/CLI path cannot regress
//! back to false-UNSAT. The lower- and upper-endpoint inputs are hand-authored
//! Apache-2.0 reductions, not copies of the externally licensed SMT-LIB
//! benchmarks that originally exposed the defect.
//!
//! Part of #6582

#[cfg(not(debug_assertions))]
use std::io::Read;
#[cfg(not(debug_assertions))]
use std::path::{Path, PathBuf};
#[cfg(not(debug_assertions))]
use std::process::{Command, Stdio};
#[cfg(not(debug_assertions))]
use std::time::Duration;
#[cfg(not(debug_assertions))]
use wait_timeout::ChildExt;

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 10;
#[cfg(not(debug_assertions))]
const FALSE_UNSAT_CANARY_RUNS: usize = 3;

#[cfg(not(debug_assertions))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum SolverOutcome {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error(String),
}

#[cfg(not(debug_assertions))]
impl SolverOutcome {
    fn from_output_line(line: &str) -> Self {
        let normalized = line.trim().to_ascii_lowercase();
        match normalized.as_str() {
            "sat" => Self::Sat,
            "unsat" => Self::Unsat,
            "unknown" => Self::Unknown,
            _ if normalized.is_empty() => Self::Unknown,
            _ => Self::Error(normalized),
        }
    }
}

#[cfg(not(debug_assertions))]
fn workspace_path(relative: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
}

#[cfg(not(debug_assertions))]
fn run_command_with_timeout(
    mut command: Command,
    timeout_secs: u64,
) -> Result<SolverOutcome, String> {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|err| format!("failed spawning command: {err}"))?;

    let timeout = Duration::from_secs(timeout_secs + 2);
    let mut timed_out = false;
    let status = match child
        .wait_timeout(timeout)
        .map_err(|err| format!("failed waiting for command: {err}"))?
    {
        Some(status) => status,
        None => {
            timed_out = true;
            let _ = child.kill();
            child
                .wait()
                .map_err(|err| format!("failed killing timed out command: {err}"))?
        }
    };

    let mut stdout = Vec::new();
    if let Some(mut handle) = child.stdout.take() {
        handle
            .read_to_end(&mut stdout)
            .map_err(|err| format!("failed reading command stdout: {err}"))?;
    }

    let mut stderr = Vec::new();
    if let Some(mut handle) = child.stderr.take() {
        handle
            .read_to_end(&mut stderr)
            .map_err(|err| format!("failed reading command stderr: {err}"))?;
    }

    if timed_out {
        return Ok(SolverOutcome::Timeout);
    }

    let first_line = String::from_utf8_lossy(&stdout)
        .lines()
        .next()
        .unwrap_or_default()
        .trim()
        .to_string();
    if first_line.is_empty() && !status.success() {
        let stderr = String::from_utf8_lossy(&stderr).trim().to_string();
        return Ok(SolverOutcome::Error(stderr));
    }

    Ok(SolverOutcome::from_output_line(&first_line))
}

#[cfg(not(debug_assertions))]
fn run_ay_file(path: &Path) -> Result<SolverOutcome, String> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    command.arg(path);
    run_command_with_timeout(command, BENCHMARK_TIMEOUT_SECS)
}

#[cfg(not(debug_assertions))]
fn assert_cli_sat_6582(name: &str, relative_path: &str) -> Result<(), String> {
    let path = workspace_path(relative_path);
    assert!(path.exists(), "benchmark not found: {}", path.display());

    for run in 0..FALSE_UNSAT_CANARY_RUNS {
        let got = run_ay_file(&path)?;
        assert_eq!(
            got,
            SolverOutcome::Sat,
            "CLI release run {run} returned {got:?} for {name} (#6582)"
        );
    }
    Ok(())
}

#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn qf_lra_cli_release_mechanism_open_zero_lower_sat_6582() -> Result<(), String> {
    assert_cli_sat_6582(
        "open-zero lower endpoint",
        "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_lower_sat.smt2",
    )
}

#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn qf_lra_cli_release_mechanism_open_zero_upper_sat_6582() -> Result<(), String> {
    assert_cli_sat_6582(
        "open-zero upper endpoint",
        "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_upper_sat.smt2",
    )
}
