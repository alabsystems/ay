// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Release-only CLI soundness slices for `#6564`.
//!
//! The `ay-dpll` regression proves the root benchmark no longer returns a
//! release-only false-UNSAT. This file adds a subprocess-based QF_LRA sweep so
//! each benchmark is bounded by a hard wall-clock timeout on the shipped `ay`
//! binary instead of relying on cooperative in-process interrupts.
//!
//! Run the full 100-benchmark suite in slices by varying:
//! - `AY_QF_LRA_RELEASE_BATCH_START`
//! - `AY_QF_LRA_RELEASE_BATCH_SIZE`
//!
//! Part of #6564

#[cfg(not(debug_assertions))]
use std::io::Read;
#[cfg(not(debug_assertions))]
use std::path::{Path, PathBuf};
#[cfg(not(debug_assertions))]
use std::process::{Command, Stdio};
#[cfg(not(debug_assertions))]
use std::sync::{Once, OnceLock};
#[cfg(not(debug_assertions))]
use std::time::Duration;
#[cfg(not(debug_assertions))]
use wait_timeout::ChildExt;

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 6;
#[cfg(not(debug_assertions))]
const DEFAULT_BATCH_SIZE: usize = 5;
#[cfg(not(debug_assertions))]
const EXPECTED_FULL_SUITE_BENCHMARKS: usize = 100;
#[cfg(not(debug_assertions))]
const BATCH_START_ENV: &str = "AY_QF_LRA_RELEASE_BATCH_START";
#[cfg(not(debug_assertions))]
const BATCH_SIZE_ENV: &str = "AY_QF_LRA_RELEASE_BATCH_SIZE";

#[cfg(not(debug_assertions))]
static Z3_AVAILABLE: OnceLock<bool> = OnceLock::new();
#[cfg(not(debug_assertions))]
static Z3_SKIP_LOGGED: Once = Once::new();

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
fn check_z3_or_skip() -> bool {
    let available = *Z3_AVAILABLE.get_or_init(|| {
        Command::new("z3")
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
    });
    if available {
        return true;
    }

    Z3_SKIP_LOGGED.call_once(|| {
        eprintln!("Z3 not found in PATH; skipping #6564 CLI QF_LRA sweep");
    });
    false
}

#[cfg(not(debug_assertions))]
fn read_batch_env_usize_6564(key: &str, default: usize) -> Result<usize, String> {
    match std::env::var(key) {
        Ok(raw) => raw
            .parse::<usize>()
            .map_err(|err| format!("{key}={raw:?} is not a valid usize: {err}")),
        Err(std::env::VarError::NotPresent) => Ok(default),
        Err(err) => Err(format!("failed reading {key}: {err}")),
    }
}

#[cfg(not(debug_assertions))]
fn selected_batch_range_6564() -> Result<std::ops::Range<usize>, String> {
    let start = read_batch_env_usize_6564(BATCH_START_ENV, 0)?;
    let size = read_batch_env_usize_6564(BATCH_SIZE_ENV, DEFAULT_BATCH_SIZE)?;
    assert!(size > 0, "{BATCH_SIZE_ENV} must be > 0");
    assert!(
        start < EXPECTED_FULL_SUITE_BENCHMARKS,
        "{BATCH_START_ENV}={start} must be less than {EXPECTED_FULL_SUITE_BENCHMARKS}"
    );
    let end = (start + size).min(EXPECTED_FULL_SUITE_BENCHMARKS);
    Ok(start..end)
}

#[cfg(not(debug_assertions))]
fn qf_lra_smtcomp_entries_6564() -> Result<Vec<PathBuf>, String> {
    let dir = workspace_path("benchmarks/smtcomp/QF_LRA");
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .map_err(|err| format!("failed reading {}: {err}", dir.display()))?
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "smt2"))
        .map(|entry| entry.path())
        .collect();
    entries.sort();
    Ok(entries)
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
fn run_z3_file(path: &Path) -> Result<SolverOutcome, String> {
    let mut command = Command::new("z3");
    command
        .arg(format!("-T:{BENCHMARK_TIMEOUT_SECS}"))
        .arg(path);
    run_command_with_timeout(command, BENCHMARK_TIMEOUT_SECS)
}

#[cfg(not(debug_assertions))]
fn run_ay_file(path: &Path) -> Result<SolverOutcome, String> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    command.arg(path);
    run_command_with_timeout(command, BENCHMARK_TIMEOUT_SECS)
}

#[cfg(not(debug_assertions))]
fn emit_cli_batch_progress_6564(range: &std::ops::Range<usize>, index: usize, path: &Path) {
    let name = path.file_name().unwrap().to_string_lossy();
    eprintln!(
        "CLI QF_LRA batch [{}..{}): case {} of {} -> {}",
        range.start,
        range.end,
        index + 1,
        range.end - range.start,
        name
    );
}

#[cfg(not(debug_assertions))]
fn compare_cli_release_entry_6564(path: &Path) -> Result<(u32, u32, Option<String>), String> {
    let z3_result = run_z3_file(path)?;
    let ay_result = run_ay_file(path)?;
    let z3_definite = u32::from(matches!(
        z3_result,
        SolverOutcome::Sat | SolverOutcome::Unsat
    ));
    let ay_definite = u32::from(matches!(
        ay_result,
        SolverOutcome::Sat | SolverOutcome::Unsat
    ));
    let disagreement = if z3_definite == 1 && ay_definite == 1 && z3_result != ay_result {
        let name = path.file_name().unwrap().to_string_lossy();
        Some(format!("{name}: AY={ay_result:?} vs Z3={z3_result:?}"))
    } else {
        None
    };
    Ok((ay_definite, z3_definite, disagreement))
}

#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn qf_lra_cli_release_soundness_selected_batch_6564() -> Result<(), String> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    let entries = qf_lra_smtcomp_entries_6564()?;
    assert_eq!(
        entries.len(),
        EXPECTED_FULL_SUITE_BENCHMARKS,
        "QF_LRA benchmark count changed from the measured 100-case suite; update the #6564 CLI sweep"
    );

    let range = selected_batch_range_6564()?;
    let mut disagreements = Vec::new();
    let mut ay_solved = 0u32;
    let mut z3_solved = 0u32;

    for (index, path) in entries[range.clone()].iter().enumerate() {
        emit_cli_batch_progress_6564(&range, index, path);
        let (ay_definite, z3_definite, disagreement) = compare_cli_release_entry_6564(path)?;
        ay_solved += ay_definite;
        z3_solved += z3_definite;
        if let Some(disagreement) = disagreement {
            disagreements.push(disagreement);
        }
    }

    eprintln!(
        "CLI QF_LRA release soundness [{}..{}): AY solved {ay_solved}, Z3 solved {z3_solved}, disagreements {}",
        range.start,
        range.end,
        disagreements.len()
    );

    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: CLI QF_LRA release soundness [{}..{}) had {} disagreements:\n{}",
        range.start,
        range.end,
        disagreements.len(),
        disagreements.join("\n")
    );

    Ok(())
}
