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
//! Run the complete, checksum-pinned SMT-LIB 2024 QF_LRA archive in slices by
//! first fetching it with `scripts/download_smtcomp_benchmarks.sh --logic
//! QF_LRA`, then varying:
//! - `AY_QF_LRA_RELEASE_FULL_SWEEP=1`
//! - `AY_QF_LRA_RELEASE_BATCH_START`
//! - `AY_QF_LRA_RELEASE_BATCH_SIZE`
//!
//! Every full-sweep slice also includes the three original release reproducers,
//! even when they fall outside the selected range.
//!
//! Without the explicit full-sweep opt-in, this test runs the three
//! hand-authored Apache-2.0 release canaries. The external SMT-LIB corpus
//! remains separately fetched and is never required by the default gate.
//!
//! Part of #6564

#[cfg(not(debug_assertions))]
use std::io::Read;
#[cfg(not(debug_assertions))]
use std::path::{Path, PathBuf};
#[cfg(not(debug_assertions))]
use std::process::{Command, Stdio};
#[cfg(not(debug_assertions))]
use std::sync::OnceLock;
#[cfg(not(debug_assertions))]
use std::time::Duration;
#[cfg(not(debug_assertions))]
use wait_timeout::ChildExt;

#[cfg(not(debug_assertions))]
const BENCHMARK_TIMEOUT_SECS: u64 = 6;
#[cfg(not(debug_assertions))]
const DEFAULT_BATCH_SIZE: usize = 5;
#[cfg(not(debug_assertions))]
const EXPECTED_PINNED_ARCHIVE_BENCHMARKS: usize = 1_753;
#[cfg(not(debug_assertions))]
const PINNED_ARCHIVE_SHA256: &str =
    "8e551882cf78432953f9e6f452cde098835e6cdc64b301becf42135609ee9881";
#[cfg(not(debug_assertions))]
const PINNED_CORPUS_ROOT: &str = "benchmarks/smtcomp/non-incremental/QF_LRA";
#[cfg(not(debug_assertions))]
const PINNED_CORPUS_PROVENANCE: &str = "benchmarks/smtcomp/.QF_LRA-2024.sha256";
#[cfg(not(debug_assertions))]
const FULL_SWEEP_ENV: &str = "AY_QF_LRA_RELEASE_FULL_SWEEP";
#[cfg(not(debug_assertions))]
const BATCH_START_ENV: &str = "AY_QF_LRA_RELEASE_BATCH_START";
#[cfg(not(debug_assertions))]
const BATCH_SIZE_ENV: &str = "AY_QF_LRA_RELEASE_BATCH_SIZE";
#[cfg(not(debug_assertions))]
const HERMETIC_FIXTURES: [&str; 3] = [
    "benchmarks/smt/regression/qf_lra_release_soundness/slack_reason_sat.smt2",
    "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_lower_sat.smt2",
    "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_upper_sat.smt2",
];
#[cfg(not(debug_assertions))]
const ORIGINAL_RELEASE_REPRODUCERS: [&str; 3] = [
    "constraints-tempo-width-10.smt2",
    "constraints-tempo-width-60.smt2",
    "simple_startup_6nodes.missing.induct.smt2",
];

#[cfg(not(debug_assertions))]
static Z3_AVAILABLE: OnceLock<bool> = OnceLock::new();

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
fn z3_available() -> bool {
    *Z3_AVAILABLE.get_or_init(|| {
        Command::new("z3")
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
    })
}

#[cfg(not(debug_assertions))]
fn parse_batch_env_usize_6564(
    key: &str,
    value: Result<String, std::env::VarError>,
    default: usize,
) -> Result<usize, String> {
    match value {
        Ok(raw) => raw
            .parse::<usize>()
            .map_err(|err| format!("{key}={raw:?} is not a valid usize: {err}")),
        Err(std::env::VarError::NotPresent) => Ok(default),
        Err(err) => Err(format!("failed reading {key}: {err}")),
    }
}

#[cfg(not(debug_assertions))]
fn full_sweep_requested_6564() -> Result<bool, String> {
    match std::env::var(FULL_SWEEP_ENV) {
        Ok(value) if value == "1" => Ok(true),
        Ok(value) if value == "0" => Ok(false),
        Ok(value) => Err(format!(
            "{FULL_SWEEP_ENV} must be exactly 0 or 1, got {value:?}"
        )),
        Err(std::env::VarError::NotPresent) => Ok(false),
        Err(error) => Err(format!("failed reading {FULL_SWEEP_ENV}: {error}")),
    }
}

#[cfg(not(debug_assertions))]
fn selected_batch_range_6564(
    suite_len: usize,
    full_sweep: bool,
) -> Result<std::ops::Range<usize>, String> {
    if !full_sweep {
        return Ok(0..suite_len);
    }

    let start = parse_batch_env_usize_6564(
        BATCH_START_ENV,
        std::env::var("AY_QF_LRA_RELEASE_BATCH_START"),
        0,
    )?;
    let size = parse_batch_env_usize_6564(
        BATCH_SIZE_ENV,
        std::env::var("AY_QF_LRA_RELEASE_BATCH_SIZE"),
        DEFAULT_BATCH_SIZE,
    )?;
    assert!(size > 0, "{BATCH_SIZE_ENV} must be > 0");
    assert!(
        start < suite_len,
        "{BATCH_START_ENV}={start} must be less than {suite_len}"
    );
    let end = (start + size).min(suite_len);
    Ok(start..end)
}

#[cfg(not(debug_assertions))]
fn collect_smt2_files_recursive_6564(dir: &Path, entries: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in
        std::fs::read_dir(dir).map_err(|err| format!("failed reading {}: {err}", dir.display()))?
    {
        let entry =
            entry.map_err(|err| format!("failed reading entry in {}: {err}", dir.display()))?;
        let file_type = entry
            .file_type()
            .map_err(|err| format!("failed reading type for {}: {err}", entry.path().display()))?;
        if file_type.is_dir() {
            collect_smt2_files_recursive_6564(&entry.path(), entries)?;
        } else if file_type.is_file() && entry.path().extension().is_some_and(|ext| ext == "smt2") {
            entries.push(entry.path());
        }
    }
    Ok(())
}

#[cfg(not(debug_assertions))]
fn qf_lra_smtcomp_entries_6564() -> Result<Vec<PathBuf>, String> {
    let provenance_path = workspace_path(PINNED_CORPUS_PROVENANCE);
    let provenance = std::fs::read_to_string(&provenance_path).map_err(|err| {
        format!(
            "missing pinned QF_LRA archive provenance {}: {err}; run scripts/download_smtcomp_benchmarks.sh --logic QF_LRA",
            provenance_path.display()
        )
    })?;
    if provenance.trim() != PINNED_ARCHIVE_SHA256 {
        return Err(format!(
            "pinned QF_LRA archive provenance mismatch in {}: expected {}, found {:?}",
            provenance_path.display(),
            PINNED_ARCHIVE_SHA256,
            provenance.trim()
        ));
    }

    let dir = workspace_path(PINNED_CORPUS_ROOT);
    let mut entries = Vec::new();
    collect_smt2_files_recursive_6564(&dir, &mut entries)?;
    entries.sort();
    Ok(entries)
}

#[cfg(not(debug_assertions))]
fn qf_lra_release_entries_6564(full_sweep: bool) -> Result<Vec<PathBuf>, String> {
    if full_sweep {
        let entries = qf_lra_smtcomp_entries_6564()?;
        if entries.len() != EXPECTED_PINNED_ARCHIVE_BENCHMARKS {
            return Err(format!(
                "pinned SMT-LIB 2024 QF_LRA archive must contain exactly {} recursively discovered .smt2 files: found {} under {}",
                EXPECTED_PINNED_ARCHIVE_BENCHMARKS,
                entries.len(),
                workspace_path(PINNED_CORPUS_ROOT).display()
            ));
        }
        for required in ORIGINAL_RELEASE_REPRODUCERS {
            let occurrences = entries
                .iter()
                .filter(|path| path.file_name().and_then(|name| name.to_str()) == Some(required))
                .count();
            if occurrences != 1 {
                return Err(format!(
                    "pinned QF_LRA archive must contain original release reproducer {required} exactly once; found {occurrences}"
                ));
            }
        }
        return Ok(entries);
    }

    HERMETIC_FIXTURES
        .iter()
        .map(|relative| {
            let path = workspace_path(relative);
            if path.is_file() {
                Ok(path)
            } else {
                Err(format!(
                    "hermetic QF_LRA fixture missing: {}",
                    path.display()
                ))
            }
        })
        .collect()
}

#[cfg(not(debug_assertions))]
fn selected_release_entries_6564(
    entries: &[PathBuf],
    range: &std::ops::Range<usize>,
    full_sweep: bool,
) -> Vec<PathBuf> {
    let mut selected = entries[range.clone()].to_vec();
    if full_sweep {
        for required in ORIGINAL_RELEASE_REPRODUCERS {
            let path = entries
                .iter()
                .find(|path| path.file_name().and_then(|name| name.to_str()) == Some(required))
                .expect("full-corpus validation checked every original reproducer");
            if !selected.contains(path) {
                selected.push(path.clone());
            }
        }
    }
    selected
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
fn emit_cli_batch_progress_6564(
    range: &std::ops::Range<usize>,
    index: usize,
    selected_len: usize,
    path: &Path,
) {
    let name = path.file_name().unwrap().to_string_lossy();
    eprintln!(
        "CLI QF_LRA batch [{}..{}): case {} of {} -> {}",
        range.start,
        range.end,
        index + 1,
        selected_len,
        name
    );
}

#[cfg(not(debug_assertions))]
fn compare_cli_release_entry_6564(
    path: &Path,
    use_z3: bool,
    require_sat: bool,
) -> Result<(u32, u32, Option<String>), String> {
    let reference_result = if use_z3 {
        run_z3_file(path)?
    } else {
        SolverOutcome::Sat
    };
    let ay_result = run_ay_file(path)?;
    let reference_definite = u32::from(matches!(
        reference_result,
        SolverOutcome::Sat | SolverOutcome::Unsat
    ));
    let ay_definite = u32::from(matches!(
        ay_result,
        SolverOutcome::Sat | SolverOutcome::Unsat
    ));
    let disagreement = if require_sat && ay_result != SolverOutcome::Sat {
        let name = path.file_name().unwrap().to_string_lossy();
        Some(format!("{name}: AY={ay_result:?}, expected Sat"))
    } else if reference_definite == 1 && ay_definite == 1 && reference_result != ay_result {
        let name = path.file_name().unwrap().to_string_lossy();
        Some(format!(
            "{name}: AY={ay_result:?} vs reference={reference_result:?}"
        ))
    } else {
        None
    };
    Ok((ay_definite, reference_definite, disagreement))
}

#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(240_000)]
fn qf_lra_cli_release_soundness_selected_batch_6564() -> Result<(), String> {
    let full_sweep = full_sweep_requested_6564()?;
    if full_sweep && !z3_available() {
        return Err(format!(
            "{FULL_SWEEP_ENV}=1 requires z3 in PATH for differential checking"
        ));
    }

    let entries = qf_lra_release_entries_6564(full_sweep)?;
    let range = selected_batch_range_6564(entries.len(), full_sweep)?;
    let selected_entries = selected_release_entries_6564(&entries, &range, full_sweep);
    let mut disagreements = Vec::new();
    let mut ay_solved = 0u32;
    let mut reference_solved = 0u32;

    for (index, path) in selected_entries.iter().enumerate() {
        emit_cli_batch_progress_6564(&range, index, selected_entries.len(), path);
        let (ay_definite, reference_definite, disagreement) =
            compare_cli_release_entry_6564(path, full_sweep, !full_sweep)?;
        ay_solved += ay_definite;
        reference_solved += reference_definite;
        if let Some(disagreement) = disagreement {
            disagreements.push(disagreement);
        }
    }

    eprintln!(
        "CLI QF_LRA release soundness [{}..{}): mode={}, checked {}, AY solved {ay_solved}, reference solved {reference_solved}, disagreements {}",
        range.start,
        range.end,
        if full_sweep { "full-corpus" } else { "hermetic" },
        selected_entries.len(),
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
