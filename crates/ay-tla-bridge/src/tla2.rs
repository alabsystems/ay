// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA2 trace validation.
//!
//! Discovers and runs the TLA2 binary for validating JSONL traces
//! against temporal-logic specifications.
//!
//! Extracted from `lib.rs` for code health (#5970).

use std::path::{Path, PathBuf};
use std::process::Command;

use thiserror::Error;

use super::env_path;

/// Error type for TLA2 trace validation
#[derive(Debug, Error)]
pub enum Tla2TraceError {
    #[error("TLA2 binary not found at {path:?}; set TLA2_BIN, or add tla2 to PATH")]
    NotFound { path: PathBuf },

    #[error("failed to run TLA2: {0}")]
    Io(#[from] std::io::Error),

    #[error(
        "TLA2 trace validation failed (exit code {exit_code:?}):\nstdout: {stdout}\nstderr: {stderr}"
    )]
    ValidationFailed {
        exit_code: Option<i32>,
        stdout: String,
        stderr: String,
    },

    #[error("TLA2 trace validation timed out after {timeout:?}")]
    Timeout { timeout: std::time::Duration },
}

/// Discover the TLA2 trace-validator binary.
///
/// Search order: `TLA2_BIN`, then `tla2` on `PATH`.
pub fn find_tla2_binary() -> Result<PathBuf, Tla2TraceError> {
    if let Some(path) = env_path("TLA2_BIN") {
        if path.is_file() {
            return Ok(path);
        }
    }
    if let Ok(path) = super::which::which("tla2") {
        return Ok(path);
    }
    Err(Tla2TraceError::NotFound {
        path: PathBuf::from("tla2"),
    })
}

/// Validate a JSONL trace file against a temporal-logic spec using the TLA2 trace checker.
///
/// Returns `Ok(())` if validation succeeds. The spec file must have a companion
/// `.cfg` config file (same path with `.cfg` extension) unless `config` is given.
///
/// # Arguments
///
/// * `spec_path` — Path to the `.tla` spec file
/// * `trace_path` — Path to the `.jsonl` trace file
/// * `config` — Optional path to a `.cfg` file (defaults to spec with `.cfg` ext)
pub fn tla2_validate_trace(
    spec_path: &Path,
    trace_path: &Path,
    config: Option<&Path>,
) -> Result<(), Tla2TraceError> {
    // Default 30s timeout prevents indefinite hangs when the TLA2 binary stalls.
    tla2_validate_trace_with_timeout(
        spec_path,
        trace_path,
        config,
        Some(std::time::Duration::from_secs(30)),
    )
}

/// Like [`tla2_validate_trace`], but kills the TLA2 process if it exceeds `timeout`.
///
/// Returns [`Tla2TraceError::Timeout`] when the deadline is exceeded.
pub fn tla2_validate_trace_with_timeout(
    spec_path: &Path,
    trace_path: &Path,
    config: Option<&Path>,
    timeout: Option<std::time::Duration>,
) -> Result<(), Tla2TraceError> {
    let tla2_bin = find_tla2_binary()?;

    let config_path = match config {
        Some(c) => c.to_path_buf(),
        None => spec_path.with_extension("cfg"),
    };

    let mut child = Command::new(&tla2_bin)
        .arg("trace")
        .arg("validate")
        .arg(trace_path)
        .arg("--spec")
        .arg(spec_path)
        .arg("--config")
        .arg(&config_path)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()?;

    let output = match timeout {
        None => child.wait_with_output()?,
        Some(dur) => {
            let deadline = std::time::Instant::now() + dur;
            loop {
                match child.try_wait()? {
                    Some(_status) => break child.wait_with_output()?,
                    None => {
                        if std::time::Instant::now() >= deadline {
                            let _ = child.kill();
                            let _ = child.wait();
                            return Err(Tla2TraceError::Timeout { timeout: dur });
                        }
                        std::thread::sleep(std::time::Duration::from_millis(50));
                    }
                }
            }
        }
    };

    if output.status.success() {
        Ok(())
    } else {
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        Err(Tla2TraceError::ValidationFailed {
            exit_code: output.status.code(),
            stdout,
            stderr,
        })
    }
}
