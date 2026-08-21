// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded AY subprocess helpers for SMT-LIB integration tests.
//!
//! Every child runs in the process-group-aware timeout harness from
//! [`crate::spawn`]. The SMT suites use this boundary instead of an outer
//! `ntest` timeout, which can detach a worker blocked in `waitpid`. On expiry,
//! the calling thread terminates and reaps the solver process group, including
//! grandchildren.

use std::fmt;
use std::io;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

/// Captured text and status from one bounded AY invocation.
pub(crate) struct AyOutput {
    pub(crate) stdout: String,
    pub(crate) stderr: String,
    pub(crate) success: bool,
}

/// Whether an incomplete `unknown` result is acceptable for an assertion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnknownPolicy {
    /// Require the expected definite result.
    Reject,
    /// Accept `unknown` in addition to the expected definite result.
    Accept,
}

/// Normalized first response from a file-based SMT-LIB run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Outcome {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error(String),
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sat => write!(f, "sat"),
            Self::Unsat => write!(f, "unsat"),
            Self::Unknown => write!(f, "unknown"),
            Self::Timeout => write!(f, "timeout"),
            Self::Error(error) => write!(f, "error: {error}"),
        }
    }
}

/// Run AY on SMT-LIB supplied over stdin with the default child deadline.
pub(crate) fn run_ay_stdin(input: &str) -> AyOutput {
    run_ay_stdin_with_args(input, &[])
}

/// Run AY with arguments and SMT-LIB supplied over stdin.
pub(crate) fn run_ay_stdin_with_args(input: &str, args: &[&str]) -> AyOutput {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .output_timeout_with_stdin(input.as_bytes(), DEFAULT_CHILD_TIMEOUT)
        .unwrap_or_else(|error| panic!("bounded AY stdin run failed: {error}"));
    AyOutput {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        success: output.status.success(),
    }
}

/// Run AY on a file and normalize its first response.
pub(crate) fn run_ay_file(path: &Path, timeout: Duration) -> Outcome {
    let output = match Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(path)
        .output_timeout(timeout)
    {
        Ok(output) => output,
        Err(error) if error.kind() == io::ErrorKind::TimedOut => return Outcome::Timeout,
        Err(error) => return Outcome::Error(format!("child execution failed: {error}")),
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let first = stdout.lines().next().unwrap_or("").trim();
    if !output.status.success() && first.is_empty() {
        return Outcome::Error(format!(
            "exit code {:?}, stderr: {}",
            output.status.code(),
            String::from_utf8_lossy(&output.stderr)
                .chars()
                .take(200)
                .collect::<String>()
        ));
    }
    match first {
        "sat" => Outcome::Sat,
        "unsat" => Outcome::Unsat,
        "unknown" => Outcome::Unknown,
        other => Outcome::Error(format!(
            "unexpected output `{other}`, stderr: {}",
            String::from_utf8_lossy(&output.stderr)
                .chars()
                .take(200)
                .collect::<String>()
        )),
    }
}

/// Extract the first output line, trimmed.
pub(crate) fn first_line(output: &AyOutput) -> &str {
    output.stdout.lines().next().unwrap_or("").trim()
}

/// Collect all `check-sat` response lines from captured stdout.
pub(crate) fn check_sat_results(output: &AyOutput) -> Vec<String> {
    output
        .stdout
        .lines()
        .filter_map(|line| match line.trim() {
            result @ ("sat" | "unsat" | "unknown") => Some(result.to_owned()),
            _ => None,
        })
        .collect()
}

/// Assert the first response against a definite result and unknown policy.
pub(crate) fn assert_result(
    output: &AyOutput,
    expected: &str,
    unknown_policy: UnknownPolicy,
    context: &str,
) {
    let actual = first_line(output);
    if unknown_policy == UnknownPolicy::Accept && actual == "unknown" {
        return;
    }
    assert!(
        output.success,
        "{context}: ay exited with failure\nstdout:\n{}\nstderr:\n{}",
        output.stdout, output.stderr
    );
    assert_eq!(
        actual, expected,
        "{context}: expected '{expected}', got '{actual}'\nstdout:\n{}\nstderr:\n{}",
        output.stdout, output.stderr
    );
}
