// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Oracle outcome boundary shared by the differential corpus entrypoints.

use anyhow::{Context, Result};
use std::io::Read;
use std::path::Path;
use std::process::{Child, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

#[derive(Debug, Clone, PartialEq)]
pub(super) enum SolverResult {
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

    pub(super) fn is_definite(&self) -> bool {
        matches!(self, Self::Sat | Self::Unsat)
    }
}

struct OwnedChild(Child);

impl Drop for OwnedChild {
    fn drop(&mut self) {
        if !matches!(self.0.try_wait(), Ok(Some(_))) {
            let _ = self.0.kill();
        }
        let _ = self.0.wait();
    }
}

pub(super) fn run_z3(path: &Path) -> Result<SolverResult> {
    const Z3_TIMEOUT_SECS: u64 = 10;
    const Z3_TIMEOUT_SLACK_SECS: u64 = 2;

    // Retain the sole identity-checked resolver and both original time limits.
    let mut child = OwnedChild(
        crate::common::z3_oracle()
            .context("no usable z3 oracle (see the AY-TEST-SKIP line)")?
            .command()
            .arg(format!("-T:{Z3_TIMEOUT_SECS}"))
            .arg(path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .context("failed to spawn the z3 oracle")?,
    );
    collect_z3_child(
        &mut child.0,
        Duration::from_secs(Z3_TIMEOUT_SECS + Z3_TIMEOUT_SLACK_SECS),
    )
}

fn collect_z3_child(child: &mut Child, timeout: Duration) -> Result<SolverResult> {
    let mut timed_out = false;
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
        return Ok(SolverResult::Error(format!("timeout after {timeout:?}")));
    }
    if !status.success() {
        return Ok(SolverResult::Error(format!(
            "z3 exited with {status}: {}",
            String::from_utf8_lossy(&stderr)
        )));
    }
    let stdout = String::from_utf8(stdout).context("z3 stdout is not UTF-8")?;
    if stdout
        .lines()
        .any(|line| line.trim_start().starts_with("(error \""))
    {
        return Ok(SolverResult::Error(stdout));
    }
    Ok(SolverResult::from_str(stdout.lines().next().unwrap_or("")))
}

/// Executed by the canonical exact BV test as well as the focused control test.
pub(super) fn assert_contract() -> Result<()> {
    println!("AY-ORACLE-CONTROL begin");
    #[cfg(unix)]
    {
        assert_child_contract()?;
        println!("AY-ORACLE-CONTROL Unix child outcomes passed");
    }
    #[cfg(not(unix))]
    println!("AY-TEST-SKIP suite=ay-dpll oracle-child-controls reason=requires-unix");
    assert_population_contract()?;
    println!("AY-ORACLE-CONTROL corpus accounting passed");
    Ok(())
}

#[cfg(unix)]
fn assert_child_contract() -> Result<()> {
    use std::process::Command;
    use std::time::Instant;

    let cases = [
        ("printf 'sat\\n'", SolverResult::Sat),
        ("printf 'unsat\\n'", SolverResult::Unsat),
        ("printf 'unknown\\n'", SolverResult::Unknown),
        ("exit 0", SolverResult::Unknown),
    ];
    for (script, expected) in cases {
        let mut child = shell_child(script)?;
        assert_eq!(
            collect_z3_child(&mut child.0, Duration::from_secs(2))?,
            expected,
            "oracle control {script:?}"
        );
        assert!(child.0.try_wait()?.is_some(), "child must be reaped");
    }
    for script in [
        "printf 'sat\\n'; exit 7",
        "printf 'unsat\\n'; kill -TERM $$",
        "printf '(error \"injected\")\\n'",
        "printf 'sat\\n(error \"injected\")\\n'",
    ] {
        let mut child = shell_child(script)?;
        assert!(
            matches!(
                collect_z3_child(&mut child.0, Duration::from_secs(2))?,
                SolverResult::Error(_)
            ),
            "failed oracle must not publish an answer: {script:?}"
        );
        assert!(child.0.try_wait()?.is_some(), "child must be reaped");
    }
    // A naturally bounded child also exits within two seconds if a regression
    // defeats the kill. The guard kills/reaps it on every assertion/error path.
    let mut child = OwnedChild(
        Command::new("/bin/sleep")
            .arg("2")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?,
    );
    let started = Instant::now();
    let result = collect_z3_child(&mut child.0, Duration::from_millis(20))?;
    assert!(matches!(result, SolverResult::Error(ref error) if error.contains("timeout")));
    assert!(
        child.0.try_wait()?.is_some(),
        "timeout child must be reaped"
    );
    assert!(
        started.elapsed() < Duration::from_secs(1),
        "timeout must kill promptly"
    );
    Ok(())
}

#[cfg(unix)]
fn shell_child(script: &str) -> Result<OwnedChild> {
    Ok(OwnedChild(
        std::process::Command::new("/bin/sh")
            .args(["-c", script])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?,
    ))
}

fn assert_population_contract() -> Result<()> {
    use super::differential_test_directory;

    let directory = tempfile::tempdir()?;
    assert!(
        differential_test_directory(directory.path(), unexpected_solver, unexpected_solver)
            .is_err()
    );
    std::fs::write(directory.path().join("not-a-benchmark.txt"), "ignored")?;
    assert!(
        differential_test_directory(directory.path(), unexpected_solver, unexpected_solver)
            .is_err()
    );
    std::fs::write(directory.path().join("case.smt2"), "(check-sat)\n")?;
    let non_answers: [super::BenchmarkSolver; 3] = [unknown_result, error_result, failed_result];
    for oracle in non_answers {
        assert!(differential_test_directory(directory.path(), oracle, unexpected_solver).is_err());
    }
    let summary = differential_test_directory(directory.path(), sat_result, sat_result)?;
    assert_eq!((summary.total, summary.agreed), (1, 1));
    assert!(summary.mismatches.is_empty() && summary.incompletes.is_empty());
    let summary = differential_test_directory(directory.path(), sat_result, unsat_result)?;
    assert_eq!(
        (summary.total, summary.agreed, summary.mismatches.len()),
        (1, 0, 1)
    );
    for solver in non_answers {
        let summary = differential_test_directory(directory.path(), sat_result, solver)?;
        assert_eq!(
            (summary.total, summary.agreed, summary.incompletes.len()),
            (1, 0, 1)
        );
        assert!(summary.mismatches.is_empty());
    }
    Ok(())
}

fn sat_result(_: &Path) -> Result<SolverResult> {
    Ok(SolverResult::Sat)
}

fn unsat_result(_: &Path) -> Result<SolverResult> {
    Ok(SolverResult::Unsat)
}

fn unknown_result(_: &Path) -> Result<SolverResult> {
    Ok(SolverResult::Unknown)
}

fn error_result(_: &Path) -> Result<SolverResult> {
    Ok(SolverResult::Error("injected oracle/solver error".into()))
}

fn failed_result(_: &Path) -> Result<SolverResult> {
    anyhow::bail!("injected adapter failure")
}

fn unexpected_solver(_: &Path) -> Result<SolverResult> {
    panic!("inconclusive oracle or empty population must stop before solving")
}

#[test]
#[ntest::timeout(10_000)]
fn oracle_contract_is_fail_closed() -> Result<()> {
    assert_contract()
}
