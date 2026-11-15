// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The z3 legs of ay-dpll's integration tests.
//!
//! Every leg takes its verdicts from ONE oracle: `ay_test_support::z3`
//! resolves it by path (`Z3_PATH`, else the first z3 on `PATH` that proves it
//! is z3, past aterm's reroute stubs) and names it once per test binary on
//! stderr. Nothing here spawns `z3` by name: under aterm that reaches a stub
//! that refuses, and these legs used to read the refusal as "z3 absent" and
//! skip, so a differential suite could stop comparing against z3 and stay
//! green. A leg is optional (a visible `AY-TEST-SKIP` when no z3 is usable,
//! a failure under `Z3_DIFFERENTIAL_REQUIRED`), and a non-answer from the
//! oracle is absence of evidence, never disagreement.

use super::SolverOutcome;
use anyhow::{anyhow, Context, Result};
use ay_frontend::{parse, Command as SmtCommand};
use ay_test_support::z3::{optional_z3, Z3Oracle};
use std::fs;
use std::io::{Read, Write};
use std::path::Path;
use std::process::Stdio;
use std::time::Duration;
use wait_timeout::ChildExt;

/// This test binary's oracle, or `None` after a visible skip line.
pub(crate) fn z3_oracle() -> Option<&'static Z3Oracle> {
    optional_z3(concat!("ay-dpll ", env!("CARGO_CRATE_NAME")))
}

/// True when this binary has a usable z3; the skip is announced otherwise.
pub(crate) fn check_z3_or_skip() -> bool {
    z3_oracle().is_some()
}

fn require_oracle() -> Result<&'static Z3Oracle> {
    z3_oracle().ok_or_else(|| anyhow!("no usable z3 oracle (see the AY-TEST-SKIP line)"))
}

pub(crate) fn run_z3_file(path: &Path, timeout_secs: u64) -> Result<SolverOutcome> {
    let mut child = require_oracle()?
        .command()
        .arg(format!("-T:{timeout_secs}"))
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("failed to spawn z3 for {}", path.display()))?;

    let timeout = Duration::from_secs(timeout_secs + 2);
    let mut timed_out = false;
    let status = match child
        .wait_timeout(timeout)
        .context("failed waiting for z3")?
    {
        Some(status) => status,
        None => {
            timed_out = true;
            let _ = child.kill();
            child.wait().context("failed to kill timed out z3")?
        }
    };

    let mut stdout = Vec::new();
    if let Some(mut handle) = child.stdout.take() {
        handle
            .read_to_end(&mut stdout)
            .context("failed reading z3 stdout")?;
    }

    let mut stderr = Vec::new();
    if let Some(mut handle) = child.stderr.take() {
        handle
            .read_to_end(&mut stderr)
            .context("failed reading z3 stderr")?;
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

pub(crate) fn assert_z3_sat_or_known_status(
    path: &Path,
    timeout_secs: u64,
    label: &str,
) -> Result<()> {
    if !check_z3_or_skip() {
        return Ok(());
    }

    match run_z3_file(path, timeout_secs)? {
        SolverOutcome::Sat => Ok(()),
        SolverOutcome::Unknown | SolverOutcome::Timeout => {
            let status = smtlib_status(path)?;
            if status == Some(SolverOutcome::Sat) {
                eprintln!(
                    "Z3 did not confirm SAT for {label} within {timeout_secs}s; trusting SMT-LIB :status sat"
                );
                Ok(())
            } else {
                Err(anyhow!(
                    "Z3 did not confirm SAT for {label}; SMT-LIB status was {status:?}"
                ))
            }
        }
        other => Err(anyhow!(
            "Z3 disagrees on expected SAT for {label}: got {other:?}"
        )),
    }
}

fn smtlib_status(path: &Path) -> Result<Option<SolverOutcome>> {
    let smt = fs::read_to_string(path)
        .with_context(|| format!("failed reading benchmark {}", path.display()))?;
    let commands = parse(&smt).with_context(|| format!("failed parsing {}", path.display()))?;
    Ok(commands.into_iter().find_map(|command| match command {
        SmtCommand::SetInfo(keyword, value) if keyword == ":status" => {
            Some(SolverOutcome::from_output_line(&value.to_string()))
        }
        _ => None,
    }))
}

/// z3's full stdout for `smt` on stdin; an error when it did not exit 0.
pub(crate) fn solve_with_z3(smt: &str) -> std::result::Result<String, String> {
    let mut child = require_oracle()
        .map_err(|e| e.to_string())?
        .command()
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn z3: {e}"))?;

    if let Some(stdin) = child.stdin.as_mut() {
        stdin
            .write_all(smt.as_bytes())
            .map_err(|e| format!("failed to write SMT to z3 stdin: {e}"))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("failed waiting for z3: {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("z3 exited with status {}: {stderr}", output.status));
    }
    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

/// z3's full stdout for the SMT-LIB file at `path`; an error when it did not
/// exit 0.
pub(crate) fn solve_with_z3_file(path: &Path) -> std::result::Result<String, String> {
    let output = require_oracle()
        .map_err(|e| e.to_string())?
        .command()
        .arg(path)
        .output()
        .map_err(|e| format!("failed to spawn z3 for {}: {e}", path.display()))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "z3 failed for {} with status {}: {}",
            path.display(),
            output.status,
            stderr
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}
