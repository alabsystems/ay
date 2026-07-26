// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test utilities for ay-dpll integration tests.
#![allow(dead_code)]
// Shared helpers are compiled into each integration-test binary separately, so
// any given test target legitimately uses only a subset of this module.

use anyhow::{anyhow, Context, Result};
use ay_dpll::Executor;
use ay_frontend::{parse, Command as SmtCommand, Sort};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Once, OnceLock,
};
use std::time::Duration;
use wait_timeout::ChildExt;

static Z3_AVAILABLE: OnceLock<bool> = OnceLock::new();
static Z3_SKIP_LOGGED: Once = Once::new();

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SolverOutcome {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error(String),
}

impl SolverOutcome {
    pub(crate) fn from_output_line(line: &str) -> Self {
        let normalized = line.trim().to_ascii_lowercase();
        match normalized.as_str() {
            "sat" => Self::Sat,
            "unsat" => Self::Unsat,
            "unknown" => Self::Unknown,
            "timeout" => Self::Timeout,
            _ if normalized.is_empty() => Self::Unknown,
            _ => Self::Error(normalized),
        }
    }
}

pub(crate) fn workspace_path(relative: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
}

pub(crate) fn check_z3_or_skip() -> bool {
    let available = *Z3_AVAILABLE.get_or_init(|| {
        ProcessCommand::new("z3")
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
    });
    if available {
        return true;
    }

    Z3_SKIP_LOGGED.call_once(|| {
        eprintln!("Z3 not found in PATH; skipping differential SMT benchmark tests");
    });
    false
}

pub(crate) fn run_z3_file(path: &Path, timeout_secs: u64) -> Result<SolverOutcome> {
    let mut child = ProcessCommand::new("z3")
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

pub(crate) fn run_executor_smt_with_timeout(smt: &str, timeout_secs: u64) -> Result<SolverOutcome> {
    let commands = parse(smt).map_err(|err| anyhow!("parse error: {err}"))?;
    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    // Memory backstop via the engine's designed limit (honest
    // `UnknownReason::MemoryLimit`, polled in the solve loop): a future
    // runaway fails ITS test instead of taking the whole machine down
    // (2026-07-10 panic: one divergent solve grew the suite process past
    // 100GB). The measurement is process-wide peak RSS, so the bound is set
    // far above any legitimate suite peak (post-fix suites peak in the MBs);
    // once something trips it, later tests in the same process may also
    // report MemoryLimit — the FIRST failure is the culprit.
    executor.set_memory_limit(Some(8 << 30));

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

    let outputs = executor.execute_all(&commands);
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    if timed_out {
        return Ok(SolverOutcome::Timeout);
    }

    let first_line = outputs
        .map_err(|err| anyhow!("execution error: {err}"))?
        .into_iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "unknown".to_string());
    Ok(SolverOutcome::from_output_line(&first_line))
}

pub(crate) fn run_executor_file_with_timeout(
    path: &Path,
    timeout_secs: u64,
) -> Result<SolverOutcome> {
    let smt = fs::read_to_string(path)
        .with_context(|| format!("failed reading benchmark {}", path.display()))?;
    run_executor_smt_with_timeout(&smt, timeout_secs)
}

pub(crate) fn count_real_declarations(path: &Path) -> Result<usize> {
    let smt = fs::read_to_string(path)
        .with_context(|| format!("failed reading benchmark {}", path.display()))?;
    let commands = parse(&smt).with_context(|| format!("failed parsing {}", path.display()))?;
    Ok(commands.into_iter().filter(is_zero_arity_real_decl).count())
}

fn is_zero_arity_real_decl(command: &SmtCommand) -> bool {
    match command {
        SmtCommand::DeclareConst(_, sort) => is_real_sort(sort),
        SmtCommand::DeclareFun(_, args, sort) => args.is_empty() && is_real_sort(sort),
        _ => false,
    }
}

fn is_real_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Simple(name) if name == "Real")
}

/// Extract two integer values from a get-model constructor expression.
/// Searches for `(ctor_name N1 N2)` in the model output.
pub(crate) fn extract_mkpair_int_values(output: &str, ctor_name: &str) -> (i64, i64) {
    let search = format!("({ctor_name} ");
    let pos = output
        .find(&search)
        .unwrap_or_else(|| panic!("model missing ({ctor_name} ...): {output}"));
    let rest = &output[pos + search.len()..];
    let (val1, remaining) = parse_smt_int(rest, output);
    let remaining = remaining.trim_start();
    let (val2, _) = parse_smt_int(remaining, output);
    (val1, val2)
}

/// Extract two real values from a get-model constructor expression.
/// Searches for `(ctor_name R1 R2)` in the model output.
pub(crate) fn extract_mkpair_real_values(output: &str, ctor_name: &str) -> (f64, f64) {
    let search = format!("({ctor_name} ");
    let pos = output
        .find(&search)
        .unwrap_or_else(|| panic!("model missing ({ctor_name} ...): {output}"));
    let rest = &output[pos + search.len()..];
    let (val1, remaining) = parse_smt_real(rest, output);
    let remaining = remaining.trim_start();
    let (val2, _) = parse_smt_real(remaining, output);
    (val1, val2)
}

/// Parse an SMT-LIB integer value, returning (value, remaining_str).
pub(crate) fn parse_smt_int<'a>(s: &'a str, ctx: &str) -> (i64, &'a str) {
    let s = s.trim_start();
    if let Some(inner) = s.strip_prefix("(- ") {
        let end = inner
            .find(')')
            .unwrap_or_else(|| panic!("unclosed (- in: {ctx}"));
        let num: i64 = inner[..end]
            .trim()
            .parse()
            .unwrap_or_else(|e| panic!("parse int: {e}, in: {ctx}"));
        (-num, &inner[end + 1..])
    } else {
        let end = s.find([')', ' ']).unwrap_or(s.len());
        let num: i64 = s[..end]
            .parse()
            .unwrap_or_else(|e| panic!("parse int '{v}': {e}, in: {ctx}", v = &s[..end]));
        (num, &s[end..])
    }
}

/// Parse an SMT-LIB real value, returning (value, remaining_str).
pub(crate) fn parse_smt_real<'a>(s: &'a str, ctx: &str) -> (f64, &'a str) {
    let s = s.trim_start();
    if let Some(inner) = s.strip_prefix("(- ") {
        let (val, rest) = parse_smt_real_positive(inner, ctx);
        let rest = rest.trim_start();
        let rest = rest.strip_prefix(')').unwrap_or(rest);
        (-val, rest)
    } else {
        parse_smt_real_positive(s, ctx)
    }
}

fn parse_smt_real_positive<'a>(s: &'a str, ctx: &str) -> (f64, &'a str) {
    if let Some(inner) = s.strip_prefix("(/ ") {
        let sp = inner
            .find(' ')
            .unwrap_or_else(|| panic!("malformed rational in: {ctx}"));
        let num: f64 = inner[..sp]
            .parse()
            .unwrap_or_else(|e| panic!("parse real num: {e}, in: {ctx}"));
        let rest = &inner[sp + 1..];
        let end = rest.find(')').unwrap_or(rest.len());
        let den: f64 = rest[..end]
            .parse()
            .unwrap_or_else(|e| panic!("parse real den: {e}, in: {ctx}"));
        let rest = &rest[end..];
        let rest = rest.strip_prefix(')').unwrap_or(rest);
        (num / den, rest)
    } else {
        let end = s.find([')', ' ']).unwrap_or(s.len());
        let num: f64 = s[..end]
            .parse()
            .unwrap_or_else(|e| panic!("parse real '{v}': {e}, in: {ctx}", v = &s[..end]));
        (num, &s[end..])
    }
}

/// Parse and execute SMT-LIB input, returning all output lines joined by newlines.
///
/// Panics on parse or execution errors with diagnostic messages including the
/// SMT input.
pub(crate) fn solve(smt: &str) -> String {
    solve_vec(smt).join("\n")
}

/// Parse and execute SMT-LIB input, returning the raw output line vector.
///
/// Panics on parse or execution errors with diagnostic messages including the
/// SMT input.
pub(crate) fn solve_vec(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
}

/// Like [`solve_vec`], but with fail-closed self-certification (`--self-check`):
/// `sat`/`unsat` are emitted ONLY when AY's own in-tree checker confirms them,
/// and anything unverifiable degrades to `unknown`. Use this to pin behavior
/// that is only sound in the authoritative self-check mode (default mode may
/// still trust the solving machinery).
pub(crate) fn solve_selfcheck_vec(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
}

/// Convenience string form of [`solve_selfcheck_vec`].
pub(crate) fn solve_selfcheck(smt: &str) -> String {
    solve_selfcheck_vec(smt).join("\n")
}

/// Find the first sat/unsat/unknown line in solver output.
pub(crate) fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}
