// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Run ay on the given SMT-LIB script via the in-process library API.
///
/// Parses the SMT-LIB text and executes commands directly in-process,
/// eliminating subprocess spawn overhead (~8ms per call) and pipe
/// serialization. When `timeout_ms` is set, a watchdog thread sets the
/// executor's interrupt flag after the deadline, causing check-sat to
/// return `unknown`.
pub(crate) fn run_ay(script: &str, config: &SolverConfig) -> Result<String, SolverError> {
    run_ay_library(script, config.timeout_ms)
}

/// Run ay via the library API: parse SMT-LIB text, then execute commands
/// directly in-process. Eliminates subprocess spawn overhead (~8ms per call)
/// and pipe serialization.
///
/// When `timeout_ms` is set, a watchdog thread sets the executor's interrupt
/// flag after the deadline, causing check-sat to return `unknown`.
fn run_ay_library(script: &str, timeout_ms: Option<u64>) -> Result<String, SolverError> {
    let commands =
        ay_frontend::parse(script).map_err(|e| SolverError::SolverError(format!("parse: {e}")))?;
    let mut executor = ay_dpll::Executor::new();

    // Wire interrupt flag for cooperative timeout (#5931).
    // Timer thread uses park_timeout so it can be woken early when the
    // executor finishes, avoiding orphaned sleeping threads (#6231).
    let timer_handle = if let Some(ms) = timeout_ms {
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(flag.clone());
        let cancelled = Arc::new(AtomicBool::new(false));
        let cancel_flag = cancelled.clone();
        let handle = std::thread::spawn(move || {
            std::thread::park_timeout(Duration::from_millis(ms));
            if !cancel_flag.load(Ordering::Acquire) {
                flag.store(true, Ordering::SeqCst);
            }
        });
        Some((handle, cancelled))
    } else {
        None
    };

    let mut outputs = Vec::new();
    for cmd in &commands {
        match executor.execute(cmd) {
            Ok(Some(out)) => outputs.push(out),
            Ok(None) => {}
            Err(e) => {
                // Non-fatal after check-sat: get-info :reason-unknown may
                // fail when the result was sat/unsat (not unknown).
                // The critical outputs (check-sat, get-value) already captured.
                if outputs.is_empty() {
                    // Cancel timer before returning error.
                    if let Some((handle, cancelled)) = timer_handle {
                        cancelled.store(true, Ordering::Release);
                        handle.thread().unpark();
                    }
                    return Err(SolverError::SolverError(format!("{e}")));
                }
            }
        }
    }

    // Cancel the timer early — executor is done.
    if let Some((handle, cancelled)) = timer_handle {
        cancelled.store(true, Ordering::Release);
        handle.thread().unpark();
    }
    if outputs.is_empty() {
        Ok(String::new())
    } else {
        Ok(outputs.join("\n") + "\n")
    }
}

/// Extract the reason for `unknown` from ay's `(get-info :reason-unknown)` response.
///
/// Scans remaining output lines for `(:reason-unknown "...")` and returns the
/// reason string (e.g., "timeout", "incomplete"). Returns `None` if no
/// reason-unknown response is found.
pub(crate) fn extract_reason_unknown(lines: &[String]) -> Option<String> {
    for line in lines {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("(:reason-unknown") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_suffix(')') {
                let reason = inner.trim().trim_matches('"');
                if !reason.is_empty() {
                    return Some(reason.to_string());
                }
            }
        }
    }
    None
}

/// Parse ay output into check-sat result and remaining lines.
pub(crate) fn parse_ay_output(output: &str) -> Result<(CheckSatResult, Vec<String>), SolverError> {
    let mut lines: Vec<String> = output.lines().map(String::from).collect();
    if lines.is_empty() {
        return Err(SolverError::EmptyOutput);
    }

    let status_line = lines.remove(0).trim().to_string();
    let status = match status_line.as_str() {
        "sat" => CheckSatResult::Sat,
        "unsat" => CheckSatResult::Unsat,
        "unknown" => CheckSatResult::Unknown,
        other => return Err(SolverError::UnexpectedOutput(other.to_string())),
    };

    Ok((status, lines))
}
