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
    run_ay_library(script, call_timeout_ms(config, Instant::now()))
}

/// The interrupt timer of one call: the per-call `timeout_ms`, but never past
/// the run's global deadline (`-t` bounds the whole run, not each call).
/// `None` when neither is set: then the call has no time limit at all.
pub(crate) fn call_timeout_ms(config: &SolverConfig, now: Instant) -> Option<u64> {
    let remaining = config.global_deadline.map(|deadline| {
        u64::try_from(deadline.saturating_duration_since(now).as_millis()).unwrap_or(u64::MAX)
    });
    match (config.timeout_ms, remaining) {
        (Some(per_call), Some(remaining)) => Some(per_call.min(remaining)),
        (per_call, remaining) => per_call.or(remaining),
    }
}

/// What a call answers when its time is up before its check-sat.
const UNKNOWN_OUTPUT: &str = "unknown\n";

/// A fresh executor for one FlatZinc call. Its deadline is exactly the
/// caller's: without one, AY adds no safety deadline of its own (by default
/// an untimed check-sat stops at 5 minutes, which ended untimed MiniZinc runs
/// at about 300 s with UNKNOWN). The process that runs `ay flatzinc solve`
/// owns the time limit.
pub(crate) fn flatzinc_executor() -> ay_dpll::Executor {
    let mut executor = ay_dpll::Executor::new();
    executor.set_exact_deadline(true);
    executor
}

/// Run ay via the library API: parse SMT-LIB text, then execute commands
/// directly in-process. Eliminates subprocess spawn overhead (~8ms per call)
/// and pipe serialization.
///
/// When `timeout_ms` is set, a watchdog thread sets the executor's interrupt
/// flag after the deadline, causing check-sat to return `unknown`.
///
/// The deadline also holds outside check-sat: a call whose time is up
/// before its check-sat starts answers `unknown` without parsing or
/// declaring the rest of the script. Declaring a large model is not
/// interruptible and took longer than the whole `-t` on MiniZinc
/// `nside/EASY_1000_100` (2026-11-19: `-t 30000` still running at 60 s).
fn run_ay_library(script: &str, timeout_ms: Option<u64>) -> Result<String, SolverError> {
    let deadline = timeout_ms.map(|ms| Instant::now() + Duration::from_millis(ms));
    let expired = || deadline.is_some_and(|deadline| Instant::now() >= deadline);
    if expired() {
        return Ok(UNKNOWN_OUTPUT.to_string());
    }
    let commands =
        ay_frontend::parse(script).map_err(|e| SolverError::SolverError(format!("parse: {e}")))?;
    let mut executor = flatzinc_executor();

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

    let mut outputs: Vec<String> = Vec::new();
    let mut checked = false;
    for cmd in &commands {
        let is_check = matches!(
            cmd,
            ay_frontend::Command::CheckSat | ay_frontend::Command::CheckSatAssuming(_)
        );
        // Out of time before the check-sat: `unknown`, as the check-sat
        // would answer. After an `unknown` the rest (get-value) is skipped;
        // after `sat` it runs, since the caller reads the values.
        if expired() {
            if !checked {
                outputs = vec![UNKNOWN_OUTPUT.trim_end().to_string()];
                break;
            }
            if outputs
                .first()
                .is_some_and(|status| status.trim() == "unknown")
            {
                break;
            }
        }
        checked |= is_check;
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
