// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLC output parsing functions.
//!
//! Parses TLC's textual stdout/stderr output into structured
//! [`TlcOutcome`] and [`TlcViolation`] values.
//!
//! Extracted from `lib.rs` for code health (#5970).

use super::{TlcOutcome, TlcViolation};

pub fn parse_tlc_outcome(stdout: &str, stderr: &str, exit_code: Option<i32>) -> TlcOutcome {
    let combined = if stderr.is_empty() {
        stdout
    } else if stdout.is_empty() {
        stderr
    } else {
        // Avoid allocating for the fast path by only using stderr/stdout checks below.
        ""
    };

    let text = if combined.is_empty() {
        // Fall back to allocation only when both are present.
        let mut s = String::with_capacity(stdout.len() + 1 + stderr.len());
        s.push_str(stdout);
        if !s.ends_with('\n') {
            s.push('\n');
        }
        s.push_str(stderr);
        s
    } else {
        combined.to_string()
    };

    // Success marker.
    if text.contains("Model checking completed. No error has been found.") {
        return TlcOutcome::NoError;
    }

    // Common failure markers (ordered by specificity).

    // Deadlock
    if text.contains("Error: Deadlock reached.") || text.contains("TLC_DEADLOCK") {
        return TlcOutcome::Deadlock;
    }

    // Invariant violation
    if text.contains("is violated.") && text.contains("Error: Invariant") {
        return TlcOutcome::InvariantViolation {
            name: extract_invariant_name(&text),
        };
    }

    // Assertion failure
    if text.contains("Error: The following assertion failed")
        || text.contains("Assertion failed")
        || text.contains("ASSERT")
    {
        return TlcOutcome::AssertionFailure {
            message: extract_assertion_message(&text),
        };
    }

    // Liveness/temporal properties
    if text.contains("Temporal properties were violated")
        || text.contains("liveness properties were violated")
        || text.contains("stuttering")
    {
        return TlcOutcome::LivenessViolation;
    }

    // State space exhaustion
    if text.contains("Out of memory")
        || text.contains("too many states")
        || text.contains("state space too large")
        || text.contains("SANY_STATE_SPACE")
    {
        return TlcOutcome::StateSpaceExhausted;
    }

    // Config file errors
    if text.contains("CFG_PARSE")
        || text.contains("Error reading configuration file")
        || text.contains("Configuration file error")
        || text.contains(".cfg")
            && (text.contains("error") || text.contains("Error") || text.contains("cannot"))
    {
        return TlcOutcome::ConfigError;
    }

    // Type errors
    if text.contains("TLC_TYPE")
        || text.contains("was not in the domain")
        || text.contains("is not a")
        || text.contains("type mismatch")
        || text.contains("Type mismatch")
    {
        return TlcOutcome::TypeError;
    }

    // Parse errors
    if text.contains("TLA_PARSE")
        || text.contains("Parse error")
        || text.contains("TLC parsing")
        || text.contains("Syntax error")
        || text.contains("SANY error")
    {
        return TlcOutcome::ParseError;
    }

    if exit_code != Some(0) {
        return TlcOutcome::ExecutionFailed { exit_code };
    }

    TlcOutcome::Unknown { exit_code }
}

/// Extract a structured violation from TLC output.
///
/// This provides more detailed error information including the
/// counterexample trace when available.
pub fn extract_violation(
    stdout: &str,
    stderr: &str,
    exit_code: Option<i32>,
) -> Option<TlcViolation> {
    let outcome = parse_tlc_outcome(stdout, stderr, exit_code);
    if outcome.is_success() {
        return None;
    }

    let code = outcome.error_code()?;
    let text = format!("{stdout}\n{stderr}");

    let (property_name, message) = match &outcome {
        TlcOutcome::Deadlock => (
            None,
            "Deadlock reached: no enabled transitions from current state".to_string(),
        ),
        TlcOutcome::InvariantViolation { name } => {
            let msg = name.as_ref().map_or_else(
                || "Invariant violation".to_string(),
                |n| format!("Invariant {n} is violated"),
            );
            (name.clone(), msg)
        }
        TlcOutcome::LivenessViolation => (None, "Temporal/liveness property violated".to_string()),
        TlcOutcome::AssertionFailure { message } => {
            let msg = message
                .clone()
                .unwrap_or_else(|| "Assertion failed".to_string());
            (None, msg)
        }
        TlcOutcome::TypeError => (None, "Type error in specification".to_string()),
        TlcOutcome::ParseError => (None, "Parse error in specification".to_string()),
        TlcOutcome::ConfigError => (None, "Configuration file error".to_string()),
        TlcOutcome::StateSpaceExhausted => (None, "State space exhausted".to_string()),
        TlcOutcome::ExecutionFailed { exit_code } => {
            let msg = exit_code
                .map(|c| format!("TLC execution failed with exit code {c}"))
                .unwrap_or_else(|| "TLC execution failed".to_string());
            (None, msg)
        }
        TlcOutcome::Unknown { .. } => (None, "Unknown TLC error".to_string()),
        TlcOutcome::NoError => return None,
    };

    let trace = extract_trace(&text);
    let suggestion = suggest_fix(&outcome, &text);

    Some(TlcViolation {
        code,
        message,
        property_name,
        trace,
        suggestion,
    })
}

pub(crate) fn extract_assertion_message(text: &str) -> Option<String> {
    // Look for assertion message patterns
    for line in text.lines() {
        if line.contains("Assertion failed") || line.contains("ASSERT") {
            // Extract the relevant part
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                return Some(trimmed.to_string());
            }
        }
    }
    None
}

/// Extract the counterexample trace from TLC output.
pub(crate) fn extract_trace(text: &str) -> Option<Vec<String>> {
    let mut trace = Vec::new();
    let mut in_trace = false;
    let mut current_state = String::new();

    for line in text.lines() {
        // TLC trace typically starts with "State 1:" or similar
        if line.starts_with("State ") && line.contains(':') {
            if !current_state.is_empty() {
                trace.push(current_state.trim().to_string());
            }
            in_trace = true;
            current_state = line.to_string();
        } else if in_trace {
            // Continue accumulating state info
            if line.starts_with('/') && line.contains('\\') {
                // This looks like a variable assignment
                current_state.push('\n');
                current_state.push_str(line);
            } else if line.trim().is_empty() && !current_state.is_empty() {
                // End of state
                trace.push(current_state.trim().to_string());
                current_state = String::new();
            } else if !line.trim().is_empty()
                && !line.contains("Error")
                && !line.contains("Finished")
            {
                current_state.push('\n');
                current_state.push_str(line);
            }
        }
    }

    // Don't forget the last state
    if !current_state.is_empty() {
        trace.push(current_state.trim().to_string());
    }

    if trace.is_empty() {
        None
    } else {
        Some(trace)
    }
}

/// Suggest a fix based on the error type.
pub(crate) fn suggest_fix(outcome: &TlcOutcome, text: &str) -> Option<String> {
    match outcome {
        TlcOutcome::Deadlock => {
            if text.contains("state =") && (text.contains("SAT") || text.contains("UNSAT")) {
                Some(
                    "This may be an expected terminal state. Consider adding a TERMINAL \
                     declaration in your config or adding a self-loop in terminal states."
                        .to_string(),
                )
            } else {
                Some(
                    "Check that all states have at least one enabled transition, \
                     or mark terminal states explicitly."
                        .to_string(),
                )
            }
        }
        TlcOutcome::InvariantViolation { name } => {
            let inv_name = name.as_deref().unwrap_or("the invariant");
            Some(format!(
                "Review the counterexample trace to understand how {inv_name} was violated. \
                 Check preconditions and action guards."
            ))
        }
        TlcOutcome::TypeError => Some(
            "Check that all operators receive arguments of the expected type. \
             Verify CONSTANT declarations match their usage."
                .to_string(),
        ),
        TlcOutcome::ParseError => Some(
            "Check TLA+ syntax. Common issues: missing EXTENDS, unbalanced delimiters, \
             invalid operator names."
                .to_string(),
        ),
        TlcOutcome::ConfigError => Some(
            "Check config file syntax. Ensure CONSTANTS, SPECIFICATION, and INVARIANT \
             declarations are properly formatted."
                .to_string(),
        ),
        TlcOutcome::StateSpaceExhausted => Some(
            "Reduce state space by using symmetry sets, constraining CONSTANTS, \
             or adding state constraints with CONSTRAINT."
                .to_string(),
        ),
        _ => None,
    }
}

pub(crate) fn extract_invariant_name(text: &str) -> Option<String> {
    // Typical TLC line:
    // "Error: Invariant TypeInvariant is violated."
    let needle_start = "Error: Invariant ";
    let needle_end = " is violated.";
    let start = text.find(needle_start)? + needle_start.len();
    let rest = &text[start..];
    let end = rest.find(needle_end)?;
    let name = rest[..end].trim();
    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
}
