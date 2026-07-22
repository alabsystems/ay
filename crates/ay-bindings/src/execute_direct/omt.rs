// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! OMT executor bridge for direct execution (#6702).
//!
//! When a `AYProgram` contains optimization objectives (maximize/minimize),
//! the Solver-based direct path cannot handle them because `ay_dpll::api::Solver`
//! does not expose objective registration. This bridge lowers the program to
//! SMT-LIB text, parses it into `ay_frontend::Command` values, and runs them
//! through `ay_dpll::Executor` which already supports OMT.

use super::context::catch_execute_stage;
use super::types::ExecuteValueMap;
use super::{ExecuteCounterexample, ExecuteError, ExecuteTypedResult, ModelValue};
use crate::program::AYProgram;

/// Execute an OMT-bearing program through the executor bridge.
///
/// Renders the program to SMT-LIB text, parses via `ay_frontend`, and
/// executes through `ay_dpll::Executor`. Returns typed results compatible
/// with the direct execution API.
pub(crate) fn execute_omt(program: &AYProgram) -> Result<ExecuteTypedResult, ExecuteError> {
    // Render to SMT-LIB text
    let smt_text = program.to_string();

    // Parse into commands
    let commands = ay_frontend::parse(&smt_text)
        .map_err(|e| ExecuteError::ConstraintExecution(format!("OMT parse error: {e}")))?;

    // Execute through ay_dpll::Executor with panic handling
    let exec_result: Result<Vec<String>, String> = catch_execute_stage(
        || {
            let mut executor = ay_dpll::Executor::new();
            let outputs = executor
                .execute_all(&commands)
                .map_err(|e| format!("OMT executor error: {e}"))?;
            Ok(outputs)
        },
        |reason| Err(format!("OMT executor panic: {reason}")),
    );

    let outputs = match exec_result {
        Ok(outputs) => outputs,
        Err(reason) => return Ok(ExecuteTypedResult::Unknown(reason)),
    };

    // Interpret the outputs. The executor returns one output per command that
    // produces output: "sat"/"unsat"/"unknown" for check-sat, model text for
    // get-model, objectives text for get-objectives, etc.
    interpret_executor_outputs(&outputs)
}

/// Interpret executor output strings into an `ExecuteTypedResult`.
///
/// Scans outputs for the last check-sat result and any model/objectives data.
fn interpret_executor_outputs(outputs: &[String]) -> Result<ExecuteTypedResult, ExecuteError> {
    let mut last_check_sat: Option<&str> = None;
    let mut model_values = ExecuteValueMap::default();
    let mut objectives_output: Option<&str> = None;

    for output in outputs {
        let trimmed = output.trim();
        match trimmed {
            "sat" | "unsat" | "unknown" => {
                last_check_sat = Some(trimmed);
            }
            s if s.starts_with("(objectives") => {
                objectives_output = Some(s);
            }
            s if s.starts_with("(model") || s.starts_with("(define-fun") => {
                // Model output — parse variable assignments.
                parse_model_into(&mut model_values, s);
            }
            _ => {
                // Other outputs (get-value, echo, etc.) — check for
                // unknown reason strings.
                if last_check_sat.is_none() && trimmed.starts_with("(error") {
                    return Err(ExecuteError::ConstraintExecution(trimmed.to_string()));
                }
            }
        }
    }

    match last_check_sat {
        Some("unsat") => Ok(ExecuteTypedResult::Verified),
        Some("sat") => {
            // If we have objectives output, store it in the values map
            // so callers can access it.
            if let Some(obj_text) = objectives_output {
                model_values.insert(
                    "__objectives".to_string(),
                    ModelValue::String(obj_text.to_string()),
                );
            }
            Ok(ExecuteTypedResult::Counterexample(
                ExecuteCounterexample::new(model_values, ExecuteValueMap::default()),
            ))
        }
        Some(reason) => Ok(ExecuteTypedResult::Unknown(reason.to_string())),
        None => {
            // No check-sat output found — the program may not have had a check-sat
            Ok(ExecuteTypedResult::Unknown(
                "no check-sat result in OMT output".to_string(),
            ))
        }
    }
}

/// Parse simple model output into the values map.
///
/// Handles the common `(define-fun name () Sort value)` pattern from get-model.
fn parse_model_into(values: &mut ExecuteValueMap<ModelValue>, model_text: &str) {
    // Simple line-by-line parsing of define-fun entries
    for line in model_text.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with("(define-fun ") {
            continue;
        }
        // (define-fun name () Sort value)
        let inner = &trimmed["(define-fun ".len()..];
        let mut parts = inner.splitn(2, ' ');
        let name = match parts.next() {
            Some(n) => n.to_string(),
            None => continue,
        };
        let rest = match parts.next() {
            Some(r) => r,
            None => continue,
        };
        // Skip "() Sort " to get to value
        // Format: () Sort value)
        if let Some(after_parens) = rest.strip_prefix("() ") {
            // Find the sort/value boundary — sort is the next token, value is the rest
            let mut sort_end = 0;
            let mut depth = 0;
            for (i, ch) in after_parens.char_indices() {
                match ch {
                    '(' => depth += 1,
                    ')' if depth > 0 => depth -= 1,
                    ' ' if depth == 0 => {
                        sort_end = i;
                        break;
                    }
                    _ => {}
                }
            }
            if sort_end > 0 {
                let value_str = after_parens[sort_end + 1..].trim_end_matches(')').trim();
                let model_value = parse_model_value(value_str);
                values.insert(name, model_value);
            }
        }
    }
}

/// Parse a single model value string into a ModelValue.
fn parse_model_value(s: &str) -> ModelValue {
    if s == "true" {
        ModelValue::Bool(true)
    } else if s == "false" {
        ModelValue::Bool(false)
    } else if let Ok(n) = s.parse::<i64>() {
        ModelValue::Int(n.into())
    } else if s.starts_with("(- ") {
        // Negative integer: (- N)
        let inner = s
            .strip_prefix("(- ")
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(s);
        if let Ok(n) = inner.parse::<i64>() {
            ModelValue::Int((-n).into())
        } else {
            ModelValue::String(s.to_string())
        }
    } else {
        ModelValue::String(s.to_string())
    }
}
