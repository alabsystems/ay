// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn solve_satisfaction(
    result: &TranslationResult,
    config: &SolverConfig,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    if !config.all_solutions {
        return solve_satisfaction_single(result, config, out);
    }

    // All-solutions mode: iterate with blocking clauses.
    // Reusable buffer avoids cloning declarations on every iteration (#326).
    let mut solutions_found = 0;
    let mut extra_assertions = String::new();
    let mut buf = String::with_capacity(result.declarations.len() + 4096);

    loop {
        buf.clear();
        buf.push_str(&result.declarations);
        buf.push_str(&extra_assertions);
        buf.push_str("(check-sat)\n");
        if !result.smt_var_names.is_empty() {
            let vars = result.smt_var_names.join(" ");
            buf.push_str(&format!("(get-value ({vars}))\n"));
        }
        buf.push_str("(get-info :reason-unknown)\n");

        let output = run_ay(&buf, config)?;
        let (status, lines) = parse_ay_output(&output)?;

        match status {
            CheckSatResult::Sat => {
                let values = parse_get_value(&lines)?;
                let dzn = format_dzn_solution(&values, &result.output_vars);
                write!(out, "{dzn}")?;
                writeln!(out, "----------")?;
                out.flush()?;
                solutions_found += 1;

                // Build blocking clause: negate this assignment
                let mut disjuncts = Vec::new();
                for name in &result.smt_var_names {
                    if let Some(val) = values.get(name) {
                        disjuncts.push(format!("(not (= {name} {val}))"));
                    }
                }
                if disjuncts.is_empty() {
                    // No variables to block — avoid infinite loop
                    break;
                }
                if disjuncts.len() == 1 {
                    extra_assertions.push_str(&format!("(assert {})\n", disjuncts[0]));
                } else {
                    extra_assertions.push_str(&format!("(assert (or {}))\n", disjuncts.join(" ")));
                }
            }
            CheckSatResult::Unsat => {
                if solutions_found == 0 {
                    writeln!(out, "=====UNSATISFIABLE=====")?;
                } else {
                    // All solutions exhausted
                    writeln!(out, "==========")?;
                }
                out.flush()?;
                break;
            }
            CheckSatResult::Unknown => {
                let reason = extract_reason_unknown(&lines);
                writeln!(out, "=====UNKNOWN=====")?;
                if let Some(r) = reason {
                    writeln!(out, "% reason-unknown: {r}")?;
                }
                out.flush()?;
                break;
            }
        }
    }

    Ok(solutions_found)
}

/// Build a `(get-value ...)` command for only the output variables needed for DZN.
///
/// Returns an empty string if no output variables exist.
pub(super) fn build_output_get_value(result: &TranslationResult) -> String {
    if result.output_smt_names.is_empty() {
        return String::new();
    }
    let vars = result.output_smt_names.join(" ");
    format!("(get-value ({vars}))\n")
}

/// Single-solution satisfaction: build lean script, pipe to ay, parse model, print DZN.
///
/// Uses only output variable names in `(get-value ...)` instead of all variables,
/// reducing ay's model extraction work.
fn solve_satisfaction_single(
    result: &TranslationResult,
    config: &SolverConfig,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    let mut buf = String::with_capacity(result.declarations.len() + 256);
    buf.push_str(&result.declarations);
    buf.push_str("(check-sat)\n");
    buf.push_str(&build_output_get_value(result));
    buf.push_str("(get-info :reason-unknown)\n");

    let output = run_ay(&buf, config)?;
    let (status, lines) = parse_ay_output(&output)?;

    match status {
        CheckSatResult::Sat => {
            let values = parse_get_value(&lines)?;
            let dzn = format_dzn_solution(&values, &result.output_vars);
            write!(out, "{dzn}")?;
            writeln!(out, "----------")?;
            out.flush()?;
            Ok(1)
        }
        CheckSatResult::Unsat => {
            writeln!(out, "=====UNSATISFIABLE=====")?;
            out.flush()?;
            Ok(0)
        }
        CheckSatResult::Unknown => {
            let reason = extract_reason_unknown(&lines);
            writeln!(out, "=====UNKNOWN=====")?;
            if let Some(r) = reason {
                writeln!(out, "% reason-unknown: {r}")?;
            }
            out.flush()?;
            Ok(0)
        }
    }
}
