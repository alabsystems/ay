// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// DZN output formatting for FlatZinc solution display

use ay_core::kani_compat::DetHashMap as HashMap;
use std::fmt::Write;

use crate::translate::OutputVarInfo;

/// Format a solution in DZN format from SMT variable assignments.
///
/// `values` maps SMT variable names to their string values
/// (e.g., "x" → "5", "q_1" → "3").
pub fn format_dzn_solution(
    values: &HashMap<String, String>,
    output_vars: &[OutputVarInfo],
) -> String {
    let mut dzn = String::new();
    for var in output_vars {
        if var.is_set {
            format_set_var(&mut dzn, var, values);
        } else if var.is_array {
            format_array_var(&mut dzn, var, values);
        } else {
            format_scalar_var(&mut dzn, var, values);
        }
    }
    dzn
}

fn format_scalar_var(dzn: &mut String, var: &OutputVarInfo, values: &HashMap<String, String>) {
    let val = values
        .get(&var.smt_names[0])
        .map(String::as_str)
        .unwrap_or("_");
    let formatted = format_value(val, var.is_bool);
    let _ = writeln!(dzn, "{} = {};", var.fzn_name, formatted);
}

/// Format a set variable: reconstruct `{1, 3, 5}` from boolean bit assignments.
/// Bit i is true iff element `lo + i` is in the set.
fn format_set_var(dzn: &mut String, var: &OutputVarInfo, values: &HashMap<String, String>) {
    let (lo, _hi) = var.set_range.unwrap_or((0, var.smt_names.len() as i64 - 1));
    let elements: Vec<String> = var
        .smt_names
        .iter()
        .enumerate()
        .filter(|(_i, name)| values.get(*name).map(|v| v == "true").unwrap_or(false))
        .map(|(i, _name)| (lo + i as i64).to_string())
        .collect();
    let _ = writeln!(dzn, "{} = {{{}}};", var.fzn_name, elements.join(", "));
}

fn format_array_var(dzn: &mut String, var: &OutputVarInfo, values: &HashMap<String, String>) {
    let (lo, hi) = var.array_range.unwrap_or((1, var.smt_names.len() as i64));
    let vals: Vec<String> = var
        .smt_names
        .iter()
        .map(|n| {
            let raw = values.get(n).map(String::as_str).unwrap_or("_");
            format_value(raw, var.is_bool)
        })
        .collect();
    let _ = writeln!(
        dzn,
        "{} = array1d({}..{}, [{}]);",
        var.fzn_name,
        lo,
        hi,
        vals.join(", ")
    );
}

/// Format a raw SMT value for DZN output.
fn format_value(raw: &str, is_bool: bool) -> String {
    if is_bool {
        match raw {
            "true" => "true".into(),
            "false" => "false".into(),
            other => other.into(),
        }
    } else {
        // SMT-LIB negative integers are `(- N)`, convert to `-N`
        if let Some(inner) = raw.strip_prefix("(- ") {
            if let Some(num) = inner.strip_suffix(')') {
                return format!("-{num}");
            }
        }
        raw.into()
    }
}

#[cfg(test)]
#[path = "output_tests.rs"]
mod tests;
