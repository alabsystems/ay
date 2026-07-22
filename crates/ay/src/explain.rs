// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Human-readable explanation of solver results.
//!
//! When invoked via `--explain`, this module translates solver output into
//! natural language that a non-expert can understand. For SAT results, it
//! shows how each constraint is satisfied by the model values. For UNSAT
//! results, it identifies which constraints conflict and explains why.
//!
//! Currently supports QF_LIA (integer arithmetic) explanations; other
//! logics produce a generic summary.

use ay_dpll::Executor;
use ay_frontend::Command;

/// Generate a human-readable explanation of the solve result.
///
/// Called after check-sat completes. Uses the executor to retrieve
/// assertions and model/core information, then formats a natural
/// language explanation printed to stdout.
pub(crate) fn explain_result(executor: &mut Executor) {
    let is_unsat = executor.last_result_is_unsat();
    let is_sat = executor.last_result_is_sat();
    let is_unknown = executor.get_reason_unknown().is_some();

    if is_unknown {
        explain_unknown(executor);
    } else if is_unsat {
        explain_unsat(executor);
    } else if is_sat {
        explain_sat(executor);
    } else {
        // No check-sat result is available — the script either never ran
        // check-sat, or mutated the assertion stack afterwards (e.g. a
        // trailing `(pop)`), which invalidates the cached result. Previously
        // this fell through to the SAT branch and printed "The formula is
        // satisfiable, but model retrieval failed" even when the printed
        // verdict was `unsat` — a misleading artifact (seed-981 diagnosis).
        safe_println!();
        safe_println!("=== Explanation ===");
        safe_println!();
        safe_println!(
            "No check-sat result is available to explain: the assertion stack \
             changed after the last (check-sat) (e.g. a trailing (pop)), or \
             (check-sat) was never run."
        );
    }
}

/// Explain a SAT result by showing how each assertion is satisfied.
///
/// MVP output (#8693) emits three lines per assertion so the user can audit the
/// model without mental arithmetic:
///
/// ```text
///   assertion: <pretty-printed>
///   substituted: <with model values>
///   evaluates to: true
/// ```
fn explain_sat(executor: &mut Executor) {
    safe_println!();
    safe_println!("=== Explanation (SAT) ===");
    safe_println!();

    // Get the model text via the executor
    let model_text = match executor.execute(&Command::GetModel) {
        Ok(Some(text)) => text,
        _ => {
            safe_println!("The formula is satisfiable, but no model is available.");
            return;
        }
    };

    if model_text.contains("error") {
        safe_println!("The formula is satisfiable, but model retrieval failed.");
        return;
    }

    // Parse variable assignments from the model text
    let assignments = parse_model_assignments(&model_text);

    if assignments.is_empty() {
        safe_println!("The formula is satisfiable (no variables to display).");
        return;
    }

    // Display the solution
    safe_println!("Solution found:");
    safe_println!();
    for (name, value) in &assignments {
        safe_println!("  {name} = {value}");
    }

    // Get assertions text
    let assertions_text = match executor.execute(&Command::GetAssertions) {
        Ok(Some(text)) => text,
        _ => {
            safe_println!();
            safe_println!("All constraints satisfied.");
            return;
        }
    };

    let assertion_strs = parse_assertion_list(&assertions_text);

    if assertion_strs.is_empty() {
        safe_println!();
        safe_println!("All constraints satisfied.");
        return;
    }

    safe_println!();
    safe_println!("Constraint verification:");
    for (i, assertion) in assertion_strs.iter().enumerate() {
        let pretty = assertion.trim();
        let substituted = substitute_values(assertion, &assignments);
        let (substituted_expr, verdict) = split_substituted(&substituted);
        safe_println!("  {}. assertion: {pretty}", i + 1);
        safe_println!("     substituted: {substituted_expr}");
        safe_println!("     evaluates to: {verdict}");
    }
    safe_println!();
    safe_println!("All {} constraint(s) satisfied.", assertion_strs.len());
}

/// Split the output of [`substitute_values`] into the pure s-expression (with
/// model values swapped in) and a short verdict suitable for `evaluates to:`.
///
/// `substitute_values` produces `"<sexpr>  [= <verdict>]"` when evaluation
/// succeeds. This helper extracts the two halves, mapping evaluator strings
/// like `"8 = 8, satisfied"`, `"all sub-constraints satisfied"`, or a bare
/// integer onto a boolean-style `"true"` / `"false (<reason>)"` verdict. If the
/// expression could not be evaluated, we emit `"<unknown>"` rather than fake a
/// verdict — the substituted expression is still printed so the user can check
/// it manually.
fn split_substituted(substituted: &str) -> (String, String) {
    if let Some(idx) = substituted.find("  [= ") {
        let expr = substituted[..idx].to_string();
        // Strip the trailing `]` from the verdict block.
        let raw_verdict = substituted[idx + 5..].trim_end_matches(']').trim();
        let verdict = summarize_verdict(raw_verdict);
        (expr, verdict)
    } else {
        (substituted.to_string(), "<unknown>".to_string())
    }
}

/// Map a raw evaluator verdict string onto `"true"` / `"false (<reason>)"`.
fn summarize_verdict(raw: &str) -> String {
    let trimmed = raw.trim();
    if trimmed.contains("VIOLATED") {
        format!("false ({trimmed})")
    } else if trimmed.contains("satisfied") {
        "true".to_string()
    } else if trimmed == "true" || trimmed == "false" {
        trimmed.to_string()
    } else {
        // Bare numeric evaluation of an arithmetic sub-expression — not a
        // boolean. Surface the computed value; the caller can visually verify.
        trimmed.to_string()
    }
}

/// Explain an UNSAT result by showing which constraints conflict.
///
/// When `(:produce-unsat-cores true)` has been set and at least one named
/// assertion participated, the executor returns an s-expression list of core
/// names via `GetUnsatCore`. We surface that list verbatim so the user sees
/// the solver's minimal contradiction set. Otherwise we emit a short English
/// note and fall back to listing all assertions — preserving behavior for
/// inputs that did not opt in to named cores.
fn explain_unsat(executor: &mut Executor) {
    safe_println!();
    safe_println!("=== Explanation (UNSAT) ===");
    safe_println!();
    safe_println!("No assignment can satisfy these constraints simultaneously.");

    // Attempt to retrieve an unsat core. `GetUnsatCore` succeeds only when
    // `:produce-unsat-cores true` was set before check-sat; otherwise it
    // returns an error s-expression which we ignore.
    let core_text = match executor.execute(&Command::GetUnsatCore) {
        Ok(Some(text)) if !text.contains("error") => Some(text),
        _ => None,
    };

    if let Some(core) = &core_text {
        let core_names = parse_core_names(core);
        safe_println!();
        if core_names.is_empty() {
            safe_println!("Unsat core: {}", core.trim());
        } else {
            safe_println!(
                "Key conflicting constraints (unsat core, {} named assertion(s)):",
                core_names.len()
            );
            for (i, name) in core_names.iter().enumerate() {
                safe_println!("  {}. {name}", i + 1);
            }
        }
    }

    // Try to get assertions for additional context. When a core was unavailable
    // this is the only view; when it was available, it still helps to show the
    // full assertion list so the user can compare.
    let assertions_text = match executor.execute(&Command::GetAssertions) {
        Ok(Some(text)) => text,
        _ => {
            if core_text.is_none() {
                safe_println!();
                safe_println!("No satisfying assignment exists (unsat core not computed).");
            }
            return;
        }
    };

    let assertion_strs = parse_assertion_list(&assertions_text);
    if assertion_strs.is_empty() {
        if core_text.is_none() {
            safe_println!();
            safe_println!("No satisfying assignment exists (unsat core not computed).");
        }
        return;
    }

    safe_println!();
    if core_text.is_some() {
        safe_println!("All {} assertion(s):", assertion_strs.len());
    } else {
        safe_println!("No satisfying assignment exists (unsat core not computed).");
        safe_println!(
            "The following {} constraints cannot all be true at once:",
            assertion_strs.len()
        );
    }
    for (i, assertion) in assertion_strs.iter().enumerate() {
        safe_println!("  {}. {}", i + 1, assertion.trim());
    }

    // Generate a natural language summary of why they conflict
    if let Some(conflict_summary) = summarize_conflict(&assertion_strs) {
        safe_println!();
        safe_println!("Conflict: {conflict_summary}");
    }
}

/// Parse the names from an unsat-core s-expression.
///
/// The executor emits `(n1 n2 ...)` where each element is a bare symbol or a
/// `|quoted symbol|` form. Returns an empty vector for `()` or malformed
/// input — callers fall back to printing the raw string in that case.
fn parse_core_names(text: &str) -> Vec<String> {
    let trimmed = text.trim();
    if trimmed.is_empty() || trimmed == "()" {
        return Vec::new();
    }
    let inner = match trimmed.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        Some(s) => s.trim(),
        None => return Vec::new(),
    };

    let mut names = Vec::new();
    let mut current = String::new();
    let mut in_quoted = false;
    for ch in inner.chars() {
        if in_quoted {
            if ch == '|' {
                in_quoted = false;
                if !current.is_empty() {
                    names.push(current.clone());
                    current.clear();
                }
            } else {
                current.push(ch);
            }
        } else if ch == '|' {
            if !current.is_empty() {
                names.push(current.clone());
                current.clear();
            }
            in_quoted = true;
        } else if ch.is_whitespace() {
            if !current.is_empty() {
                names.push(current.clone());
                current.clear();
            }
        } else {
            current.push(ch);
        }
    }
    if !current.is_empty() {
        names.push(current);
    }
    names
}

/// Explain an Unknown result.
fn explain_unknown(executor: &Executor) {
    safe_println!();
    safe_println!("=== Explanation (Unknown) ===");
    safe_println!();
    if let Some(reason) = executor.get_reason_unknown() {
        safe_println!("The solver could not determine satisfiability. Reason: {reason}");
    } else {
        safe_println!("The solver could not determine satisfiability.");
    }
}

/// Parse variable assignments from SMT-LIB model text.
///
/// Model text looks like:
/// ```text
/// (model
///   (define-fun x () Int 5)
///   (define-fun y () Int 3)
/// )
/// ```
///
/// Returns a list of (name, value) pairs.
fn parse_model_assignments(model_text: &str) -> Vec<(String, String)> {
    let mut assignments = Vec::new();

    for line in model_text.lines() {
        let trimmed = line.trim();
        // Match "(define-fun <name> () <sort> <value>)" for constants
        if let Some(rest) = trimmed.strip_prefix("(define-fun ") {
            // Parse: name () sort value)
            let parts: Vec<&str> = rest.splitn(2, " () ").collect();
            if parts.len() == 2 {
                let name = parts[0].trim();
                // The remainder is "sort value)" plus the outer define-fun ')'.
                // Strip only that single trailing delimiter so nested SMT-LIB
                // values like "(- 5)" keep their own closing parenthesis.
                let sort_and_value = parts[1]
                    .trim()
                    .strip_suffix(')')
                    .unwrap_or(parts[1].trim())
                    .trim();
                // Find the space separating sort from value
                if let Some(space_idx) = sort_and_value.find(' ') {
                    let value = sort_and_value[space_idx + 1..].trim();
                    // Handle negative numbers like "(- 5)"
                    let formatted_value = format_model_value(value);
                    assignments.push((name.to_string(), formatted_value));
                }
            }
        }
    }

    assignments
}

/// Format a model value for display, handling SMT-LIB encoding.
///
/// Converts `(- 5)` to `-5`, keeps `5` as `5`, etc.
fn format_model_value(value: &str) -> String {
    let trimmed = value.trim();
    if let Some(inner) = trimmed.strip_prefix("(- ") {
        if let Some(num) = inner.strip_suffix(')') {
            return format!("-{}", num.trim());
        }
    }
    // Handle rational numbers like (/ 1 3)
    if let Some(inner) = trimmed.strip_prefix("(/ ") {
        if let Some(rest) = inner.strip_suffix(')') {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            if parts.len() == 2 {
                return format!("{}/{}", parts[0], parts[1]);
            }
        }
    }
    trimmed.to_string()
}

/// Parse a list of assertions from SMT-LIB `(get-assertions)` output.
///
/// The output is a single s-expression like:
/// ```text
/// ((= (+ x y) 8)
///  (> x y)
///  (> x 0))
/// ```
///
/// Returns individual assertion strings.
fn parse_assertion_list(text: &str) -> Vec<String> {
    let trimmed = text.trim();
    if trimmed == "()" || trimmed.is_empty() {
        return Vec::new();
    }

    // Strip outer parens
    let inner = if trimmed.starts_with('(') && trimmed.ends_with(')') {
        &trimmed[1..trimmed.len() - 1]
    } else {
        trimmed
    };

    // Parse individual s-expressions by tracking paren depth
    let mut assertions = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();

    for ch in inner.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth -= 1;
                current.push(ch);
                if depth == 0 {
                    let s = current.trim().to_string();
                    if !s.is_empty() {
                        assertions.push(s);
                    }
                    current.clear();
                }
            }
            c if depth == 0 && c.is_whitespace() => {
                // Between top-level expressions, skip whitespace
                let s = current.trim().to_string();
                if !s.is_empty() {
                    assertions.push(s);
                    current.clear();
                }
            }
            _ => {
                current.push(ch);
            }
        }
    }

    // Handle any trailing non-parenthesized content
    let remaining = current.trim().to_string();
    if !remaining.is_empty() {
        assertions.push(remaining);
    }

    assertions
}

/// Substitute known variable values into an assertion string.
///
/// For `(= (+ x y) 8)` with x=5, y=3, produces something like:
/// `(= (+ 5 3) 8) [= 8 = 8, satisfied]`
fn substitute_values(assertion: &str, assignments: &[(String, String)]) -> String {
    let mut result = assertion.to_string();
    for (name, value) in assignments {
        // Replace variable names with their values, being careful about word boundaries
        // Use a simple approach: replace " name " and "(name " and " name)" patterns
        result = replace_var_in_sexp(&result, name, value);
    }

    // Try to evaluate simple arithmetic for a friendly display
    if let Some(evaluated) = try_evaluate_sexp(&result) {
        format!("{result}  [= {evaluated}]")
    } else {
        result
    }
}

/// Replace a variable name with its value in an s-expression.
///
/// Careful to only replace the variable name when it appears as a token,
/// not as part of a longer name.
fn replace_var_in_sexp(sexp: &str, var_name: &str, value: &str) -> String {
    let mut result = String::with_capacity(sexp.len());
    let chars: Vec<char> = sexp.chars().collect();
    let var_chars: Vec<char> = var_name.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        // Check if we're at the start of the variable name
        if i + var_chars.len() <= chars.len() && chars[i..i + var_chars.len()] == var_chars[..] {
            // Check that the character before (if any) is a delimiter
            let before_ok = i == 0 || is_sexp_delimiter(chars[i - 1]);
            // Check that the character after (if any) is a delimiter
            let after_ok =
                i + var_chars.len() >= chars.len() || is_sexp_delimiter(chars[i + var_chars.len()]);

            if before_ok && after_ok {
                result.push_str(value);
                i += var_chars.len();
                continue;
            }
        }
        result.push(chars[i]);
        i += 1;
    }

    result
}

/// Check if a character is an s-expression delimiter.
fn is_sexp_delimiter(c: char) -> bool {
    c == '(' || c == ')' || c.is_whitespace()
}

/// Try to evaluate a simple s-expression containing only integer arithmetic.
///
/// Handles: +, -, *, =, <, >, <=, >= with integer constants.
/// Returns None if the expression is too complex.
fn try_evaluate_sexp(sexp: &str) -> Option<String> {
    let trimmed = sexp.trim();

    // Base case: a number
    if let Ok(n) = trimmed.parse::<i64>() {
        return Some(n.to_string());
    }

    // Handle negative: (- N)
    if let Some(inner) = trimmed.strip_prefix("(- ") {
        if let Some(arg) = inner.strip_suffix(')') {
            if let Some(val) = try_evaluate_sexp(arg.trim()) {
                if let Ok(n) = val.parse::<i64>() {
                    return Some((-n).to_string());
                }
            }
        }
    }

    // Handle (op args...)
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return None;
    }

    let inner = &trimmed[1..trimmed.len() - 1];
    let (op, args_str) = inner.split_once(char::is_whitespace)?;
    let args = parse_sexp_args(args_str.trim());

    match op {
        "+" => {
            let mut sum: i64 = 0;
            for arg in &args {
                sum = sum.checked_add(try_evaluate_sexp(arg)?.parse::<i64>().ok()?)?;
            }
            Some(sum.to_string())
        }
        "-" if args.len() == 2 => {
            let a = try_evaluate_sexp(&args[0])?.parse::<i64>().ok()?;
            let b = try_evaluate_sexp(&args[1])?.parse::<i64>().ok()?;
            Some(a.checked_sub(b)?.to_string())
        }
        "*" => {
            let mut product: i64 = 1;
            for arg in &args {
                product = product.checked_mul(try_evaluate_sexp(arg)?.parse::<i64>().ok()?)?;
            }
            Some(product.to_string())
        }
        "=" if args.len() == 2 => {
            let a = try_evaluate_sexp(&args[0])?;
            let b = try_evaluate_sexp(&args[1])?;
            if a == b {
                Some(format!("{a} = {b}, satisfied"))
            } else {
                Some(format!("{a} != {b}, VIOLATED"))
            }
        }
        ">" if args.len() == 2 => {
            let a = try_evaluate_sexp(&args[0])?.parse::<i64>().ok()?;
            let b = try_evaluate_sexp(&args[1])?.parse::<i64>().ok()?;
            if a > b {
                Some(format!("{a} > {b}, satisfied"))
            } else {
                Some(format!("{a} <= {b}, VIOLATED"))
            }
        }
        ">=" if args.len() == 2 => {
            let a = try_evaluate_sexp(&args[0])?.parse::<i64>().ok()?;
            let b = try_evaluate_sexp(&args[1])?.parse::<i64>().ok()?;
            if a >= b {
                Some(format!("{a} >= {b}, satisfied"))
            } else {
                Some(format!("{a} < {b}, VIOLATED"))
            }
        }
        "<" if args.len() == 2 => {
            let a = try_evaluate_sexp(&args[0])?.parse::<i64>().ok()?;
            let b = try_evaluate_sexp(&args[1])?.parse::<i64>().ok()?;
            if a < b {
                Some(format!("{a} < {b}, satisfied"))
            } else {
                Some(format!("{a} >= {b}, VIOLATED"))
            }
        }
        "<=" if args.len() == 2 => {
            let a = try_evaluate_sexp(&args[0])?.parse::<i64>().ok()?;
            let b = try_evaluate_sexp(&args[1])?.parse::<i64>().ok()?;
            if a <= b {
                Some(format!("{a} <= {b}, satisfied"))
            } else {
                Some(format!("{a} > {b}, VIOLATED"))
            }
        }
        "not" if args.len() == 1 => {
            let inner_val = try_evaluate_sexp(&args[0])?;
            if inner_val.contains("satisfied") {
                Some(inner_val.replace("satisfied", "VIOLATED"))
            } else if inner_val.contains("VIOLATED") {
                Some(inner_val.replace("VIOLATED", "satisfied"))
            } else {
                Some(format!("not({inner_val})"))
            }
        }
        "and" => {
            let mut all_satisfied = true;
            let mut parts = Vec::new();
            for arg in &args {
                let val = try_evaluate_sexp(arg)?;
                if val.contains("VIOLATED") {
                    all_satisfied = false;
                }
                parts.push(val);
            }
            if all_satisfied {
                Some("all sub-constraints satisfied".to_string())
            } else {
                Some(format!("sub-constraints: {}", parts.join("; ")))
            }
        }
        "or" => {
            let mut any_satisfied = false;
            let mut parts = Vec::new();
            for arg in &args {
                let val = try_evaluate_sexp(arg)?;
                if val.contains("satisfied") {
                    any_satisfied = true;
                }
                parts.push(val);
            }
            if any_satisfied {
                Some("at least one sub-constraint satisfied".to_string())
            } else {
                Some(format!("no sub-constraint satisfied: {}", parts.join("; ")))
            }
        }
        _ => None,
    }
}

/// Parse s-expression arguments (handles nested parens).
fn parse_sexp_args(text: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();

    for ch in text.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth -= 1;
                current.push(ch);
                if depth == 0 {
                    let s = current.trim().to_string();
                    if !s.is_empty() {
                        args.push(s);
                    }
                    current.clear();
                }
            }
            c if depth == 0 && c.is_whitespace() => {
                let s = current.trim().to_string();
                if !s.is_empty() {
                    args.push(s);
                    current.clear();
                }
            }
            _ => {
                current.push(ch);
            }
        }
    }

    let remaining = current.trim().to_string();
    if !remaining.is_empty() {
        args.push(remaining);
    }

    args
}

/// Try to generate a natural language summary of why constraints conflict.
///
/// Looks for common patterns like contradictory bounds.
fn summarize_conflict(assertions: &[String]) -> Option<String> {
    // Look for simple bound conflicts on the same variable
    let mut lower_bounds: Vec<(String, String)> = Vec::new();
    let mut upper_bounds: Vec<(String, String)> = Vec::new();
    let mut equalities: Vec<(String, String)> = Vec::new();

    for assertion in assertions {
        let trimmed = assertion.trim();
        // Match (> var val), (>= var val), (< var val), (<= var val), (= expr val)
        if let Some(inner) = trimmed.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
            let args = parse_sexp_args(inner);
            if args.len() >= 3 {
                match args[0].as_str() {
                    ">" | ">=" => {
                        lower_bounds.push((args[1].clone(), args[2].clone()));
                    }
                    "<" | "<=" => {
                        upper_bounds.push((args[1].clone(), args[2].clone()));
                    }
                    "=" => {
                        equalities.push((args[1].clone(), args[2].clone()));
                    }
                    _ => {}
                }
            }
        }
    }

    // Check for bound conflicts
    if !lower_bounds.is_empty() && !equalities.is_empty() {
        return Some(format!(
            "The constraints impose conflicting requirements. \
             There are {} bound constraint(s) and {} equality constraint(s) \
             that cannot be simultaneously satisfied.",
            lower_bounds.len() + upper_bounds.len(),
            equalities.len()
        ));
    }

    if assertions.len() > 1 {
        Some(format!(
            "These {} constraints are mutually contradictory -- \
             no values exist that can satisfy all of them at the same time.",
            assertions.len()
        ))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_model_assignments() {
        let model = r#"(model
  (define-fun x () Int 5)
  (define-fun y () Int 3)
)"#;
        let assignments = parse_model_assignments(model);
        assert_eq!(assignments.len(), 2);
        assert_eq!(assignments[0], ("x".to_string(), "5".to_string()));
        assert_eq!(assignments[1], ("y".to_string(), "3".to_string()));
    }

    #[test]
    fn test_parse_model_negative_values() {
        let model = r#"(model
  (define-fun x () Int (- 5))
  (define-fun y () Int 3)
)"#;
        let assignments = parse_model_assignments(model);
        assert_eq!(assignments.len(), 2);
        assert_eq!(assignments[0], ("x".to_string(), "-5".to_string()));
        assert_eq!(assignments[1], ("y".to_string(), "3".to_string()));
    }

    #[test]
    fn test_parse_assertion_list() {
        let text = "((= (+ x y) 8)\n (> x y)\n (> x 0))";
        let assertions = parse_assertion_list(text);
        assert_eq!(assertions.len(), 3);
        assert_eq!(assertions[0], "(= (+ x y) 8)");
        assert_eq!(assertions[1], "(> x y)");
        assert_eq!(assertions[2], "(> x 0)");
    }

    #[test]
    fn test_parse_assertion_list_empty() {
        assert!(parse_assertion_list("()").is_empty());
        assert!(parse_assertion_list("").is_empty());
    }

    #[test]
    fn test_format_model_value() {
        assert_eq!(format_model_value("5"), "5");
        assert_eq!(format_model_value("(- 5)"), "-5");
        assert_eq!(format_model_value("(/ 1 3)"), "1/3");
        assert_eq!(format_model_value("true"), "true");
    }

    #[test]
    fn test_replace_var_in_sexp() {
        assert_eq!(replace_var_in_sexp("(+ x y)", "x", "5"), "(+ 5 y)");
        assert_eq!(replace_var_in_sexp("(+ x xy)", "x", "5"), "(+ 5 xy)");
    }

    #[test]
    fn test_try_evaluate_sexp_addition() {
        assert_eq!(try_evaluate_sexp("(+ 5 3)"), Some("8".to_string()));
    }

    #[test]
    fn test_try_evaluate_sexp_comparison() {
        assert_eq!(
            try_evaluate_sexp("(> 5 3)"),
            Some("5 > 3, satisfied".to_string())
        );
        assert_eq!(
            try_evaluate_sexp("(= 8 8)"),
            Some("8 = 8, satisfied".to_string())
        );
    }

    #[test]
    fn test_try_evaluate_sexp_equality_with_nested() {
        assert_eq!(
            try_evaluate_sexp("(= (+ 5 3) 8)"),
            Some("8 = 8, satisfied".to_string())
        );
    }

    #[test]
    fn test_substitute_values() {
        let assignments = vec![
            ("x".to_string(), "5".to_string()),
            ("y".to_string(), "3".to_string()),
        ];
        let result = substitute_values("(= (+ x y) 8)", &assignments);
        assert!(result.contains("(= (+ 5 3) 8)"));
        assert!(result.contains("8 = 8, satisfied"));
    }

    #[test]
    fn test_parse_sexp_args() {
        let args = parse_sexp_args("(+ x y) 8");
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], "(+ x y)");
        assert_eq!(args[1], "8");
    }

    #[test]
    fn test_parse_sexp_args_simple() {
        let args = parse_sexp_args("x y");
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], "x");
        assert_eq!(args[1], "y");
    }

    #[test]
    fn test_parse_core_names_simple() {
        assert_eq!(parse_core_names("()"), Vec::<String>::new());
        assert_eq!(parse_core_names(""), Vec::<String>::new());
        assert_eq!(parse_core_names("(n1 n2 n3)"), vec!["n1", "n2", "n3"]);
        assert_eq!(parse_core_names("(|a b| c)"), vec!["a b", "c"]);
    }

    #[test]
    fn test_split_substituted_true() {
        let (expr, verdict) = split_substituted("(= 8 8)  [= 8 = 8, satisfied]");
        assert_eq!(expr, "(= 8 8)");
        assert_eq!(verdict, "true");
    }

    #[test]
    fn test_split_substituted_false() {
        let (expr, verdict) = split_substituted("(= 1 2)  [= 1 != 2, VIOLATED]");
        assert_eq!(expr, "(= 1 2)");
        assert!(
            verdict.starts_with("false ("),
            "expected false verdict prefix, got: {verdict}"
        );
    }

    #[test]
    fn test_split_substituted_unknown() {
        let (expr, verdict) = split_substituted("(some complex expr)");
        assert_eq!(expr, "(some complex expr)");
        assert_eq!(verdict, "<unknown>");
    }

    #[test]
    fn test_summarize_verdict_variants() {
        assert_eq!(summarize_verdict("8 = 8, satisfied"), "true");
        assert!(summarize_verdict("1 != 2, VIOLATED").starts_with("false ("));
        assert_eq!(summarize_verdict("true"), "true");
        assert_eq!(summarize_verdict("42"), "42");
        assert_eq!(summarize_verdict("all sub-constraints satisfied"), "true");
    }
}
