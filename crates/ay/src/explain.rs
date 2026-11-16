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
//! SAT explanations use the executor's typed public model evaluation. Any
//! unsupported or refused evaluation remains unknown in the explanation.

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
/// Output emits the assertion and its model value so the user can audit the
/// model without mental arithmetic:
///
/// ```text
///   assertion: <pretty-printed>
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
            safe_println!("Assertions are unavailable for explanation evaluation.");
            return;
        }
    };

    let assertion_strs = parse_assertion_list(&assertions_text);

    if assertion_strs.is_empty() {
        safe_println!();
        safe_println!("No assertions are available for explanation evaluation.");
        return;
    }

    safe_println!();
    safe_println!("Constraint verification:");
    let mut verified = 0;
    let mut violated = 0;
    let values = evaluate_explanation_assertions(executor, &assertion_strs);
    for (i, assertion) in assertion_strs.iter().enumerate() {
        let pretty = assertion.trim();
        let verdict = match values.get(i).copied().flatten() {
            Some(true) => {
                verified += 1;
                "true"
            }
            Some(false) => {
                violated += 1;
                "false"
            }
            None => "<unknown>",
        };
        safe_println!("  {}. assertion: {pretty}", i + 1);
        safe_println!("     evaluates to: {verdict}");
    }
    safe_println!();
    safe_println!(
        "{}",
        constraint_summary(assertion_strs.len(), verified, violated)
    );
}

/// One public model read reuses the executor's typed evaluation, cancellation,
/// source fence and resource accounting. Never start another solver query or
/// guess a value by substituting strings into a second arithmetic evaluator.
fn evaluate_explanation_assertions(
    executor: &mut Executor,
    assertions: &[String],
) -> Vec<Option<bool>> {
    use ay_frontend::{sexp::parse_sexps, SExpr};

    let request = format!("(get-value ({}))", assertions.join(" "));
    let Ok(commands) = ay_frontend::parse(&request) else {
        return Vec::new();
    };
    let [command] = commands.as_slice() else {
        return Vec::new();
    };
    let Command::GetValue(requested) = command else {
        return Vec::new();
    };
    let Ok(Some(output)) = executor.execute(command) else {
        return Vec::new();
    };
    let Ok(expressions) = parse_sexps(&output) else {
        return Vec::new();
    };
    let [SExpr::List(pairs)] = expressions.as_slice() else {
        return Vec::new();
    };
    if pairs.len() != assertions.len() {
        return Vec::new();
    }
    pairs
        .iter()
        .zip(requested)
        .map(|(pair, (assertion, _))| {
            let SExpr::List(items) = pair else {
                return None;
            };
            if items.len() != 2 || items[0].to_raw_string() != *assertion {
                return None;
            }
            match &items[1] {
                SExpr::True => Some(true),
                SExpr::False => Some(false),
                _ => None,
            }
        })
        .collect()
}

/// Describe only what the explanation evaluator actually established. The SAT
/// answer and the solver's independent model validation are separate evidence.
fn constraint_summary(total: usize, verified: usize, violated: usize) -> String {
    if verified == total {
        format!("All {total} constraint(s) satisfied.")
    } else {
        format!(
            "Explanation evaluation: {verified} satisfied, {violated} violated, {} unknown.",
            total - verified - violated
        )
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
    use ay_frontend::{sexp::parse_sexps, SExpr};

    let Ok(expressions) = parse_sexps(model_text) else {
        return Vec::new();
    };
    let mut assignments = Vec::new();
    // Walk model containers iteratively; never descend into a definition's
    // value, where a quoted symbol named define-fun is ordinary model data.
    let mut pending: Vec<_> = expressions.iter().rev().collect();
    while let Some(expression) = pending.pop() {
        let SExpr::List(items) = expression else {
            continue;
        };
        if items.first().and_then(SExpr::as_symbol) == Some("define-fun") {
            if items.len() == 5 && matches!(&items[2], SExpr::List(args) if args.is_empty()) {
                if let Some(name) = items[1].as_symbol() {
                    assignments.push((name.to_string(), format_model_value(&items[4].to_string())));
                }
            }
        } else {
            pending.extend(items.iter().rev());
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
    use ay_frontend::{sexp::parse_sexps, SExpr};
    let Ok(expressions) = parse_sexps(text) else {
        return Vec::new();
    };
    let [SExpr::List(assertions)] = expressions.as_slice() else {
        return Vec::new();
    };
    assertions.iter().map(SExpr::to_raw_string).collect()
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
    fn explanation_uses_typed_model_values_and_refuses_stale_models() {
        let commands = ay_frontend::parse(
            "(set-option :produce-models true) (set-logic QF_LRA)
             (declare-const x Real) (assert (= (* 3 x) 1)) (check-sat)",
        )
        .unwrap();
        let mut executor = Executor::new();
        assert_eq!(
            executor
                .execute_all(&commands)
                .unwrap()
                .last()
                .map(String::as_str),
            Some("sat")
        );
        let assertions = [
            "(= (* 3 x) 1)",
            "(or false false)",
            "(and true false)",
            "(not false)",
        ]
        .map(str::to_owned);
        assert_eq!(
            evaluate_explanation_assertions(&mut executor, &assertions),
            vec![Some(true), Some(false), Some(false), Some(true)]
        );
        executor.execute(&Command::Push(1)).unwrap();
        executor.execute(&Command::Pop(1)).unwrap();
        assert_eq!(
            evaluate_explanation_assertions(&mut executor, &assertions).as_slice(),
            &[] as &[Option<bool>]
        );
    }

    #[test]
    fn explanation_preserves_nested_sorts_and_quoted_assertion_boundaries() {
        assert_eq!(parse_model_assignments(
            "(model (define-fun dividend ()\n (_ FloatingPoint 8 200)\n (fp #b0 #b10000000 #b101)))"),
            vec![("dividend".into(), "(fp #b0 #b10000000 #b101)".into())]);
        let assertions = parse_assertion_list("((= |x)| 1) (= \"(\" \"(\"))");
        assert_eq!(assertions, vec!["(= |x)| 1)", "(= \"(\" \"(\")"]);
    }

    #[test]
    fn explanation_summary_does_not_promote_unknown_or_false_to_verified() {
        assert_eq!(
            constraint_summary(11, 0, 0),
            "Explanation evaluation: 0 satisfied, 0 violated, 11 unknown."
        );
        assert_eq!(
            constraint_summary(3, 1, 1),
            "Explanation evaluation: 1 satisfied, 1 violated, 1 unknown."
        );
        assert_eq!(
            constraint_summary(2, 2, 0),
            "All 2 constraint(s) satisfied."
        );
    }

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
        assert_eq!(parse_assertion_list("()").as_slice(), &[] as &[String]);
        assert_eq!(parse_assertion_list("").as_slice(), &[] as &[String]);
    }

    #[test]
    fn test_format_model_value() {
        assert_eq!(format_model_value("5"), "5");
        assert_eq!(format_model_value("(- 5)"), "-5");
        assert_eq!(format_model_value("(/ 1 3)"), "1/3");
        assert_eq!(format_model_value("true"), "true");
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
}
