// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! UNSAT explanations from retained query evidence. A zero theory-conflict
//! counter does not prove that no theory reasoning occurred. Read original
//! term data directly; rendered assertions are neither a parser input nor the
//! complete query when temporary assumptions are present.

use ay_dpll::Executor;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ReasonCode {
    PreprocessingDetected,
    CheckedRefutation(&'static str),
    TheoryConflict(&'static str),
    Unknown,
}

impl ReasonCode {
    pub(crate) fn tag(&self) -> &'static str {
        match self {
            Self::PreprocessingDetected => "PreprocessingDetected",
            Self::CheckedRefutation(_) => "CheckedRefutation",
            Self::TheoryConflict(_) => "TheoryConflict",
            Self::Unknown => "Unknown",
        }
    }

    pub(crate) fn theory(&self) -> Option<&str> {
        match self {
            Self::CheckedRefutation(name) | Self::TheoryConflict(name) => Some(name),
            _ => None,
        }
    }

    pub(crate) fn template(&self) -> String {
        match self {
            Self::PreprocessingDetected =>
                "An original query constraint is Boolean false, so the constraints cannot all hold.".to_owned(),
            Self::CheckedRefutation(theory) => format!(
                "The independent {theory} proof checker validated a refutation of the original constraints."
            ),
            Self::TheoryConflict(theory) => format!(
                "The {theory} theory solver reported conflicts while solving this query."
            ),
            Self::Unknown =>
                "AY returned UNSAT, but the retained diagnostics do not identify a more specific reasoning path.".to_owned(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum ExplainFormat {
    #[default]
    Plain,
    Json,
}

/// Diagnostic only: these observations never authorize a verdict or grade.
pub(crate) fn detect_reason_code(executor: &Executor) -> ReasonCode {
    if !executor.last_result_is_unsat() {
        return ReasonCode::Unknown;
    }
    let stats = executor.statistics();
    // Both markers are set only after strict authored-scope installation of
    // the native FP certificate, including its independent semantic check.
    if ["fp.pinned.checked_presolve", "fp.ground.checked_presolve"]
        .iter()
        .any(|key| stats.get_int(key).unwrap_or(0) > 0)
    {
        return ReasonCode::CheckedRefutation("FP");
    }
    if executor.last_unsat_query_contains_literal_false() == Some(true) {
        return ReasonCode::PreprocessingDetected;
    }
    for (key, name) in [
        ("smt.conflicts.lia", "LIA"),
        ("smt.conflicts.lra", "LRA"),
        ("smt.conflicts.euf", "EUF"),
        ("smt.conflicts.arrays", "arrays"),
    ] {
        if stats.get_int(key).unwrap_or(0) > 0 {
            return ReasonCode::TheoryConflict(name);
        }
    }
    if stats.theory_conflicts > 0 {
        return ReasonCode::TheoryConflict("unspecified");
    }
    ReasonCode::Unknown
}

pub(crate) fn emit_unsat_reason(executor: &mut Executor, format: ExplainFormat) {
    let reason = detect_reason_code(executor);
    match format {
        ExplainFormat::Plain => {
            safe_println!();
            safe_println!("=== Reason code (UNSAT) ===");
            match reason.theory() {
                Some(theory) => safe_println!("Reason: {}({theory})", reason.tag()),
                None => safe_println!("Reason: {}", reason.tag()),
            }
            safe_println!("Explanation: {}", reason.template());
        }
        ExplainFormat::Json => safe_println!("{}", format_reason_json(&reason)),
    }
}

fn format_reason_json(reason: &ReasonCode) -> String {
    serde_json::json!({
        "reason": reason.tag(),
        "theory": reason.theory(),
        "message": reason.template(),
    })
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;

    fn execute(script: &str) -> Executor {
        let mut executor = Executor::new();
        executor.execute_all(&parse(script).unwrap()).unwrap();
        assert!(executor.last_result_is_unsat());
        executor
    }

    #[test]
    fn checked_fp_refutation_is_not_reported_as_purely_propositional() {
        let mut executor = execute(include_str!(
            "../../ay-model-check/tests/fixtures/wide-fp-remainder-odd-unsat.smt2"
        ));
        assert_eq!(
            detect_reason_code(&executor),
            ReasonCode::CheckedRefutation("FP")
        );
        executor.execute_all(&parse(
            "(reset)(set-logic QF_UF)(declare-const a Bool)(check-sat-assuming (a (not a)))"
        ).unwrap()).unwrap();
        assert!(executor.last_result_is_unsat());
        assert_eq!(
            executor.last_unsat_query_contains_literal_false(),
            Some(false)
        );
        assert_eq!(detect_reason_code(&executor), ReasonCode::Unknown);
    }

    #[test]
    fn literal_false_is_read_from_the_original_query() {
        let executor = execute("(set-logic QF_UF)(assert false)(check-sat)");
        assert_eq!(
            executor.last_unsat_query_contains_literal_false(),
            Some(true)
        );
        assert_eq!(
            detect_reason_code(&executor),
            ReasonCode::PreprocessingDetected
        );
    }
}
