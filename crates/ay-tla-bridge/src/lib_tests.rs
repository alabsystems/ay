// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn parse_no_error() {
    let out = "Model checking completed. No error has been found.\n";
    assert_eq!(parse_tlc_outcome(out, "", Some(0)), TlcOutcome::NoError);
}

#[test]
fn parse_deadlock() {
    let out = "Error: Deadlock reached.\n";
    assert_eq!(parse_tlc_outcome(out, "", Some(1)), TlcOutcome::Deadlock);
}

#[test]
fn parse_invariant_violation_extracts_name() {
    let out = "Error: Invariant TypeInvariant is violated.\n";
    assert_eq!(
        parse_tlc_outcome(out, "", Some(1)),
        TlcOutcome::InvariantViolation {
            name: Some("TypeInvariant".to_string())
        }
    );
}

#[test]
fn parse_execution_failed_falls_back_to_exit_code() {
    let out = "Some unknown output\n";
    assert_eq!(
        parse_tlc_outcome(out, "", Some(2)),
        TlcOutcome::ExecutionFailed { exit_code: Some(2) }
    );
}

/// SMOKE TEST: Verifies TlcBackend::discover() handles missing TLC gracefully.
/// This test validates error handling without requiring TLC to be installed.
#[test]
fn can_skip_real_tlc_run_when_missing() {
    // If TLC is missing, discover() returns Err. If present, returns Ok.
    // Either outcome is valid - we're testing the API doesn't panic.
    // No assertion needed: reaching this point without panic = success.
    let _result = TlcBackend::discover();
}

// Tests for new outcome variants

#[test]
fn parse_assertion_failure() {
    let out = "Error: The following assertion failed\n";
    assert!(matches!(
        parse_tlc_outcome(out, "", Some(1)),
        TlcOutcome::AssertionFailure { .. }
    ));
}

#[test]
fn parse_liveness_violation() {
    let out = "Temporal properties were violated.\n";
    assert_eq!(
        parse_tlc_outcome(out, "", Some(1)),
        TlcOutcome::LivenessViolation
    );
}

#[test]
fn parse_config_error() {
    let out = "Error reading configuration file test.cfg\n";
    assert_eq!(parse_tlc_outcome(out, "", Some(1)), TlcOutcome::ConfigError);
}

#[test]
fn parse_state_space_exhausted() {
    let out = "Out of memory while exploring state space\n";
    assert_eq!(
        parse_tlc_outcome(out, "", Some(1)),
        TlcOutcome::StateSpaceExhausted
    );
}

#[test]
fn parse_type_error() {
    let out = "TLC_TYPE error: value was not in the domain\n";
    assert_eq!(parse_tlc_outcome(out, "", Some(1)), TlcOutcome::TypeError);
}

#[test]
fn parse_parse_error() {
    let out = "Parse error in module Test at line 10\n";
    assert_eq!(parse_tlc_outcome(out, "", Some(1)), TlcOutcome::ParseError);
}

// Tests for TlcOutcome helper methods

#[test]
fn outcome_is_success() {
    assert!(TlcOutcome::NoError.is_success());
    assert!(!TlcOutcome::Deadlock.is_success());
    assert!(!TlcOutcome::InvariantViolation { name: None }.is_success());
}

#[test]
fn outcome_is_violation() {
    assert!(!TlcOutcome::NoError.is_violation());
    assert!(TlcOutcome::Deadlock.is_violation());
    assert!(TlcOutcome::InvariantViolation { name: None }.is_violation());
    assert!(TlcOutcome::LivenessViolation.is_violation());
    assert!(TlcOutcome::AssertionFailure { message: None }.is_violation());
    assert!(!TlcOutcome::TypeError.is_violation());
    assert!(!TlcOutcome::ParseError.is_violation());
}

#[test]
fn outcome_is_spec_error() {
    assert!(!TlcOutcome::NoError.is_spec_error());
    assert!(!TlcOutcome::Deadlock.is_spec_error());
    assert!(TlcOutcome::TypeError.is_spec_error());
    assert!(TlcOutcome::ParseError.is_spec_error());
    assert!(TlcOutcome::ConfigError.is_spec_error());
}

#[test]
fn outcome_error_code() {
    assert!(TlcOutcome::NoError.error_code().is_none());
    assert_eq!(
        TlcOutcome::Deadlock.error_code(),
        Some(TlcErrorCode::Deadlock)
    );
    assert_eq!(
        TlcOutcome::InvariantViolation { name: None }.error_code(),
        Some(TlcErrorCode::InvariantViolation)
    );
}

// Tests for extract_violation

#[test]
fn extract_violation_returns_none_for_success() {
    let out = "Model checking completed. No error has been found.\n";
    assert!(extract_violation(out, "", Some(0)).is_none());
}

#[test]
fn extract_violation_deadlock() {
    let out = "Error: Deadlock reached.\nState 1:\n/\\ x = 1\n";
    let violation = extract_violation(out, "", Some(1)).unwrap();
    assert_eq!(violation.code, TlcErrorCode::Deadlock);
    assert!(violation.message.contains("Deadlock"));
    assert!(violation.suggestion.is_some());
}

#[test]
fn extract_violation_invariant() {
    let out = "Error: Invariant SatCorrect is violated.\nState 1:\n/\\ state = \"SAT\"\n";
    let violation = extract_violation(out, "", Some(1)).unwrap();
    assert_eq!(violation.code, TlcErrorCode::InvariantViolation);
    assert_eq!(violation.property_name, Some("SatCorrect".to_string()));
    assert!(violation.suggestion.is_some());
}

#[test]
fn extract_trace_from_output() {
    let out = r#"
State 1: <Initial predicate>
/\ assignment = [v1 |-> "UNDEF", v2 |-> "UNDEF"]
/\ state = "PROPAGATING"

State 2: <Propagate>
/\ assignment = [v1 |-> "FALSE", v2 |-> "UNDEF"]
/\ state = "PROPAGATING"

Error: Invariant violated.
"#;
    let trace = extract_trace(out);
    assert!(trace.is_some());
    let trace = trace.unwrap();
    assert!(trace.len() >= 2);
    assert!(trace[0].contains("State 1"));
    assert!(trace[1].contains("State 2"));
}

#[test]
fn suggest_fix_for_deadlock_with_terminal_state() {
    let outcome = TlcOutcome::Deadlock;
    let text = "state = \"UNSAT\"";
    let suggestion = suggest_fix(&outcome, text);
    assert!(suggestion.is_some());
    assert!(suggestion.unwrap().contains("terminal state"));
}

#[test]
fn suggest_fix_for_invariant_violation() {
    let outcome = TlcOutcome::InvariantViolation {
        name: Some("TypeInvariant".to_string()),
    };
    let suggestion = suggest_fix(&outcome, "");
    assert!(suggestion.is_some());
    assert!(suggestion.unwrap().contains("TypeInvariant"));
}
