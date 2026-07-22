// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for TLC runner.
//!
//! These tests require TLC to be available. They are skipped when
//! TLC is not installed.
//!
//! To run:
//! - Set `TLC_BIN` to point to a `tlc` executable, OR
//! - Set `TLA2TOOLS_JAR` to point to `tla2tools.jar`
//!
//! Example:
//! ```bash
//! TLC_BIN=/usr/local/bin/tlc cargo test -p ay-tla-bridge --test tlc_integration
//! ```

use ay_tla_bridge::TlcOutcome;
use ntest::timeout;

// NOTE: test_cdcl_test_spec and test_cdcl_main_spec deleted - required external TLC tool (#596)
// TLC tests must be run manually with TLC_BIN or TLA2TOOLS_JAR set.

/// Test that we correctly identify various TLC error types.
#[test]
#[timeout(5000)]
fn test_outcome_parsing() {
    use ay_tla_bridge::parse_tlc_outcome;

    // Successful run
    assert_eq!(
        parse_tlc_outcome(
            "Model checking completed. No error has been found.\n",
            "",
            Some(0)
        ),
        TlcOutcome::NoError
    );

    // Deadlock
    assert_eq!(
        parse_tlc_outcome("Error: Deadlock reached.\n", "", Some(1)),
        TlcOutcome::Deadlock
    );

    // Invariant violation with name
    assert_eq!(
        parse_tlc_outcome("Error: Invariant TypeInvariant is violated.\n", "", Some(1)),
        TlcOutcome::InvariantViolation {
            name: Some("TypeInvariant".to_string())
        }
    );

    // Invariant violation with complex name
    assert_eq!(
        parse_tlc_outcome(
            "Error: Invariant SatCorrect is violated.\nThe behavior up to this point is:\n...",
            "",
            Some(1)
        ),
        TlcOutcome::InvariantViolation {
            name: Some("SatCorrect".to_string())
        }
    );

    // Liveness violation
    assert_eq!(
        parse_tlc_outcome("Temporal properties were violated.\n", "", Some(1)),
        TlcOutcome::LivenessViolation
    );

    // Type error
    assert_eq!(
        parse_tlc_outcome("TLC_TYPE error: value was not in the domain\n", "", Some(1)),
        TlcOutcome::TypeError
    );

    // Parse error
    assert_eq!(
        parse_tlc_outcome("Parse error in module Foo\n", "", Some(1)),
        TlcOutcome::ParseError
    );

    // Unknown failure
    assert_eq!(
        parse_tlc_outcome("Something unexpected happened\n", "", Some(42)),
        TlcOutcome::ExecutionFailed {
            exit_code: Some(42)
        }
    );
}
