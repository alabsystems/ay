// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_verdict_display_verified() {
    let v = VerificationVerdict::Verified {
        boundary: VerificationBoundary::SmtGroundAssertion,
        evidence: VerificationEvidenceKind::Independent,
    };
    assert!(v.to_string().contains("verified"));
    assert!(v.is_verified());
    assert!(!v.is_incomplete());
    assert!(!v.is_violated());
}

#[test]
fn test_verdict_display_incomplete() {
    let v = VerificationVerdict::Incomplete(VerificationFailure {
        boundary: VerificationBoundary::SmtCircularSatFallback,
        detail: "assertion 3 SAT-fallback".to_string(),
    });
    assert!(v.to_string().contains("incomplete"));
    assert!(v.is_incomplete());
}

#[test]
fn test_verdict_display_violated() {
    let v = VerificationVerdict::Violated(VerificationFailure {
        boundary: VerificationBoundary::SmtGroundAssertion,
        detail: "assertion 0 evaluates to false".to_string(),
    });
    assert!(v.to_string().contains("violated"));
    assert!(v.is_violated());
}

#[test]
fn test_failure_display() {
    let f = VerificationFailure {
        boundary: VerificationBoundary::SmtAssumption,
        detail: "no model available".to_string(),
    };
    let s = f.to_string();
    assert!(s.contains("SmtAssumption"));
    assert!(s.contains("no model available"));
}
