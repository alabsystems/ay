// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_failure_display() {
    let f = InterpolationFailure::SharedVarsEmpty {
        a_vars: 3,
        b_vars: 2,
    };
    assert_eq!(f.to_string(), "shared_vars empty (A: 3 vars, B: 2 vars)");

    let f = InterpolationFailure::NotApplicable {
        reason: "no constraints".to_string(),
    };
    assert_eq!(f.to_string(), "not applicable: no constraints");
}

#[test]
fn test_diagnostics_summary() {
    let mut diag = InterpolationDiagnostics::new();
    assert_eq!(diag.summary(), "no failures recorded");

    diag.golem_sat = Some(InterpolationFailure::NotApplicable {
        reason: "empty A-side".to_string(),
    });
    diag.lia_farkas = Some(InterpolationFailure::SharedVarsEmpty {
        a_vars: 2,
        b_vars: 3,
    });

    let summary = diag.summary();
    assert!(summary.contains("golem:not applicable: empty A-side"));
    assert!(summary.contains("lia:shared_vars empty"));
}

#[test]
fn test_dominant_failure_priority() {
    let mut diag = InterpolationDiagnostics::new();

    // SharedVarsEmpty takes priority over NotApplicable
    diag.golem_sat = Some(InterpolationFailure::NotApplicable {
        reason: "test".to_string(),
    });
    diag.n1_per_clause = Some(InterpolationFailure::SharedVarsEmpty {
        a_vars: 3,
        b_vars: 2,
    });

    let dominant = diag.dominant_failure().unwrap();
    assert!(matches!(
        dominant,
        InterpolationFailure::SharedVarsEmpty { .. }
    ));
}

#[test]
fn test_failure_count() {
    let mut diag = InterpolationDiagnostics::new();
    assert_eq!(diag.failure_count(), 0);

    diag.golem_sat = Some(InterpolationFailure::NotApplicable {
        reason: "test".to_string(),
    });
    assert_eq!(diag.failure_count(), 1);

    diag.lia_farkas = Some(InterpolationFailure::SharedVarsEmpty {
        a_vars: 1,
        b_vars: 1,
    });
    assert_eq!(diag.failure_count(), 2);
}

#[test]
fn test_interpolation_stats_summary() {
    let stats = InterpolationStats::default();
    assert_eq!(stats.summary(), "no interpolation attempts");
    assert_eq!(stats.total_successes(), 0);

    let stats = InterpolationStats {
        attempts: 10,
        golem_a_unsat_skips: 2,
        golem_sat_successes: 3,
        n1_per_clause_successes: 2,
        lia_farkas_successes: 1,
        syntactic_farkas_successes: 0,
        iuc_farkas_successes: 1,
        all_failed: 3,
    };
    assert_eq!(stats.total_successes(), 7);
    let summary = stats.summary();
    assert!(summary.contains("attempts=10"));
    assert!(summary.contains("golem=3"));
    assert!(summary.contains("golem_a_unsat_skips=2"));
    assert!(summary.contains("all_failed=3"));
    assert!(summary.contains("success=70%"));
}

#[test]
fn test_interpolation_stats_consistency_allows_skip_and_success_overlap() {
    // A-side UNSAT skip only excludes conjunctive method-1; the same attempt
    // may still succeed on method-2..5.
    let stats = InterpolationStats {
        attempts: 1,
        golem_a_unsat_skips: 1,
        n1_per_clause_successes: 1,
        ..InterpolationStats::default()
    };
    stats.debug_assert_consistency();
}
