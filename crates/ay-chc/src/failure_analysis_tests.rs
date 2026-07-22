// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_failure_mode_from_high_smt_unknowns() {
    let stats = SolverStats {
        iterations: 100,
        smt_unknowns: 30, // 30% unknown
        ..Default::default()
    };

    let analysis = FailureAnalysis::from_stats(&stats);
    assert_eq!(analysis.mode, FailureMode::SmtTimeout);
}

#[test]
fn test_failure_mode_from_unlearnable() {
    let stats = SolverStats {
        iterations: 100,
        consecutive_unlearnable: 15,
        ..Default::default()
    };

    let analysis = FailureAnalysis::from_stats(&stats);
    assert_eq!(analysis.mode, FailureMode::WeakLemmas);
}

#[test]
fn test_failure_mode_from_deep_cex() {
    let stats = SolverStats {
        iterations: 100,
        max_frame: 10,
        max_cex_depth: 50, // Much deeper than frames
        ..Default::default()
    };

    let analysis = FailureAnalysis::from_stats(&stats);
    assert_eq!(analysis.mode, FailureMode::DeepCounterexample);
}

#[test]
fn test_guide_suggests_bmc_for_deep_cex() {
    let analysis = FailureAnalysis {
        mode: FailureMode::DeepCounterexample,
        stuck_predicate: None,
        max_cex_depth: 50,
        confidence: 0.7,
        diagnostic: String::new(),
    };

    let guide = FailureGuide::from_analysis(&analysis);
    assert!(matches!(
        guide.try_alternative_engine,
        Some(AlternativeEngine::Bmc { .. })
    ));
}

#[test]
fn test_guide_applies_adjustments() {
    let analysis = FailureAnalysis {
        mode: FailureMode::WeakLemmas,
        stuck_predicate: None,
        max_cex_depth: 10,
        confidence: 0.8,
        diagnostic: String::new(),
    };

    let guide = FailureGuide::from_analysis(&analysis);
    let config = PdrConfig::default();
    let new_config = guide.apply_to_config(config);

    // Should enable stronger generalization features for weak lemmas
    assert!(new_config.use_farkas_combination);
    assert!(new_config.use_relational_equality);
    assert!(new_config.use_range_weakening);
}

#[test]
fn test_failure_mode_from_oscillation() {
    let stats = SolverStats {
        iterations: 100,
        restart_count: 8,  // Many restarts
        lemmas_learned: 5, // Very few lemmas (0.05 rate < 0.1 threshold)
        ..Default::default()
    };

    let analysis = FailureAnalysis::from_stats(&stats);
    assert_eq!(analysis.mode, FailureMode::Oscillation);
}

#[test]
fn test_failure_mode_from_predicate_coupling() {
    let stats = SolverStats {
        iterations: 100,
        has_predicate_coupling: true,
        ..Default::default()
    };

    let analysis = FailureAnalysis::from_stats(&stats);
    assert_eq!(analysis.mode, FailureMode::PredicateCoupling);
}

#[test]
fn test_zero_iterations_no_panic() {
    // Edge case: zero iterations should not cause division by zero
    let stats = SolverStats {
        iterations: 0,
        smt_unknowns: 5, // Would trigger SmtTimeout if we divided by 0
        ..Default::default()
    };

    let analysis = FailureAnalysis::from_stats(&stats);
    // Should fall through to ResourceExhausted, not panic
    assert_eq!(analysis.mode, FailureMode::ResourceExhausted);
}
