// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_luby_sequence() {
    // Expected Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
    for (i, &exp) in expected.iter().enumerate() {
        assert_eq!(
            luby(i as u32),
            exp,
            "luby({}) should be {}, got {}",
            i,
            exp,
            luby(i as u32)
        );
    }
}

#[test]
fn test_config_restart_defaults() {
    let config = PdrConfig::default();
    assert!(config.use_restarts);
    assert_eq!(config.restart_initial_threshold, 10);
}

#[test]
fn test_config_entry_cegar_defaults() {
    // Default config has Entry-CEGAR enabled (helps gj2007 pattern)
    let default_config = PdrConfig::default();
    assert!(default_config.use_entry_cegar_discharge);

    // Production config has Entry-CEGAR disabled (avoids timeout on some benchmarks)
    let production_config = PdrConfig::production(false);
    assert!(!production_config.use_entry_cegar_discharge);
}

#[test]
fn test_lia_farkas_profile_enables_arithmetic_template_surface() {
    let config = PdrConfig::lia_farkas_profile(false);

    assert!(config.is_lia_farkas_profile());
    assert!(config.strict_proofs);
    assert!(config.disable_array_scalarization);
    assert!(config.preserve_original_clauses);
    assert!(config.use_range_weakening);
    assert!(config.use_init_bound_weakening);
    assert!(config.use_farkas_combination);
    assert!(config.use_relational_equality);
    assert!(config.use_interpolation);
    assert!(config.use_convex_closure);
    assert!(config.use_scaled_difference_bounds);
    assert!(config.use_lemma_hints);
    assert!(config.max_frames >= 60);
    assert!(config.max_iterations >= 700);
    assert!(config.max_obligations >= 75_000);
}

#[test]
fn test_lia_farkas_template_surface_counts_enabled_families() {
    let config = PdrConfig::lia_farkas_profile(false);
    let surface = config.lia_farkas_template_surface();

    assert!(surface.affine_equalities);
    assert!(surface.intervals);
    assert!(surface.difference_bounds);
    assert!(surface.scaled_linear_combinations);
    assert_eq!(surface.enabled_count(), 4);
}

#[test]
fn test_config_builder_pattern() {
    // Downstream consumers can use builder pattern instead of struct update syntax
    let config = PdrConfig::default()
        .with_max_frames(10)
        .with_max_iterations(100)
        .with_max_obligations(5000)
        .with_verbose(true);

    assert_eq!(config.max_frames, 10);
    assert_eq!(config.max_iterations, 100);
    assert_eq!(config.max_obligations, 5000);
    assert!(config.verbose);
}

#[test]
fn test_config_builder_cancellation_token() {
    // Test with_cancellation_token
    let token = CancellationToken::new();
    let config = PdrConfig::default().with_cancellation_token(Some(token));
    assert!(config.cancellation_token.is_some());

    // Test None case
    let config = PdrConfig::default().with_cancellation_token(None);
    assert!(config.cancellation_token.is_none());
}

#[test]
fn test_config_builder_user_hints() {
    // Test with_user_hints - use empty vec since LemmaHint requires complex types
    let config = PdrConfig::default().with_user_hints(vec![]);
    assert!(config.user_hints.is_empty());

    // The with_user_hints builder is available and works
    // Full hint construction tested in lemma_hints module
}

#[test]
fn test_config_builder_chaining_idempotent() {
    // Verify later calls override earlier ones (last write wins)
    let config = PdrConfig::default().with_max_frames(10).with_max_frames(20);

    assert_eq!(config.max_frames, 20);
}
