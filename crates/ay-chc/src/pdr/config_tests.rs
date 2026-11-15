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

// --- Workstream B: SpacerLane (DESIGN §3.7 / §4.5) ---

#[test]
fn spacer_lane_default_is_rung_2_and_off_ignores_other_flags() {
    assert_eq!(SpacerLane::default(), SpacerLane::OFF);
    assert_eq!(PdrConfig::default().spacer, SpacerLane::rung(2));
    assert_eq!(SpacerLane::rung(0), SpacerLane::OFF);
    let mut lane = SpacerLane::OFF;
    lane.free_pob = true;
    lane.lift_caps = true;
    assert_eq!(lane.validate(false), SpacerLane::OFF);
}

#[test]
fn spacer_lane_rungs_are_cumulative() {
    let r1 = SpacerLane::rung(1);
    assert!(r1.enabled && r1.core_lemma && r1.ind_gen && r1.confirm_cores && r1.lift_caps);
    assert!(!r1.free_pob && !r1.mbp_exact_lia && !r1.ind_gen_weaken);
    assert_eq!(r1.backend, OracleBackend::Legacy);
    assert_eq!(r1.ind_gen_max_queries, 64);
    assert_eq!(r1.rung_label(), 1);
    let r2 = SpacerLane::rung(2);
    assert!(r2.free_pob && r2.mbp_exact_lia && r2.core_lemma);
    assert_eq!(r2.rung_label(), 2);
    let r4 = SpacerLane::rung(4);
    assert_eq!(r4.backend, OracleBackend::Session);
    assert_eq!(r4.ind_gen_max_queries, 256);
    assert!(r4.free_pob);
    assert_eq!(r4.rung_label(), 4);
    let r5 = SpacerLane::rung(5);
    assert!(r5.ind_gen_weaken);
    assert_eq!(r5.rung_label(), 5);
    assert_eq!(SpacerLane::rung(9), r5);
}

#[test]
fn spacer_lane_validate_refuses_lift_caps_without_core_lemma() {
    let mut lane = SpacerLane::rung(1);
    lane.core_lemma = false;
    let v = lane.validate(false);
    assert!(v.enabled);
    assert!(!v.lift_caps);
    assert!(v.ind_gen);
}

#[test]
fn spacer_lane_from_default_switches_is_rung_2() {
    let sw = crate::ab_switches::ChcAbSwitches::default();
    assert_eq!(SpacerLane::from_ab_switches(&sw), SpacerLane::rung(2));
    let mut sw0 = sw;
    sw0.spacer_rung = 0;
    sw0.spacer_free_pob = Some(true);
    assert_eq!(
        SpacerLane::from_ab_switches(&sw0),
        SpacerLane::OFF,
        "rung 0 is the legacy pipeline whatever the overrides say"
    );
    let mut sw2 = sw;
    sw2.spacer_rung = 1;
    assert_eq!(SpacerLane::from_ab_switches(&sw2), SpacerLane::rung(1));
    let mut sw3 = sw;
    sw3.spacer_rung = 2;
    sw3.spacer_free_pob = Some(false);
    let lane = SpacerLane::from_ab_switches(&sw3);
    assert!(lane.enabled && !lane.free_pob && !lane.mbp_exact_lia && lane.core_lemma);
    let mut sw4 = sw;
    sw4.spacer_confirm_cores = Some(false);
    let lane = SpacerLane::from_ab_switches(&sw4);
    assert!(lane.enabled && !lane.confirm_cores && lane.core_lemma);
}

#[test]
fn spacer_core_profile_sets_spacer_defaults() {
    let p = PdrConfig::spacer_core_profile(PdrConfig::default().with_spacer(SpacerLane::OFF));
    assert!(p.spacer.enabled);
    assert_eq!(p.spacer, SpacerLane::rung(1));
    assert!(!p.use_pob_push && !p.use_restarts && !p.use_may_pobs && !p.use_convex_closure);
    assert!(p.use_mbp);
    let base = PdrConfig::default().with_spacer(SpacerLane::rung(2));
    let p2 = PdrConfig::spacer_core_profile(base);
    assert_eq!(p2.spacer, SpacerLane::rung(2));
}
