// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Typed-switch tests for DIMACS proof-route selection.

#[test]
fn test_dimacs_proof_posture_maps_to_typed_variant_mode() {
    for (posture, expected) in [
        (DimacsProofPosture::NoProof, VariantProofMode::Disabled),
        (DimacsProofPosture::Drat, VariantProofMode::Drat),
        (DimacsProofPosture::InternalLrat, VariantProofMode::Lrat),
        (DimacsProofPosture::LratOutput, VariantProofMode::Lrat),
    ] {
        let input = variant_input_for_dimacs_route(
            SolverVariant::Default,
            32,
            96,
            posture,
            DimacsRouteContext::new(OfficialMainRoute::Other, StartupPhaseInit::Default),
        );
        assert_eq!(input.proof_mode(), expected);
        assert_eq!(input.route_profile(), VariantRouteProfile::Standard);
    }

    let internal_lrat = variant_input_for_dimacs_route(
        SolverVariant::Default,
        32,
        96,
        DimacsProofPosture::InternalLrat,
        DimacsRouteContext::new(OfficialMainRoute::Regular, StartupPhaseInit::Default),
    );
    assert_eq!(internal_lrat.proof_mode(), VariantProofMode::Lrat);
    assert_eq!(internal_lrat.route_profile(), VariantRouteProfile::Standard);

    let lrat_output = variant_input_for_dimacs_route(
        SolverVariant::Default,
        32,
        96,
        DimacsProofPosture::LratOutput,
        DimacsRouteContext::new(OfficialMainRoute::Regular, StartupPhaseInit::Default),
    );
    assert_eq!(lrat_output.proof_mode(), VariantProofMode::Lrat);
    assert_eq!(
        lrat_output.route_profile(),
        VariantRouteProfile::OfficialSatCompMainLrat
    );
}

#[test]
fn test_variant_input_for_dimacs_records_dense_mutex_restart_env_request() {
    // B75: the lever is a typed SAT switch; unit tests scope it through the
    // consumer test seam (the misc_test_override idiom B41 established here).
    let _lock = lock_env();
    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());

    let default_input = lrat_output_input(SolverVariant::Default);
    assert!(
        !default_input.dense_mutex_focused_restart_gate_experiment(),
        "dense-mutex focused restart route must be default-off"
    );

    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        dense_mutex_focused_restart_gate: true,
        ..Default::default()
    });
    let requested_input = lrat_output_input(SolverVariant::Default);
    assert!(
        requested_input.dense_mutex_focused_restart_gate_experiment(),
        "--sat-dense-mutex-focused-restart-gate should record the focused restart route request"
    );
}

#[test]
fn test_variant_input_for_dimacs_records_dense_clique_mab_branch_env_request() {
    let _lock = lock_env();
    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());

    let default_input = lrat_output_input(SolverVariant::Default);
    assert!(
        !default_input.dense_clique_mab_branch_experiment(),
        "dense-clique MAB branch route must be default-off"
    );

    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        dense_clique_mab_branch: true,
        ..Default::default()
    });
    let requested_input = lrat_output_input(SolverVariant::Default);
    assert!(
        requested_input.dense_clique_mab_branch_experiment(),
        "--sat-dense-clique-mab-branch should record the dense-clique MAB branch route request"
    );
}

#[test]
fn test_variant_input_for_dimacs_bve_lrat_scout_route_env_default_off() {
    let _lock = lock_env();
    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());
    let _g = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let input = lrat_output_input(SolverVariant::Default);

    assert_eq!(
        input.route_profile(),
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        !input.bve_lrat_scout_route(),
        "Main/LRAT BVE scout route switch must be default-off"
    );
}

#[test]
fn test_variant_input_for_dimacs_bve_lrat_scout_route_env_official_only() {
    let _lock = lock_env();
    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        bve_lrat_scout_route: true,
        ..Default::default()
    });
    let _g = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let official = lrat_output_input(SolverVariant::Default);
    assert_eq!(
        official.route_profile(),
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        official.bve_lrat_scout_route(),
        "--sat-bve-lrat-scout-route should request the official Main/LRAT BVE scout route"
    );

    let non_official = variant_input_for_dimacs_route(
        SolverVariant::Default,
        180,
        3_160,
        DimacsProofPosture::LratOutput,
        DimacsRouteContext::new(OfficialMainRoute::Other, StartupPhaseInit::Default),
    );
    assert_eq!(non_official.route_profile(), VariantRouteProfile::Standard);
    assert!(
        !non_official.bve_lrat_scout_route(),
        "route helper must keep the BVE scout flag off without the official wrapper shape"
    );

    let internal_lrat_export = internal_lrat_input();
    assert_eq!(
        internal_lrat_export.route_profile(),
        VariantRouteProfile::Standard
    );
    assert!(
        !internal_lrat_export.bve_lrat_scout_route(),
        "switch must not enable the route for internal LRAT export without LRAT output"
    );

    let aggressive = lrat_output_input(SolverVariant::Aggressive);
    assert_eq!(aggressive.route_profile(), VariantRouteProfile::Standard);
    assert!(
        !aggressive.bve_lrat_scout_route(),
        "switch must not enable the route outside default variant"
    );
}

#[test]
fn test_variant_input_for_dimacs_fmla_decompose_lrat_preflight_env_default_off() {
    let _lock = lock_env();
    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());
    let _g = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let input = lrat_output_input(SolverVariant::Default);

    assert_eq!(
        input.route_profile(),
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        !input.fmla_decompose_lrat_preflight_route(),
        "Main/LRAT Fmla decompose preflight route switch must be default-off"
    );
}

#[test]
fn test_variant_input_for_dimacs_fmla_decompose_lrat_preflight_env_official_only() {
    let _lock = lock_env();
    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        fmla_decompose_lrat_preflight_route: true,
        ..Default::default()
    });
    let _g = ScopedEnvVar::set("AY_SAT_PROFILE_ID", "ay-sat-regular-main");

    let official = lrat_output_input(SolverVariant::Default);
    assert_eq!(
        official.route_profile(),
        VariantRouteProfile::OfficialSatCompMainLrat
    );
    assert!(
        official.fmla_decompose_lrat_preflight_route(),
        "--sat-fmla-decompose-lrat-preflight-route should request the Main/LRAT preflight route"
    );

    let non_official = variant_input_for_dimacs_route(
        SolverVariant::Default,
        180,
        3_160,
        DimacsProofPosture::LratOutput,
        DimacsRouteContext::new(OfficialMainRoute::Other, StartupPhaseInit::Default),
    );
    assert_eq!(non_official.route_profile(), VariantRouteProfile::Standard);
    assert!(
        !non_official.fmla_decompose_lrat_preflight_route(),
        "route helper must keep the Fmla preflight flag off without official wrapper shape"
    );

    let internal_lrat_export = internal_lrat_input();
    assert_eq!(
        internal_lrat_export.route_profile(),
        VariantRouteProfile::Standard
    );
    assert!(
        !internal_lrat_export.fmla_decompose_lrat_preflight_route(),
        "switch must not enable the route for internal LRAT export without LRAT output"
    );

    let aggressive = lrat_output_input(SolverVariant::Aggressive);
    assert_eq!(aggressive.route_profile(), VariantRouteProfile::Standard);
    assert!(
        !aggressive.fmla_decompose_lrat_preflight_route(),
        "switch must not enable the route outside default variant"
    );
}
