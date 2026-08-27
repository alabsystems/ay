// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn variant_input_for_dimacs(
    variant: SolverVariant,
    num_vars: usize,
    num_clauses: usize,
    proof: DimacsProofPosture,
) -> VariantInput {
    let official_main = if official_sat_main_regular_route_from_env() {
        OfficialMainRoute::Regular
    } else {
        OfficialMainRoute::Other
    };
    let startup_phase_init = if env_truthy(SATCOMP_MAIN_STARTUP_PHASE_INIT_ENV) {
        StartupPhaseInit::Explicit
    } else {
        StartupPhaseInit::Default
    };
    let input = variant_input_for_dimacs_route(
        variant,
        num_vars,
        num_clauses,
        proof,
        DimacsRouteContext::new(official_main, startup_phase_init),
    );
    let input = if ay_core::sat_ab_switches().dense_mutex_focused_restart_gate {
        input.with_dense_mutex_focused_restart_gate_experiment()
    } else {
        input
    };
    let input = if ay_core::sat_ab_switches().dense_clique_mab_branch {
        input.with_dense_clique_mab_branch_experiment()
    } else {
        input
    };
    if ay_core::sat_ab_switches().bve_lrat_scout_route
        && matches!(variant, SolverVariant::Default)
        && proof.lrat_output()
        && matches!(
            input.route_profile(),
            VariantRouteProfile::OfficialSatCompMainLrat
        )
    {
        let input = input.with_bve_lrat_scout_route();
        if ay_core::sat_ab_switches().fmla_decompose_lrat_preflight_route {
            input.with_fmla_decompose_lrat_preflight_route()
        } else {
            input
        }
    } else if ay_core::sat_ab_switches().fmla_decompose_lrat_preflight_route
        && matches!(variant, SolverVariant::Default)
        && proof.lrat_output()
        && matches!(
            input.route_profile(),
            VariantRouteProfile::OfficialSatCompMainLrat
        )
    {
        input.with_fmla_decompose_lrat_preflight_route()
    } else {
        input
    }
}

fn variant_input_for_dimacs_route(
    variant: SolverVariant,
    num_vars: usize,
    num_clauses: usize,
    proof: DimacsProofPosture,
    route: DimacsRouteContext,
) -> VariantInput {
    let official_main_default_lrat = matches!(route.official_main, OfficialMainRoute::Regular)
        && matches!(variant, SolverVariant::Default)
        && proof.lrat_output();
    let input = if official_main_default_lrat {
        VariantInput::new(num_vars, num_clauses, proof.variant_proof_mode())
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
    } else {
        VariantInput::new(num_vars, num_clauses, proof.variant_proof_mode())
    };
    if official_main_default_lrat && matches!(route.startup_phase_init, StartupPhaseInit::Default) {
        input.with_startup_policy(VariantStartupPolicy::DisableWarmupWalk)
    } else {
        input
    }
}

fn variant_profile_plan_for_dimacs_features(
    variant: SolverVariant,
    num_vars: usize,
    num_clauses: usize,
    proof: DimacsProofPosture,
    features: &SatFeatures,
) -> VariantProfilePlan {
    // Auto-route Default for binary-dominant mid-size instances when the user
    // did not pass an explicit `--sat-variant`: first the probe band
    // (Default -> Probe, ratio <= 4.0; kill-switch AY_AB_PROBE_ROUTE=0), then
    // the disjoint aggressive band (Default -> Aggressive, 4.0 < ratio <= 6.5,
    // 50k-250k vars; kill-switch AY_AB_AGGRESSIVE_ROUTE=0). An explicit variant
    // is always honored verbatim.
    let requested_source = sat_variant_decision_source();
    let (variant, source) = if sat_variant_explicitly_selected() {
        (variant, requested_source)
    } else {
        variant.auto_route_with_source(features, requested_source)
    };
    let input = variant_input_for_dimacs(variant, num_vars, num_clauses, proof);
    let route_source = if input
        .route_profile()
        .requires_proof_safe_specialist_routing()
        || (matches!(variant, SolverVariant::Default) && proof.lrat_output())
    {
        official_sat_main_regular_route_source_from_env()
    } else {
        None
    };
    VariantProfilePlan::for_features_with_sources(variant, input, features, source, route_source)
}

/// Whether an explicit, non-empty `--sat-variant` (or `AY_SAT_VARIANT`) was
/// selected — in which case load-time auto-routing must not override it.
fn sat_variant_explicitly_selected() -> bool {
    matches!(
        ay_core::misc_cli_flags().sat_variant.as_deref(),
        Some(value) if !value.trim().is_empty()
    )
}

fn sat_variant_decision_source() -> DecisionSource {
    let flags = ay_core::misc_cli_flags();
    if flags.sat_variant_from_cli
        && flags
            .sat_variant
            .as_deref()
            .is_some_and(|value| !value.trim().is_empty())
    {
        DecisionSource::Cli
    } else if flags
        .sat_variant
        .as_deref()
        .is_some_and(|value| !value.trim().is_empty())
    {
        DecisionSource::EnvShim("AY_SAT_VARIANT")
    } else {
        DecisionSource::Default
    }
}

fn sat_variant_source_label() -> &'static str {
    let flags = ay_core::misc_cli_flags();
    match flags.sat_variant.as_deref() {
        Some(value) if !value.trim().is_empty() && flags.sat_variant_from_cli => "--sat-variant",
        Some(value) if !value.trim().is_empty() => "AY_SAT_VARIANT",
        Some(_) => "--sat-variant-empty-default",
        None => "default",
    }
}

/// Content byte length above which the streaming probe-route pre-scan is
/// skipped. Any in-band formula (<= 3M vars, ratio <= 4, binary-dominant) is
/// well under this; larger content is a giant that is out-of-band by variable
/// count anyway, so the O(n) scan is not worth its cost.
const STREAMING_PROBE_ROUTE_SCAN_MAX_BYTES: usize = 400_000_000;

/// Streaming-path analogue of the buffered auto-route: decide whether an
/// unspecified Default preset should route to Probe (binary-dominant, ratio <=
/// 4.0) or, failing that, to Aggressive (binary-dominant, 4.0 < ratio <= 6.5,
/// 50k-250k vars) for a large mid-size formula. The streaming parser does not
/// buffer clauses, so the band inputs (max variable, clause count,
/// binary-clause count) come from a single content pre-scan. Returns `variant`
/// unchanged when auto-routing is disallowed (explicit `--sat-variant`), the
/// content is a giant, or neither band matches; the per-band kill-switches
/// (`AY_AB_PROBE_ROUTE=0` / `AY_AB_AGGRESSIVE_ROUTE=0`) are honored inside
/// [`SolverVariant::auto_route_from_counts`].
fn streaming_auto_route(
    content: &str,
    variant: SolverVariant,
    automatic_routing: DimacsAutomaticRouting,
    requested_source: DecisionSource,
) -> (SolverVariant, DecisionSource) {
    if !automatic_routing.is_allowed() || content.len() > STREAMING_PROBE_ROUTE_SCAN_MAX_BYTES {
        return (variant, requested_source);
    }
    let (max_var, num_clauses, num_binary) = scan_probe_route_shape(content);
    variant.auto_route_from_counts_with_source(max_var, num_clauses, num_binary, requested_source)
}

/// One pass over DIMACS `content` returning the auto-route band inputs shared
/// by both the probe and aggressive bands:
/// `(max_variable_index, num_clauses, num_binary_clauses)`. `max_variable_index`
/// matches the solver's content-driven sizing (the largest referenced variable,
/// not the declared header count). Clauses may span lines; a clause ends at a
/// `0` token, so binary clauses are those with exactly two literals before `0`.
fn scan_probe_route_shape(content: &str) -> (usize, usize, usize) {
    let mut max_var = 0usize;
    let mut num_clauses = 0usize;
    let mut num_binary = 0usize;
    let mut lits_in_clause = 0usize;
    for line in content.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty()
            || trimmed.starts_with('c')
            || trimmed.starts_with('p')
            || trimmed.starts_with('%')
        {
            continue;
        }
        for tok in trimmed.split_ascii_whitespace() {
            let value: i64 = match tok.parse() {
                Ok(value) => value,
                Err(_) => continue,
            };
            if value == 0 {
                num_clauses += 1;
                if lits_in_clause == 2 {
                    num_binary += 1;
                }
                lits_in_clause = 0;
            } else {
                lits_in_clause += 1;
                let abs = value.unsigned_abs() as usize;
                if abs > max_var {
                    max_var = abs;
                }
            }
        }
    }
    (max_var, num_clauses, num_binary)
}

fn proof_format_name(format: ProofFormat) -> &'static str {
    match format {
        ProofFormat::Drat => "drat",
        ProofFormat::Lrat => "lrat",
        ProofFormat::Lean4 => "lean4",
        ProofFormat::Alethe => "alethe",
        ProofFormat::Veripb => "veripb",
    }
}

fn dimacs_original_clauses_from_literals(clauses: &[Vec<Literal>]) -> Vec<(u64, Vec<i32>)> {
    clauses
        .iter()
        .enumerate()
        .map(|(idx, clause)| {
            (
                idx as u64 + 1,
                clause.iter().map(|lit| lit.to_dimacs()).collect(),
            )
        })
        .collect()
}

fn summary_route_profile(
    variant: SolverVariant,
    proof_config: Option<&ProofConfig>,
) -> VariantRouteProfile {
    let lrat_mode = proof_config.is_some_and(|proof| {
        matches!(
            proof.format,
            ProofFormat::Lrat | ProofFormat::Lean4 | ProofFormat::Alethe
        )
    });
    let lrat_output = proof_config.is_some_and(|proof| matches!(proof.format, ProofFormat::Lrat));
    let official_main_default_lrat = official_sat_main_regular_route_from_env()
        && matches!(variant, SolverVariant::Default)
        && lrat_mode
        && lrat_output;

    if official_main_default_lrat {
        VariantRouteProfile::OfficialSatCompMainLrat
    } else {
        VariantRouteProfile::Standard
    }
}

fn summary_route_fail_closed(route_profile: VariantRouteProfile) -> bool {
    official_sat_main_regular_route_from_env()
        && !matches!(route_profile, VariantRouteProfile::OfficialSatCompMainLrat)
}

fn emit_sat_applied_run_summary(
    policy: &str,
    policy_source: &str,
    route_profile: VariantRouteProfile,
    proof_config: Option<&ProofConfig>,
) {
    // `-q`/`--quiet` suppresses AY's provenance commentary; the policy preamble
    // is pure stderr commentary, so skip it entirely. stdout/proof/exit-code
    // paths are untouched.
    if super::quiet_enabled() {
        return;
    }
    let proof_active = proof_config.is_some();
    let proof_format = proof_config
        .map(|proof| proof_format_name(proof.format))
        .unwrap_or("none");
    let proof_origin = match proof_config {
        Some(proof) if proof.is_temp => "temporary",
        Some(_) => "file",
        None => "none",
    };
    let verify_proof = if super::VERIFY_PROOF_ENABLED.load(Ordering::SeqCst) {
        "on"
    } else {
        "off"
    };

    safe_eprintln!("c --- SAT applied run ---");
    safe_eprintln!("c sat.policy: {policy}");
    safe_eprintln!("c sat.policy_source: {policy_source}");
    safe_eprintln!("c sat.route_profile: {}", route_profile.as_str());
    safe_eprintln!(
        "c sat.route_fail_closed: {}",
        if summary_route_fail_closed(route_profile) {
            "yes"
        } else {
            "no"
        }
    );
    safe_eprintln!("c sat.guidance_loaded: no");
    safe_eprintln!(
        "c sat.proof_active: {}",
        if proof_active { "yes" } else { "no" }
    );
    safe_eprintln!("c sat.proof_format: {proof_format}");
    safe_eprintln!("c sat.proof_origin: {proof_origin}");
    safe_eprintln!("c sat.verify_proof: {verify_proof}");
}

#[derive(Debug, Clone)]
struct SatCompetitionJitMetadata {
    artifact_id: &'static str,
    application_counter: &'static str,
    requested_mode: String,
    candidate_mode: &'static str,
    mode_present: bool,
    fail_closed: bool,
}

impl SatCompetitionJitMetadata {
    fn runtime_fail_closed(&self, application_count: u64, metadata_present: bool) -> bool {
        !metadata_present
            || self.fail_closed
            || ((self.candidate_mode == "current" || self.candidate_mode == "solver-program")
                && application_count == 0)
    }

    fn native_dispatch(&self, application_count: u64, metadata_present: bool) -> bool {
        metadata_present
            && (self.candidate_mode == "current" || self.candidate_mode == "solver-program")
            && application_count > 0
            && !self.runtime_fail_closed(application_count, metadata_present)
    }
}

fn trimmed_env_value(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}

fn sat_native_helper_competition_jit_metadata() -> SatCompetitionJitMetadata {
    match trimmed_env_value("AY_COMPETITION_JIT_MODE") {
        Some(value) if value.eq_ignore_ascii_case("off") => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "off",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) if value.eq_ignore_ascii_case("current") => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "current",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) if value.eq_ignore_ascii_case("solver-program") => SatCompetitionJitMetadata {
            artifact_id: SAT_WHOLE_LOOP_GUARD_ARTIFACT,
            application_counter: SAT_WHOLE_LOOP_GUARD_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "solver-program",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) if value.eq_ignore_ascii_case("profile-only") => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "profile-only",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "off",
            mode_present: true,
            fail_closed: true,
        },
        None => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: "off".to_string(),
            candidate_mode: "off",
            mode_present: false,
            fail_closed: true,
        },
    }
}

fn sat_native_helper_competition_jit_evidence(
    jit: &SatCompetitionJitMetadata,
    application_count: u64,
) -> stats_output::CompetitionJitEvidence {
    stats_output::CompetitionJitEvidence {
        track: "sat".to_string(),
        artifact_id: jit.artifact_id.to_string(),
        candidate_mode: jit.candidate_mode.to_string(),
        application_counter: Some(stats_output::CompetitionJitApplicationCounter {
            key: jit.application_counter.to_string(),
            value: application_count,
        }),
    }
}

fn enrich_sat_native_helper_competition_jit_json(
    map: &mut serde_json::Map<String, serde_json::Value>,
    jit: &SatCompetitionJitMetadata,
    application_count: u64,
    metadata_present: bool,
) {
    map.insert("competition_track".to_string(), serde_json::json!("sat"));
    map.insert(
        "competition_jit_artifact".to_string(),
        serde_json::json!(jit.artifact_id),
    );
    map.insert(
        "competition_jit_mode".to_string(),
        serde_json::json!(jit.candidate_mode),
    );
    map.insert(
        "competition_jit_application_counter".to_string(),
        serde_json::json!(jit.application_counter),
    );

    if !map
        .get("competition_jit")
        .is_some_and(serde_json::Value::is_object)
    {
        map.insert(
            "competition_jit".to_string(),
            serde_json::json!({
                "track": "sat",
                "artifact_id": jit.artifact_id,
                "candidate_mode": jit.candidate_mode,
                "application_counter": {
                    "key": jit.application_counter,
                    "value": application_count,
                },
            }),
        );
    }
    let Some(competition_jit) = map
        .get_mut("competition_jit")
        .and_then(serde_json::Value::as_object_mut)
    else {
        return;
    };
    competition_jit.insert("schema_version".to_string(), serde_json::json!(1));
    competition_jit.insert("artifact".to_string(), serde_json::json!(jit.artifact_id));
    competition_jit.insert(
        "requested_mode".to_string(),
        serde_json::json!(jit.requested_mode.as_str()),
    );
    competition_jit.insert(
        "native_dispatch".to_string(),
        serde_json::json!(jit.native_dispatch(application_count, metadata_present)),
    );
    competition_jit.insert(
        "fail_closed".to_string(),
        serde_json::json!(jit.runtime_fail_closed(application_count, metadata_present)),
    );
}
