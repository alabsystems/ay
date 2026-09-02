// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact compatibility-environment provenance for startup feature gates.

use super::GateStages;
use crate::auto::DecisionSource;
use crate::features::{InstanceClass, SatFeatures};
use crate::proof_capability::ProofMode;
use crate::variant::{
    SolverVariant, VariantConfig, VariantProofMode, VariantRouteProfile,
    BVE_SMALL_CIRCUIT_MAX_DENSITY, BVE_SMALL_CIRCUIT_MAX_VARS, BVE_SPARSE_MAX_DENSITY,
    BVE_SPARSE_MAX_VARS,
};

pub(super) fn startup_policy_veto_source(
    config: &VariantConfig,
    route_source: Option<DecisionSource>,
    gate: GateStages,
) -> Option<(DecisionSource, String)> {
    let decided = route_source == Some(DecisionSource::EnvShim("AY_SAT_AI_CLASS"))
        && matches!(config.variant, SolverVariant::Default)
        && matches!(
            config.input().route_profile(),
            VariantRouteProfile::Standard
        )
        && matches!(config.input().proof_mode(), VariantProofMode::Lrat)
        && matches!(gate.capability, "walk" | "warmup")
        && gate.final_state;
    decided.then(|| {
        if startup_phase_initialization_explicitly_enabled() {
            (
                DecisionSource::EnvShim(
                    "AY_SAT_AI_CLASS+AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT",
                ),
                "AY_SAT_AI_CLASS and AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT jointly preserve startup phase initialization".to_string(),
            )
        } else {
            (
                DecisionSource::EnvShim("AY_SAT_AI_CLASS"),
                "AY_SAT_AI_CLASS vetoed official Main/LRAT startup policy".to_string(),
            )
        }
    })
}

fn startup_phase_initialization_explicitly_enabled() -> bool {
    std::env::var("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT").is_ok_and(|value| {
        matches!(
            value.trim().to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "on"
        )
    })
}

pub(super) fn drat_substitution_env_source(
    mode: ProofMode,
    variant: SolverVariant,
    gate: GateStages,
) -> Option<(DecisionSource, String)> {
    if !matches!(mode, ProofMode::Drat)
        || !matches!(gate.capability, "decompose" | "congruence")
        || !ay_core::sat_ab_switches().no_drat_subst
    {
        return None;
    }
    if gate.nominal || gate.before_proof {
        return Some((
            DecisionSource::Cli,
            "--sat-no-drat-subst proof clamp".to_string(),
        ));
    }
    (matches!(variant, SolverVariant::Default) && ay_core::sat_ab_switches().no_subst_auto).then(
        || {
            (
                DecisionSource::Cli,
                "--sat-no-subst-auto and --sat-no-drat-subst redundantly disable substitution"
                    .to_string(),
            )
        },
    )
}

pub(super) fn resolved_env_source(
    config: &VariantConfig,
    gate: GateStages,
) -> Option<(DecisionSource, String)> {
    if !matches!(config.variant, SolverVariant::Default) {
        return None;
    }
    match gate.capability {
        "congruence" | "decompose" => substitution_env_source(gate.capability),
        "bve" => bve_env_source(config),
        _ => None,
    }
}

fn substitution_env_source(capability: &str) -> Option<(DecisionSource, String)> {
    // B36: the CONGRUENCE/DECOMPOSE force-enable shims are gone; the one
    // operator influence left on these gates is the substitution-AUTO kill.
    let _ = capability;
    ay_core::sat_ab_switches()
        .no_subst_auto
        .then(|| (DecisionSource::Cli, "--sat-no-subst-auto".to_string()))
}

fn bve_env_source(config: &VariantConfig) -> Option<(DecisionSource, String)> {
    let num_vars = config.input().num_vars();
    if matches!(config.input().proof_mode(), VariantProofMode::Lrat) || num_vars == 0 {
        return None;
    }
    let density = config.input().num_clauses() as f64 / num_vars as f64;
    let max_vars_env = ay_core::sat_ab_switches()
        .bve_sparse_max_vars
        .filter(|value| *value > 0);
    let max_density_env = ay_core::sat_ab_switches()
        .bve_sparse_max_density
        .filter(|value| value.is_finite() && *value > 0.0);
    let max_vars = max_vars_env.unwrap_or(BVE_SPARSE_MAX_VARS);
    let max_density = max_density_env.unwrap_or(BVE_SPARSE_MAX_DENSITY);
    let default_vars_admitted = num_vars <= BVE_SPARSE_MAX_VARS;
    // Mirror of the real gate's fixed-edge small-circuit arm (variant.rs
    // `sparse_band_bve_unlock_active`, 14bd679a6): a small, sparse instance is
    // re-admitted after the tunable density check fails. The arm is identical
    // in the default and configured worlds — fixed edges, no env knob — so it
    // can never make the tunables look decisive, which is exactly what this
    // provenance mirror exists to report truthfully.
    let small_circuit_admitted =
        num_vars <= BVE_SMALL_CIRCUIT_MAX_VARS && density <= BVE_SMALL_CIRCUIT_MAX_DENSITY;
    let default_density_admitted = density <= BVE_SPARSE_MAX_DENSITY || small_circuit_admitted;
    let configured_vars_admitted = num_vars <= max_vars;
    let configured_density_admitted = density <= max_density || small_circuit_admitted;
    let kill_present = ay_core::sat_ab_switches().no_bve_sparse;
    let vars_present = max_vars_env.is_some();
    let density_present = max_density_env.is_some();
    let current = !kill_present && configured_vars_admitted && configured_density_admitted;
    let admission = |remove_kill: bool, remove_vars: bool, remove_density: bool| {
        (!kill_present || remove_kill)
            && if remove_vars {
                default_vars_admitted
            } else {
                configured_vars_admitted
            }
            && if remove_density {
                default_density_admitted
            } else {
                configured_density_admitted
            }
    };
    let kill_changed = kill_present && admission(true, false, false) != current;
    let vars_changed = vars_present && admission(false, true, false) != current;
    let density_changed = density_present && admission(false, false, true) != current;
    let mut decisive = (kill_changed, vars_changed, density_changed);
    if decisive == (false, false, false) {
        for candidate in [
            (kill_present, vars_present, false),
            (kill_present, false, density_present),
            (false, vars_present, density_present),
            (kill_present, vars_present, density_present),
        ] {
            if candidate != (false, false, false)
                && admission(candidate.0, candidate.1, candidate.2) != current
            {
                decisive = candidate;
                break;
            }
        }
    }
    let source = match decisive {
        // B34: any attribution involving the kill is a CLI decision
        // (--sat-no-bve-sparse); the value knobs keep their env identity.
        (true, _, _) => DecisionSource::Cli,
        (false, true, false) | (false, false, true) | (false, true, true) => DecisionSource::Cli,
        (false, false, false) => return None,
    };
    Some((
        source,
        format!(
            "compatibility BVE controls jointly change admission: kill={kill_present} num_vars={num_vars} max_vars={max_vars} clause_var_ratio={density:.3} max_density={max_density}"
        ),
    ))
}

pub(super) fn circuit_equiv_symmetry_cli_decided(
    features: &SatFeatures,
    instance_class: InstanceClass,
    gate: GateStages,
) -> bool {
    gate.capability == "symmetry"
        && !gate.final_state
        && !gate.resolved
        && features.num_vars < 4096
        && !matches!(
            instance_class,
            InstanceClass::Random3Sat | InstanceClass::RandomKSat
        )
        && features.looks_like_binary_ternary_multiplier_equivalence()
        && ay_core::sat_ab_switches().circuit_equiv_throughput_profile
}

pub(super) fn declared_clause_var_ratio(config: &VariantConfig) -> f64 {
    config.input().num_clauses() as f64 / config.input().num_vars().max(1) as f64
}
