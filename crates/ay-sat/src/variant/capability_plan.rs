// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resolved variant plans and truthful capability-decision telemetry.

use super::{
    dimacs_baseline_features, minimal_features, probe_features, SolverVariant, VariantConfig,
    VariantInput, VariantStartupPolicy,
};
use crate::auto::{CapabilityDecision, CapabilityLedger, CapabilityState, DecisionSource};
use crate::features::{InstanceClass, SatFeatures};
use crate::proof_capability::{self, ProofMode, ProofTransform};
use crate::{InprocessingFeatureProfile, Solver};

mod adaptive_provenance;
mod env_provenance;
use adaptive_provenance::adaptive_reason;
use env_provenance::{
    circuit_equiv_symmetry_cli_decided, declared_clause_var_ratio, drat_substitution_env_source,
    resolved_env_source, startup_policy_veto_source,
};

/// Fully resolved SAT profile plan after one pre-CDCL classification step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantProfilePlan {
    /// Variant config after formula-class adaptive adjustment.
    pub config: VariantConfig,
    /// Formula class computed from the supplied feature snapshot.
    pub instance_class: InstanceClass,
    /// Whether adaptive profile adjustment changed any feature gate.
    pub adjusted_features: bool,
    /// Every capability decision taken while resolving this plan.
    pub ledger: CapabilityLedger,
}

impl VariantProfilePlan {
    /// Build a profile plan from a variant, input metadata, and formula features.
    #[must_use]
    pub fn for_features(
        variant: SolverVariant,
        input: VariantInput,
        features: &SatFeatures,
    ) -> Self {
        Self::for_features_with_source(variant, input, features, DecisionSource::Default)
    }

    /// Build a profile plan and record which layer selected its named variant.
    /// Frontends pass `Cli` only for a real explicit CLI selection and
    /// `EnvShim("AY_SAT_VARIANT")` only for that exact compatibility fallback.
    /// Formula-driven variant routing passes `Auto`.
    #[must_use]
    pub fn for_features_with_source(
        variant: SolverVariant,
        input: VariantInput,
        features: &SatFeatures,
        variant_source: DecisionSource,
    ) -> Self {
        Self::for_features_with_sources(variant, input, features, variant_source, None)
    }

    /// Build a plan with separate provenance for variant and route selection.
    #[must_use]
    pub fn for_features_with_sources(
        variant: SolverVariant,
        input: VariantInput,
        features: &SatFeatures,
        variant_source: DecisionSource,
        route_source: Option<DecisionSource>,
    ) -> Self {
        Self::from_config_features_with_sources(
            variant.config(input),
            features,
            variant_source,
            route_source,
        )
    }

    /// Add formula-class adaptive adjustment to an already resolved config.
    #[must_use]
    pub fn from_config_features(config: VariantConfig, features: &SatFeatures) -> Self {
        Self::from_config_features_with_source(config, features, DecisionSource::Default)
    }

    /// Add formula-class adaptive adjustment with explicit variant provenance.
    #[must_use]
    pub fn from_config_features_with_source(
        config: VariantConfig,
        features: &SatFeatures,
        variant_source: DecisionSource,
    ) -> Self {
        Self::from_config_features_with_sources(config, features, variant_source, None)
    }

    /// Add formula adaptation with separate variant and route provenance.
    #[must_use]
    pub fn from_config_features_with_sources(
        mut config: VariantConfig,
        features: &SatFeatures,
        variant_source: DecisionSource,
        route_source: Option<DecisionSource>,
    ) -> Self {
        let nominal_features = nominal_variant_features(config.variant);
        let resolved_features = config.features;
        let instance_class = InstanceClass::classify(features);
        let adaptive_adjusted = crate::adaptive::adjust_features_for_instance(
            features,
            &instance_class,
            &mut config.features,
        );
        let adaptive_features = config.features;
        let route_adjusted = config.apply_route_profile_clamps();
        let branch_adjusted = config.apply_feature_adaptive_branch_policy(features);
        let dense_clique_mab_adjusted = config.apply_dense_clique_mab_branch_experiment(features);
        let dense_mutex_restart_adjusted =
            config.apply_dense_mutex_focused_restart_gate_experiment(features);
        let midband_restart_adjusted = config.apply_midband_deep_restart_gate(features);
        let before_proof_features = config.features;
        if config.input.proof_mode {
            proof_capability::apply_profile_permissions(
                &mut config.features,
                ProofMode::from_lrat_enabled(config.input.lrat_mode),
            );
        }
        let proof_adjusted = before_proof_features != config.features;
        let mut startup_features = config.features;
        if startup_phase_initialization_disabled(&config) {
            startup_features.walk = false;
            startup_features.warmup = false;
        }
        let mut ledger = CapabilityLedger::default();
        config.record_capability_decisions(
            features,
            instance_class,
            variant_source,
            route_source,
            FeatureStages {
                nominal: nominal_features,
                resolved: resolved_features,
                adaptive: adaptive_features,
                before_proof: before_proof_features,
            },
            startup_features,
            &mut ledger,
        );
        for &capability in &ay_core::misc_cli_flags().disabled_sat_startup_capabilities {
            ledger.replace_startup_decision(CapabilityDecision {
                capability,
                state: CapabilityState::Off,
                source: DecisionSource::Cli,
                because: "explicit CLI disable".to_string(),
            });
        }
        Self {
            config,
            instance_class,
            ledger,
            adjusted_features: adaptive_adjusted
                || route_adjusted
                || branch_adjusted
                || dense_clique_mab_adjusted
                || dense_mutex_restart_adjusted
                || midband_restart_adjusted
                || proof_adjusted,
        }
    }

    /// Apply this frozen profile plan to a fresh solver.
    pub fn apply_to_solver(&self, solver: &mut Solver) {
        self.config.apply_to_solver(solver);
        solver.set_capability_ledger(self.ledger.clone());
    }

    /// Apply only post-parse feature adaptation and the startup ledger.
    pub fn apply_postparse_to_solver(&self, solver: &mut Solver) {
        solver.apply_feature_profile(&self.config.features);
        solver.set_capability_ledger(self.ledger.clone());
    }
}

#[derive(Clone, Copy)]
struct FeatureStages {
    nominal: InprocessingFeatureProfile,
    resolved: InprocessingFeatureProfile,
    adaptive: InprocessingFeatureProfile,
    before_proof: InprocessingFeatureProfile,
}

#[derive(Clone, Copy)]
struct GateStages {
    capability: &'static str,
    nominal: bool,
    resolved: bool,
    adaptive: bool,
    before_proof: bool,
    final_state: bool,
}

impl VariantConfig {
    fn record_capability_decisions(
        &self,
        features: &SatFeatures,
        instance_class: InstanceClass,
        variant_source: DecisionSource,
        route_source: Option<DecisionSource>,
        stages: FeatureStages,
        startup_features: InprocessingFeatureProfile,
        ledger: &mut CapabilityLedger,
    ) {
        for gate in capability_gates(stages, startup_features) {
            let (source, because) = capability_provenance(
                self,
                features,
                instance_class,
                variant_source,
                route_source,
                gate,
            );
            ledger.record(CapabilityDecision {
                capability: gate.capability,
                state: if gate.final_state {
                    CapabilityState::On
                } else {
                    CapabilityState::Off
                },
                source,
                because,
            });
        }
    }
}

fn nominal_variant_features(variant: SolverVariant) -> InprocessingFeatureProfile {
    match variant {
        SolverVariant::Default | SolverVariant::Aggressive => dimacs_baseline_features(),
        SolverVariant::Minimal => minimal_features(),
        SolverVariant::Probe => probe_features(),
        SolverVariant::Custom(profile) => profile,
    }
}

fn capability_provenance(
    config: &VariantConfig,
    features: &SatFeatures,
    instance_class: InstanceClass,
    variant_source: DecisionSource,
    route_source: Option<DecisionSource>,
    gate: GateStages,
) -> (DecisionSource, String) {
    if let Some(source) = startup_policy_veto_source(config, route_source, gate) {
        return source;
    }
    if startup_policy_decided(config, gate) {
        if startup_phase_initialization_disabled(config) {
            return (
                route_source.unwrap_or(DecisionSource::Auto),
                format!("startup_policy={}", config.input.startup_policy.as_str()),
            );
        }
        return (
            DecisionSource::EnvShim("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT"),
            "AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT enabled startup phase initialization"
                .to_string(),
        );
    }
    if proof_policy_decided(config, features, instance_class, gate) {
        let mode = ProofMode::from_lrat_enabled(config.input.lrat_mode);
        if let Some(source) = drat_substitution_env_source(mode, config.variant, gate) {
            return source;
        }
        return (
            DecisionSource::Auto,
            format!("proof capability policy mode={mode:?}"),
        );
    }
    if route_policy_decided(config, features, instance_class, gate) {
        return (
            route_source.unwrap_or(DecisionSource::Auto),
            format!("route={}", config.input.route_profile.as_str()),
        );
    }
    if gate.resolved != gate.adaptive {
        return adaptive_provenance(gate, features, instance_class);
    }
    if let Some(source) = resolved_env_source(config, gate) {
        return source;
    }
    if gate.nominal != gate.resolved {
        if gate.capability == "condition" && declared_clause_var_ratio(config) > 100.0 {
            return (
                DecisionSource::Auto,
                format!(
                    "declared_clause_var_ratio={:.3} > 100",
                    declared_clause_var_ratio(config)
                ),
            );
        }
        return (
            DecisionSource::Auto,
            format!("resolved {:?} profile policy", config.variant),
        );
    }
    if !config.input.proof_mode
        && !config
            .input
            .route_profile
            .requires_proof_safe_specialist_routing()
        && circuit_equiv_symmetry_cli_decided(features, instance_class, gate)
    {
        return (
            DecisionSource::Cli,
            "circuit-equivalence profile suppressed small-formula symmetry".to_string(),
        );
    }
    default_provenance(variant_source, config.variant, instance_class)
}

fn adaptive_provenance(
    gate: GateStages,
    features: &SatFeatures,
    instance_class: InstanceClass,
) -> (DecisionSource, String) {
    (
        DecisionSource::Auto,
        adaptive_reason(gate.capability, features, instance_class),
    )
}

fn default_provenance(
    source: DecisionSource,
    variant: SolverVariant,
    instance_class: InstanceClass,
) -> (DecisionSource, String) {
    (
        source,
        format!("variant={variant:?} class={instance_class:?}"),
    )
}

fn startup_policy_decided(config: &VariantConfig, gate: GateStages) -> bool {
    if !config
        .input
        .route_profile
        .requires_proof_safe_specialist_routing()
        || !matches!(gate.capability, "walk" | "warmup")
    {
        return false;
    }
    startup_phase_initialization_disabled(config)
        || std::env::var("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT").is_ok_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
}

fn startup_phase_initialization_disabled(config: &VariantConfig) -> bool {
    matches!(
        config.input.startup_policy,
        VariantStartupPolicy::DisableWarmupWalk
    ) && matches!(config.variant, SolverVariant::Default)
        && config.input.lrat_mode
}

fn proof_policy_decided(
    config: &VariantConfig,
    features: &SatFeatures,
    instance_class: InstanceClass,
    gate: GateStages,
) -> bool {
    if !config.input.proof_mode || gate.final_state {
        return false;
    }
    let Some(transform) = proof_transform(gate.capability) else {
        return false;
    };
    let mode = ProofMode::from_lrat_enabled(config.input.lrat_mode);
    !proof_capability::transform_allowed(mode, transform)
        && (gate.nominal
            || gate.before_proof
            || resolved_env_source(config, gate).is_some()
            || circuit_equiv_symmetry_cli_decided(features, instance_class, gate))
}

fn route_policy_decided(
    config: &VariantConfig,
    features: &SatFeatures,
    instance_class: InstanceClass,
    gate: GateStages,
) -> bool {
    config
        .input
        .route_profile
        .requires_proof_safe_specialist_routing()
        && matches!(gate.capability, "sweep" | "symmetry")
        && !gate.final_state
        && (gate.nominal
            || gate.adaptive
            || circuit_equiv_symmetry_cli_decided(features, instance_class, gate))
}

fn proof_transform(capability: &str) -> Option<ProofTransform> {
    Some(match capability {
        "vivify" => ProofTransform::Vivify,
        "subsume" => ProofTransform::Subsume,
        "probe" => ProofTransform::Probe,
        "bve" => ProofTransform::Bve,
        "bce" => ProofTransform::Bce,
        "condition" => ProofTransform::Condition,
        "decompose" => ProofTransform::Decompose,
        "factor" => ProofTransform::Factor,
        "sbva" => ProofTransform::Sbva,
        "transred" => ProofTransform::Transred,
        "htr" => ProofTransform::Htr,
        "gate" => ProofTransform::Gate,
        "congruence" => ProofTransform::Congruence,
        "sweep" => ProofTransform::Sweep,
        "backbone" => ProofTransform::Backbone,
        "reorder" => ProofTransform::Reorder,
        "cce" => ProofTransform::Cce,
        "symmetry" => ProofTransform::Symmetry,
        _ => return None,
    })
}

macro_rules! gate {
    ($name:literal, $field:ident, $stages:ident, $final_state:ident) => {
        GateStages {
            capability: $name,
            nominal: $stages.nominal.$field,
            resolved: $stages.resolved.$field,
            adaptive: $stages.adaptive.$field,
            before_proof: $stages.before_proof.$field,
            final_state: $final_state.$field,
        }
    };
}

fn capability_gates(
    stages: FeatureStages,
    final_state: InprocessingFeatureProfile,
) -> [GateStages; 23] {
    [
        gate!("preprocess", preprocess, stages, final_state),
        gate!("walk", walk, stages, final_state),
        gate!("warmup", warmup, stages, final_state),
        gate!("shrink", shrink, stages, final_state),
        gate!("hbr", hbr, stages, final_state),
        gate!("vivify", vivify, stages, final_state),
        gate!("subsume", subsume, stages, final_state),
        gate!("probe", probe, stages, final_state),
        gate!("bve", bve, stages, final_state),
        gate!("bce", bce, stages, final_state),
        gate!("condition", condition, stages, final_state),
        gate!("decompose", decompose, stages, final_state),
        gate!("factor", factor, stages, final_state),
        gate!("sbva", sbva, stages, final_state),
        gate!("transred", transred, stages, final_state),
        gate!("htr", htr, stages, final_state),
        gate!("gate", gate, stages, final_state),
        gate!("congruence", congruence, stages, final_state),
        gate!("sweep", sweep, stages, final_state),
        gate!("backbone", backbone, stages, final_state),
        gate!("symmetry", symmetry, stages, final_state),
        gate!("reorder", reorder, stages, final_state),
        gate!("cce", cce, stages, final_state),
    ]
}
