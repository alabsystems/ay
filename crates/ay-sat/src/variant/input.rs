// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed input metadata for SAT variant planning.

use super::{VariantRouteProfile, VariantStartupPolicy};
use crate::proof_capability::ProofMode;

/// Proof posture requested while resolving a SAT variant.
///
/// This is planning metadata, not runtime proof authority. The solver derives
/// authoritative proof state from installed proof output and internal
/// LRAT/trace state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantProofMode {
    /// Resolve a non-proof profile.
    Disabled,
    /// Resolve a DRAT proof profile.
    Drat,
    /// Resolve an LRAT proof profile.
    Lrat,
}

impl VariantProofMode {
    pub(super) const fn capability_mode(self) -> Option<ProofMode> {
        match self {
            Self::Disabled => None,
            Self::Drat => Some(ProofMode::Drat),
            Self::Lrat => Some(ProofMode::Lrat),
        }
    }
}

/// Input facts used to resolve a preset into concrete solver settings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VariantInput {
    num_vars: usize,
    num_clauses: usize,
    proof_mode: VariantProofMode,
    startup_policy: VariantStartupPolicy,
    route_profile: VariantRouteProfile,
    dense_mutex_focused_restart_gate_experiment: bool,
    dense_clique_mab_branch_experiment: bool,
    bve_lrat_scout_route: bool,
    fmla_decompose_lrat_preflight_route: bool,
}

impl VariantInput {
    /// Construct variant input metadata.
    #[must_use]
    pub const fn new(num_vars: usize, num_clauses: usize, proof_mode: VariantProofMode) -> Self {
        Self {
            num_vars,
            num_clauses,
            proof_mode,
            startup_policy: VariantStartupPolicy::Preserve,
            route_profile: VariantRouteProfile::Standard,
            dense_mutex_focused_restart_gate_experiment: false,
            dense_clique_mab_branch_experiment: false,
            bve_lrat_scout_route: false,
            fmla_decompose_lrat_preflight_route: false,
        }
    }

    /// Number of variables in the input formula.
    #[must_use]
    pub const fn num_vars(self) -> usize {
        self.num_vars
    }

    /// Number of clauses in the input formula.
    #[must_use]
    pub const fn num_clauses(self) -> usize {
        self.num_clauses
    }

    /// Proof posture requested for variant planning.
    #[must_use]
    pub const fn proof_mode(self) -> VariantProofMode {
        self.proof_mode
    }

    /// Startup phase-initialization policy for this route.
    #[must_use]
    pub const fn startup_policy(self) -> VariantStartupPolicy {
        self.startup_policy
    }

    /// Frontend-selected route profile, before formula-class adaptation.
    #[must_use]
    pub const fn route_profile(self) -> VariantRouteProfile {
        self.route_profile
    }

    /// Whether the dense-mutex focused restart experiment was requested.
    #[must_use]
    pub const fn dense_mutex_focused_restart_gate_experiment(self) -> bool {
        self.dense_mutex_focused_restart_gate_experiment
    }

    /// Whether the dense-clique MAB branch experiment was requested.
    #[must_use]
    pub const fn dense_clique_mab_branch_experiment(self) -> bool {
        self.dense_clique_mab_branch_experiment
    }

    /// Whether the bounded Main/LRAT BVE scout route was requested.
    #[must_use]
    pub const fn bve_lrat_scout_route(self) -> bool {
        self.bve_lrat_scout_route
    }

    /// Whether the Fmla Main/LRAT decompose preflight route was requested.
    #[must_use]
    pub const fn fmla_decompose_lrat_preflight_route(self) -> bool {
        self.fmla_decompose_lrat_preflight_route
    }

    pub(super) const fn capability_mode(self) -> Option<ProofMode> {
        self.proof_mode.capability_mode()
    }

    /// Return this input with an explicit startup phase-initialization policy.
    #[must_use]
    pub const fn with_startup_policy(mut self, startup_policy: VariantStartupPolicy) -> Self {
        self.startup_policy = startup_policy;
        self
    }

    /// Return this input with an explicit frontend route profile.
    #[must_use]
    pub const fn with_route_profile(mut self, route_profile: VariantRouteProfile) -> Self {
        self.route_profile = route_profile;
        self
    }

    /// Enable the dense-mutex focused restart gate experiment.
    #[must_use]
    pub const fn with_dense_mutex_focused_restart_gate_experiment(mut self) -> Self {
        self.dense_mutex_focused_restart_gate_experiment = true;
        self
    }

    /// Enable the dense-clique MAB branch experiment.
    #[must_use]
    pub const fn with_dense_clique_mab_branch_experiment(mut self) -> Self {
        self.dense_clique_mab_branch_experiment = true;
        self
    }

    /// Enable the bounded Main/LRAT BVE scout route.
    #[must_use]
    pub const fn with_bve_lrat_scout_route(mut self) -> Self {
        self.bve_lrat_scout_route = true;
        self
    }

    /// Enable the Fmla Main/LRAT decompose preflight route.
    #[must_use]
    pub const fn with_fmla_decompose_lrat_preflight_route(mut self) -> Self {
        self.fmla_decompose_lrat_preflight_route = true;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_mode_maps_to_exactly_one_capability_posture() {
        assert_eq!(VariantProofMode::Disabled.capability_mode(), None);
        assert_eq!(
            VariantProofMode::Drat.capability_mode(),
            Some(ProofMode::Drat)
        );
        assert_eq!(
            VariantProofMode::Lrat.capability_mode(),
            Some(ProofMode::Lrat)
        );
    }

    #[test]
    fn input_defaults_and_enable_builders_preserve_typed_proof_mode() {
        let defaults = VariantInput::new(7, 11, VariantProofMode::Lrat);
        assert_eq!(defaults.startup_policy(), VariantStartupPolicy::Preserve);
        assert_eq!(defaults.route_profile(), VariantRouteProfile::Standard);
        assert!(!defaults.dense_mutex_focused_restart_gate_experiment());
        assert!(!defaults.dense_clique_mab_branch_experiment());
        assert!(!defaults.bve_lrat_scout_route());
        assert!(!defaults.fmla_decompose_lrat_preflight_route());

        let input = defaults
            .with_dense_mutex_focused_restart_gate_experiment()
            .with_dense_clique_mab_branch_experiment()
            .with_bve_lrat_scout_route()
            .with_fmla_decompose_lrat_preflight_route();

        assert_eq!(input.num_vars(), 7);
        assert_eq!(input.num_clauses(), 11);
        assert_eq!(input.proof_mode(), VariantProofMode::Lrat);
        assert!(input.dense_mutex_focused_restart_gate_experiment());
        assert!(input.dense_clique_mab_branch_experiment());
        assert!(input.bve_lrat_scout_route());
        assert!(input.fmla_decompose_lrat_preflight_route());
    }
}
