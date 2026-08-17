// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing technique control registry.
//!
//! Centralizes the `(enabled, next_conflict)` scheduling state for each
//! inprocessing technique. Follows CaDiCaL's X-macro pattern
//! (`reference/cadical/src/options.hpp`) translated to Rust `macro_rules!`.
//!
//! See: the development design notes

/// Per-technique scheduling control: enabled flag + next-conflict threshold.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TechniqueControl {
    pub enabled: bool,
    pub next_conflict: u64,
    /// Tracks the last interval used by `reschedule_growing` so successive
    /// calls grow from the previous value. Initialized to the base interval.
    interval_used: u64,
}

impl TechniqueControl {
    #[inline]
    pub(crate) const fn new(enabled: bool, next_conflict: u64) -> Self {
        Self {
            enabled,
            next_conflict,
            interval_used: next_conflict,
        }
    }

    /// Check if technique should fire given current conflict count.
    #[inline]
    pub(crate) fn should_fire(&self, num_conflicts: u64) -> bool {
        self.enabled && num_conflicts >= self.next_conflict
    }

    /// Current growing-interval state used for the next backoff calculation.
    #[inline]
    pub(crate) const fn interval_used(&self) -> u64 {
        self.interval_used
    }

    /// Schedule the next firing `interval` conflicts from `current`.
    #[inline]
    pub(crate) fn reschedule(&mut self, current: u64, interval: u64) {
        self.next_conflict = current + interval;
    }

    /// Reset the growing interval state to `base`. Called during
    /// preprocessing/incremental resets so the growth sequence restarts.
    #[inline]
    pub(crate) fn reset_interval(&mut self, base: u64) {
        self.next_conflict = base;
        self.interval_used = base;
    }

    /// Schedule with a growing interval: each call multiplies the previous
    /// interval by `growth_numer / growth_denom` (e.g., 3/2 = 1.5x),
    /// clamped to `[base_interval, max_interval]`.
    ///
    /// CaDiCaL doubles the BVE elimination bound each round (elim.cpp:971).
    /// For subsumption a gentler 1.5x avoids starving simplification while
    /// reducing the 47% overhead that dominates crn_11_99.
    #[inline]
    pub(crate) fn reschedule_growing(
        &mut self,
        current: u64,
        base_interval: u64,
        growth_numer: u64,
        growth_denom: u64,
        max_interval: u64,
    ) -> u64 {
        let grown = self.interval_used.saturating_mul(growth_numer) / growth_denom;
        let interval = grown.max(base_interval).min(max_interval);
        self.interval_used = interval;
        self.next_conflict = current + interval;
        interval
    }
}

/// How much a pass may mutate SAT state when it runs.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InprocessingMutability {
    ObserveOnly,
    ClauseDatabase,
    VariableMapping,
    ExtensionVariables,
    OrderingOnly,
}

/// Proof formats supported by an inprocessing pass.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InprocessingProofSupport {
    All,
    DratOnly,
    None,
}

#[allow(dead_code)]
impl InprocessingProofSupport {
    #[inline]
    const fn from_transform(transform: ProofTransform) -> Self {
        match transform {
            // Decompose DRAT unclamped 2026-07-09, Congruence 2026-07-10
            // (wf_ff5991a1) — see PROOF_CAPABILITY_REGISTRY in
            // proof_capability.rs — the enforcing table; this advisory
            // descriptor mirrors the registry defaults and does not reflect
            // the --sat-no-drat-subst kill-switch.
            ProofTransform::Bve
            | ProofTransform::Factor
            | ProofTransform::Sbva
            | ProofTransform::Decompose
            | ProofTransform::Congruence => Self::DratOnly,
            ProofTransform::Sweep | ProofTransform::Symmetry => Self::None,
            ProofTransform::Inprobe
            | ProofTransform::Vivify
            | ProofTransform::VivifyIrred
            | ProofTransform::Subsume
            | ProofTransform::Probe
            | ProofTransform::Backbone
            | ProofTransform::Bce
            | ProofTransform::Condition
            | ProofTransform::Transred
            | ProofTransform::Htr
            | ProofTransform::Gate
            | ProofTransform::Cce
            | ProofTransform::Reorder => Self::All,
        }
    }

    #[inline]
    const fn allows(self, mode: InprocessingPolicyMode) -> bool {
        match (self, mode) {
            (Self::All, _) => true,
            (
                Self::DratOnly,
                InprocessingPolicyMode::Search | InprocessingPolicyMode::DratProof,
            ) => true,
            (Self::DratOnly, InprocessingPolicyMode::LratProof) => false,
            (Self::None, InprocessingPolicyMode::Search) => true,
            (Self::None, InprocessingPolicyMode::DratProof | InprocessingPolicyMode::LratProof) => {
                false
            }
        }
    }
}

/// Solver mode used by the compatibility policy.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InprocessingPolicyMode {
    Search,
    DratProof,
    LratProof,
}

/// Static pass descriptor consumed by the compatibility policy.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct InprocessingPassDescriptor {
    pub name: &'static str,
    pub default_enabled: bool,
    pub default_interval: u64,
    pub mutability: InprocessingMutability,
    pub proof_support: InprocessingProofSupport,
    pub preserves_model: bool,
    pub incremental_safe: bool,
    pub state_effect: &'static str,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InprocessingPolicyDecision {
    Run,
    Disable,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InprocessingPolicyReason {
    Enabled,
    DisabledByFeature,
    DisabledByProofMode,
}

/// Append-only policy record for one compatibility-policy decision.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct InprocessingLedgerEntry {
    pub pass: &'static InprocessingPassDescriptor,
    pub decision: InprocessingPolicyDecision,
    pub reason: InprocessingPolicyReason,
}

/// Generates the `InprocessingControls` struct and a `new()` constructor
/// from a technique table. Each technique gets typed field access with
/// zero overhead (direct struct field, no HashMap).
///
/// Each technique declares its proof transform identity. The executable
/// proof-mode allow/deny table lives in `proof_capability.rs`; the local pass
/// descriptor preserves architecture metadata for ledgers and diagnostics.
macro_rules! define_inproc_controls {
    ($(
        $name:ident: default_enabled = $enabled:expr,
                     default_interval = $interval:expr,
                     proof_transform = $proof_transform:expr,
                     mutability = $mutability:expr,
                     preserves_model = $preserves_model:expr,
                     incremental_safe = $incremental_safe:expr,
                     state_effect = $state_effect:expr;
    )*) => {
        /// Centralized inprocessing scheduling controls.
        ///
        /// Each technique has an `enabled` flag and a `next_conflict` threshold.
        /// Replaces the flat `next_*` + `*_enabled` fields that were duplicated
        /// across `Solver::new()` and `Solver::with_proof_output()`.
        #[derive(Debug, Clone)]
        pub(crate) struct InprocessingControls {
            $( pub $name: TechniqueControl, )*
        }

        impl InprocessingControls {
            #[allow(dead_code)]
            pub(super) const PASS_DESCRIPTORS: &'static [InprocessingPassDescriptor] = &[
                $(
                    InprocessingPassDescriptor {
                        name: stringify!($name),
                        default_enabled: $enabled,
                        default_interval: $interval,
                        mutability: $mutability,
                        proof_support: InprocessingProofSupport::from_transform($proof_transform),
                        preserves_model: $preserves_model,
                        incremental_safe: $incremental_safe,
                        state_effect: $state_effect,
                    },
                )*
            ];

            /// Create controls with default values (no proof logging).
            pub(super) fn new() -> Self {
                Self {
                    $( $name: TechniqueControl::new($enabled, $interval), )*
                }
            }

            /// Apply proof-mode overrides: disable techniques incompatible
            /// with the active proof format.
            pub(super) fn with_proof_overrides(self, is_lrat: bool) -> Self {
                self.with_proof_overrides_for_route(is_lrat, false)
            }

            /// Apply proof-mode overrides. The internal dense factor->BVE LRAT
            /// route uses a scoped preprocessing driver and must not globally
            /// reopen proof-incomplete transforms.
            pub(super) fn with_proof_overrides_for_route(
                mut self,
                is_lrat: bool,
                _allow_dense_factor_bve_lrat: bool,
            ) -> Self {
                let proof_mode = ProofMode::from_lrat_enabled(is_lrat);
                $(
                    if !proof_capability::transform_allowed(proof_mode, $proof_transform) {
                        self.$name.enabled = false;
                    }
                )*
                self
            }

            /// Emit compatibility-policy decisions for every registered pass.
            #[allow(dead_code)]
            pub(super) fn compatibility_policy_ledger(
                &self,
                mode: InprocessingPolicyMode,
            ) -> Vec<InprocessingLedgerEntry> {
                let mut entries = Vec::with_capacity(Self::PASS_DESCRIPTORS.len());
                $(
                    let pass = Self::PASS_DESCRIPTORS
                        .iter()
                        .find(|descriptor| descriptor.name == stringify!($name))
                        .expect("generated pass descriptor must exist");
                    let (decision, reason) = if !self.$name.enabled {
                        (
                            InprocessingPolicyDecision::Disable,
                            InprocessingPolicyReason::DisabledByFeature,
                        )
                    } else if !pass.proof_support.allows(mode) {
                        (
                            InprocessingPolicyDecision::Disable,
                            InprocessingPolicyReason::DisabledByProofMode,
                        )
                    } else {
                        (
                            InprocessingPolicyDecision::Run,
                            InprocessingPolicyReason::Enabled,
                        )
                    };
                    entries.push(InprocessingLedgerEntry {
                        pass,
                        decision,
                        reason,
                    });
                )*
                entries
            }
        }
    };
}

// ─── Technique Table ─────────────────────────────────────────────
//
// ONE line per technique. Adding a new technique requires only adding
// a row here (plus the engine field in Solver and the run method).
//
// Intervals use the constants from mod.rs. We import them via super.

use super::{
    BACKBONE_INTERVAL, BCE_INTERVAL, CCE_INTERVAL, CONDITION_INTERVAL, FACTOR_INTERVAL,
    HTR_INTERVAL, INPROBE_INTERVAL, PROBE_INTERVAL, REORDER_INTERVAL, SBVA_INTERVAL,
    SUBSUME_INTERVAL, SWEEP_INTERVAL, TRANSRED_INTERVAL, VIVIFY_INTERVAL, VIVIFY_IRRED_INTERVAL,
};
use crate::proof_capability::{self, ProofMode, ProofTransform};

define_inproc_controls! {
    // Unified inprocessing round timer (#4851 Wave 2).
    // CaDiCaL: inprobe() runs ALL techniques as a single pipeline on one schedule.
    // Interval grows logarithmically: 10 * INPROBE_INTERVAL * log10(phase + 9).
    inprobe:      default_enabled = true,  default_interval = INPROBE_INTERVAL,      proof_transform = ProofTransform::Inprobe,     mutability = InprocessingMutability::ObserveOnly,        preserves_model = true,  incremental_safe = true,  state_effect = "pipeline-schedule";
    vivify:       default_enabled = true,  default_interval = VIVIFY_INTERVAL,       proof_transform = ProofTransform::Vivify,      mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = true,  state_effect = "strengthen-clauses";
    vivify_irred: default_enabled = true,  default_interval = VIVIFY_IRRED_INTERVAL, proof_transform = ProofTransform::VivifyIrred, mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = true,  state_effect = "strengthen-irredundant-clauses";
    subsume:      default_enabled = true,  default_interval = SUBSUME_INTERVAL,      proof_transform = ProofTransform::Subsume,     mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = true,  state_effect = "delete-subsumed-clauses";
    probe:        default_enabled = true,  default_interval = PROBE_INTERVAL,        proof_transform = ProofTransform::Probe,       mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = true,  state_effect = "failed-literal-units";
    backbone:     default_enabled = true,  default_interval = BACKBONE_INTERVAL,     proof_transform = ProofTransform::Backbone,    mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = true,  state_effect = "backbone-units";
    bve:          default_enabled = false, default_interval = 0,                     proof_transform = ProofTransform::Bve,         mutability = InprocessingMutability::VariableMapping,    preserves_model = true,  incremental_safe = false, state_effect = "eliminate-variables";
    bce:          default_enabled = false, default_interval = BCE_INTERVAL,          proof_transform = ProofTransform::Bce,         mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = false, state_effect = "delete-blocked-clauses";
    condition:    default_enabled = false, default_interval = CONDITION_INTERVAL,    proof_transform = ProofTransform::Condition,   mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = false, state_effect = "condition-clauses";
    decompose:    default_enabled = false, default_interval = 0,                     proof_transform = ProofTransform::Decompose,   mutability = InprocessingMutability::VariableMapping,    preserves_model = true,  incremental_safe = false, state_effect = "substitute-components";
    factor:       default_enabled = true,  default_interval = FACTOR_INTERVAL,       proof_transform = ProofTransform::Factor,      mutability = InprocessingMutability::ExtensionVariables, preserves_model = true,  incremental_safe = false, state_effect = "factor-extension-variables";
    sbva:         default_enabled = true,  default_interval = SBVA_INTERVAL,         proof_transform = ProofTransform::Sbva,        mutability = InprocessingMutability::ExtensionVariables, preserves_model = true,  incremental_safe = false, state_effect = "structured-extension-variables";
    transred:     default_enabled = true,  default_interval = TRANSRED_INTERVAL,     proof_transform = ProofTransform::Transred,    mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = true,  state_effect = "delete-transitive-binaries";
    htr:          default_enabled = true,  default_interval = HTR_INTERVAL,          proof_transform = ProofTransform::Htr,         mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = true,  state_effect = "hyper-binary-units";
    gate:         default_enabled = true,  default_interval = 0,                     proof_transform = ProofTransform::Gate,        mutability = InprocessingMutability::ObserveOnly,        preserves_model = true,  incremental_safe = true,  state_effect = "detect-gates";
    congruence:   default_enabled = false, default_interval = 0,                     proof_transform = ProofTransform::Congruence,  mutability = InprocessingMutability::VariableMapping,    preserves_model = true,  incremental_safe = false, state_effect = "rewrite-equivalences";
    sweep:        default_enabled = true,  default_interval = SWEEP_INTERVAL,        proof_transform = ProofTransform::Sweep,       mutability = InprocessingMutability::VariableMapping,    preserves_model = true,  incremental_safe = false, state_effect = "sat-sweep-equivalences";
    cce:          default_enabled = false, default_interval = CCE_INTERVAL,          proof_transform = ProofTransform::Cce,         mutability = InprocessingMutability::ClauseDatabase,     preserves_model = true,  incremental_safe = false, state_effect = "delete-covered-clauses";
    reorder:      default_enabled = true,  default_interval = REORDER_INTERVAL,      proof_transform = ProofTransform::Reorder,     mutability = InprocessingMutability::OrderingOnly,        preserves_model = true,  incremental_safe = true,  state_effect = "reorder-branch-queue";
}

#[cfg(test)]
#[path = "inproc_control_tests.rs"]
mod tests;
