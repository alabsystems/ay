// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Feature-driven inprocessing technique gating for single-thread SAT.
//!
//! After a static variant preset is applied (via [`VariantConfig::apply_to_solver`]),
//! this module adjusts the inprocessing feature profile based on instance-specific
//! features extracted from the CNF formula. This bridges the gap between the
//! portfolio solver (which uses features for multi-thread strategy selection) and
//! single-thread mode (which previously applied a static preset regardless of
//! formula structure).
//!
//! ## Threshold Rules
//!
//! The adjustments are conservative overrides — they only *disable* techniques
//! that are demonstrably harmful for a given instance class, or *enable*
//! techniques known to help. They never override the variant preset in the
//! "wrong direction" (e.g., enabling a technique that the variant intentionally
//! disabled).
//!
//! | Rule | Condition | Action | Reference |
//! |------|-----------|--------|-----------|
//! | Conditioning ratio gate | `clause_var_ratio > 100.0` | Disable conditioning | CaDiCaL `conditionmaxrat=100` |
//! | Random k-SAT symmetry | `class == Random3Sat` | Disable symmetry | No exploitable symmetry |
//! | Industrial/large reorder | `class == Industrial` or `num_vars > 50_000` | Disable reorder | Expensive on large formulas |

use crate::features::{InstanceClass, SatFeatures};
use crate::InprocessingFeatureProfile;

/// Maximum clause-to-variable ratio for conditioning to remain enabled.
///
/// CaDiCaL's `conditionmaxrat` option defaults to 100: conditioning (GBCE)
/// becomes prohibitively expensive when the formula is highly over-constrained
/// because each conditioning round scans all clauses against root-level
/// assignments.
const CONDITION_MAX_RATIO: f64 = 100.0;

/// Variable count threshold above which reorder is disabled.
///
/// Kissat's clause-weighted VMTF queue reorder is O(n log n) in the number of
/// variables. On large industrial formulas (>50K vars), the overhead exceeds
/// the benefit.
const REORDER_MAX_VARS: usize = 50_000;

fn circuit_equiv_throughput_profile_enabled() -> bool {
    ay_core::sat_ab_switches().circuit_equiv_throughput_profile
}

/// Adjust an inprocessing feature profile based on instance features.
///
/// This function applies conservative, feature-driven overrides to the profile
/// that was initially set by a variant preset. It is intended to be called
/// after `VariantConfig::apply_to_solver` and before solving begins.
///
/// The function only modifies toggles where instance features provide a clear
/// signal. It returns `true` if any adjustment was made.
///
/// # Arguments
///
/// * `features` - Static syntactic features extracted from the CNF formula.
/// * `class` - Instance class derived from the features.
/// * `profile` - Mutable reference to the feature profile to adjust.
pub fn adjust_features_for_instance(
    features: &SatFeatures,
    class: &InstanceClass,
    profile: &mut InprocessingFeatureProfile,
) -> bool {
    adjust_features_for_instance_with_circuit_equiv_profile(
        features,
        class,
        profile,
        circuit_equiv_throughput_profile_enabled(),
    )
}

fn adjust_features_for_instance_with_circuit_equiv_profile(
    features: &SatFeatures,
    class: &InstanceClass,
    profile: &mut InprocessingFeatureProfile,
    circuit_equiv_throughput_profile_enabled: bool,
) -> bool {
    let mut changed = false;

    // Rule 1: Conditioning ratio gate.
    // CaDiCaL conditionmaxrat=100: disable conditioning on highly over-constrained
    // formulas where the scan cost per round exceeds the benefit.
    if features.clause_var_ratio > CONDITION_MAX_RATIO && profile.condition {
        profile.condition = false;
        changed = true;
    }

    // Rule 2: Random k-SAT has no exploitable symmetry or backbone.
    // Random formulas are structurally symmetric by construction, so symmetry
    // breaking preprocessing cannot find useful symmetries to break.
    // Backbone detection is also unproductive: random formulas near the phase
    // transition rarely have backbone literals.
    if matches!(
        *class,
        InstanceClass::Random3Sat | InstanceClass::RandomKSat
    ) {
        if profile.symmetry {
            profile.symmetry = false;
            changed = true;
        }
        if profile.backbone {
            profile.backbone = false;
            changed = true;
        }
    }

    // Rule 3: Re-enable symmetry for small structured formulas (#8190).
    // Symmetry defaults OFF (CaDiCaL has none), but AY uniquely solves
    // two-trees-511v via symmetry breaking. Re-enable when the formula is
    // small enough for the symmetry detector (< 4096 vars) and not random.
    let suppress_small_formula_symmetry_reenable = circuit_equiv_throughput_profile_enabled
        && features.looks_like_binary_ternary_multiplier_equivalence();

    if !profile.symmetry
        && features.num_vars < 4096
        && !matches!(
            *class,
            InstanceClass::Random3Sat | InstanceClass::RandomKSat
        )
        && !suppress_small_formula_symmetry_reenable
    {
        profile.symmetry = true;
        changed = true;
    }

    // Rule 4: Industrial/large formulas — disable reorder.
    // Kissat-style clause-weighted VMTF reorder is O(n log n) and the constant
    // factor is high. On large industrial formulas the overhead exceeds benefit.
    if (*class == InstanceClass::Industrial || features.num_vars > REORDER_MAX_VARS)
        && profile.reorder
    {
        profile.reorder = false;
        changed = true;
    }

    changed
}

/// Returns whether reorder should be disabled based on instance features.
///
/// This logic is now also handled by [`adjust_features_for_instance`] which
/// writes the reorder toggle directly into the `InprocessingFeatureProfile`.
/// Retained for internal test coverage of the reorder threshold rule.
#[cfg(test)]
#[must_use]
pub(crate) fn should_disable_reorder(features: &SatFeatures, class: &InstanceClass) -> bool {
    *class == InstanceClass::Industrial || features.num_vars > REORDER_MAX_VARS
}

#[cfg(test)]
mod tests;
