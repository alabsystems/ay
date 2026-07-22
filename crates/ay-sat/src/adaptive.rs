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

const CIRCUIT_EQUIV_THROUGHPUT_PROFILE_ENV: &str = "AY_SAT_CIRCUIT_EQUIV_THROUGHPUT_PROFILE";

fn circuit_equiv_throughput_profile_env_value_enabled(value: &str) -> bool {
    matches!(
        value.trim().to_ascii_lowercase().as_str(),
        "1" | "true" | "yes" | "on"
    )
}

fn circuit_equiv_throughput_profile_enabled() -> bool {
    std::env::var(CIRCUIT_EQUIV_THROUGHPUT_PROFILE_ENV)
        .is_ok_and(|value| circuit_equiv_throughput_profile_env_value_enabled(&value))
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
mod tests {
    use super::*;
    use crate::features::{InstanceClass, SatFeatures};
    use crate::literal::{Literal, Variable};

    /// Helper: create a positive literal for variable index `v`.
    fn pos(v: u32) -> Literal {
        Literal::positive(Variable(v))
    }

    /// Helper: create a negative literal for variable index `v`.
    fn neg(v: u32) -> Literal {
        Literal::negative(Variable(v))
    }

    fn rotating_var(num_vars: usize, seed: usize, offset: usize) -> u32 {
        ((seed.wrapping_mul(17).wrapping_add(offset)) % num_vars) as u32
    }

    fn multiplier_equivalence_like_clauses(num_vars: usize) -> Vec<Vec<Literal>> {
        let mut clauses = Vec::with_capacity(8_500);
        clauses.push(vec![pos(0)]);

        for i in 0..3_400 {
            clauses.push(vec![
                neg(rotating_var(num_vars, i, 1)),
                pos(rotating_var(num_vars, i, 2)),
            ]);
        }

        for i in 0..2_299 {
            clauses.push(vec![
                neg(rotating_var(num_vars, i, 3)),
                neg(rotating_var(num_vars, i, 4)),
                pos(rotating_var(num_vars, i, 5)),
            ]);
        }

        for i in 0..2_800 {
            clauses.push(vec![
                pos(rotating_var(num_vars, i, 6)),
                pos(rotating_var(num_vars, i, 7)),
                neg(rotating_var(num_vars, i, 8)),
            ]);
        }

        clauses
    }

    /// Baseline profile with all features enabled (for testing overrides).
    fn all_enabled_profile() -> InprocessingFeatureProfile {
        InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: true,
            vivify: true,
            subsume: true,
            probe: true,
            bve: true,
            bce: true,
            condition: true,
            decompose: true,
            factor: true,
            sbva: true,
            transred: true,
            htr: true,
            gate: true,
            congruence: true,
            sweep: true,
            backbone: true,
            symmetry: true,
            reorder: true,
            cce: true,
        }
    }

    /// Baseline profile matching the conservative DIMACS default.
    fn dimacs_default_profile() -> InprocessingFeatureProfile {
        InprocessingFeatureProfile {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: true,
            vivify: true,
            subsume: true,
            probe: true,
            bve: false,
            bce: false,
            condition: false,
            decompose: false,
            factor: true,
            sbva: true,
            transred: true,
            htr: true,
            gate: true,
            congruence: false,
            sweep: true,
            backbone: true,
            symmetry: false,
            reorder: true,
            cce: false,
        }
    }

    #[test]
    fn test_adjust_conditioning_ratio_gate_disables_above_threshold() {
        // clause_var_ratio = 200 / 1 = 200.0 > 100.0
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.clause_var_ratio = 200.0;
        features.num_vars = 2000;
        let class = InstanceClass::Structured;
        let mut profile = all_enabled_profile();

        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(changed);
        assert!(
            !profile.condition,
            "conditioning should be disabled for ratio > 100"
        );
    }

    #[test]
    fn test_adjust_conditioning_ratio_gate_keeps_below_threshold() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.clause_var_ratio = 50.0;
        features.num_vars = 2000;
        let class = InstanceClass::Structured;
        let mut profile = all_enabled_profile();

        let _changed = adjust_features_for_instance(&features, &class, &mut profile);

        // No change from conditioning gate (ratio below threshold).
        // Other rules may or may not fire depending on features.
        assert!(
            profile.condition,
            "conditioning should remain enabled for ratio < 100"
        );
    }

    #[test]
    fn test_adjust_conditioning_already_disabled_no_change() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.clause_var_ratio = 200.0;
        features.num_vars = 2000;
        let class = InstanceClass::Structured;
        let mut profile = dimacs_default_profile();
        // condition is already false in dimacs default

        let _changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(!profile.condition);
        // changed may or may not be true depending on other rules
    }

    #[test]
    fn test_adjust_random3sat_disables_symmetry() {
        // Build a random-3-SAT-like instance.
        let num_vars = 2000;
        let num_clauses = 8000;
        let clauses: Vec<Vec<Literal>> = (0..num_clauses)
            .map(|i| {
                let v0 = (i * 3) as u32 % num_vars as u32;
                let v1 = (i * 3 + 1) as u32 % num_vars as u32;
                let v2 = (i * 3 + 2) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1), pos(v2)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Random3Sat);

        let mut profile = all_enabled_profile();
        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(changed);
        assert!(
            !profile.symmetry,
            "symmetry should be disabled for Random3Sat"
        );
    }

    #[test]
    fn test_adjust_random3sat_symmetry_already_disabled() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 2000;
        let class = InstanceClass::Random3Sat;
        let mut profile = all_enabled_profile();
        profile.symmetry = false;

        let _changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(!profile.symmetry);
    }

    #[test]
    fn test_circuit_equiv_throughput_profile_defaults_off_for_symmetry_reenable() {
        let clauses = multiplier_equivalence_like_clauses(2_500);
        let features = SatFeatures::extract(2_500, &clauses);
        assert!(features.looks_like_binary_ternary_multiplier_equivalence());
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Unknown);
        let mut profile = dimacs_default_profile();

        let changed = adjust_features_for_instance_with_circuit_equiv_profile(
            &features,
            &class,
            &mut profile,
            false,
        );

        assert!(changed, "default behavior should still re-enable symmetry");
        assert!(
            profile.symmetry,
            "env-default behavior must preserve small-formula symmetry re-enable"
        );
    }

    #[test]
    fn test_circuit_equiv_throughput_profile_suppresses_symmetry_reenable_when_enabled() {
        let clauses = multiplier_equivalence_like_clauses(2_500);
        let features = SatFeatures::extract(2_500, &clauses);
        assert!(features.looks_like_binary_ternary_multiplier_equivalence());
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Unknown);
        let mut profile = dimacs_default_profile();

        let changed = adjust_features_for_instance_with_circuit_equiv_profile(
            &features,
            &class,
            &mut profile,
            true,
        );

        assert!(
            !changed,
            "profile env should only suppress the symmetry re-enable for this shape"
        );
        assert!(
            !profile.symmetry,
            "enabled circuit-equivalence probe should keep symmetry disabled"
        );
    }

    #[test]
    fn test_circuit_equiv_throughput_profile_requires_truthy_env() {
        assert!(circuit_equiv_throughput_profile_env_value_enabled("1"));
        assert!(circuit_equiv_throughput_profile_env_value_enabled("true"));
        assert!(circuit_equiv_throughput_profile_env_value_enabled("YES"));
        assert!(circuit_equiv_throughput_profile_env_value_enabled(" on "));
        assert!(!circuit_equiv_throughput_profile_env_value_enabled(""));
        assert!(!circuit_equiv_throughput_profile_env_value_enabled("0"));
        assert!(!circuit_equiv_throughput_profile_env_value_enabled("false"));
    }

    #[test]
    fn test_circuit_equiv_throughput_profile_does_not_suppress_nonmatching_shape() {
        let clauses: Vec<Vec<Literal>> = (0..1000)
            .map(|i| {
                let v0 = (i * 2) as u32 % 500;
                let v1 = (i * 2 + 1) as u32 % 500;
                vec![pos(v0), neg(v1)]
            })
            .collect();
        let features = SatFeatures::extract(500, &clauses);
        assert!(!features.looks_like_binary_ternary_multiplier_equivalence());
        let class = InstanceClass::classify(&features);
        let mut profile = dimacs_default_profile();

        let changed = adjust_features_for_instance_with_circuit_equiv_profile(
            &features,
            &class,
            &mut profile,
            true,
        );

        assert!(changed);
        assert!(
            profile.symmetry,
            "enabled env must not suppress unrelated small structured formulas"
        );
    }

    #[test]
    fn test_adjust_industrial_disables_reorder() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 100_000;
        let class = InstanceClass::Industrial;

        assert!(should_disable_reorder(&features, &class));
    }

    #[test]
    fn test_adjust_industrial_disables_reorder_in_profile() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 100_000;
        let class = InstanceClass::Industrial;
        let mut profile = all_enabled_profile();

        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(changed);
        assert!(
            !profile.reorder,
            "reorder should be disabled for Industrial class"
        );
    }

    #[test]
    fn test_adjust_large_vars_disables_reorder_in_profile() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 60_000;
        let class = InstanceClass::Structured;
        let mut profile = all_enabled_profile();

        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        assert!(changed);
        assert!(
            !profile.reorder,
            "reorder should be disabled for >50K vars regardless of class"
        );
    }

    #[test]
    fn test_adjust_large_vars_disables_reorder() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 60_000;
        let class = InstanceClass::Structured; // not industrial, but large

        assert!(
            should_disable_reorder(&features, &class),
            "reorder should be disabled for >50K vars regardless of class"
        );
    }

    #[test]
    fn test_adjust_small_vars_keeps_reorder() {
        let mut features = SatFeatures::extract(1, &[vec![pos(0)]]);
        features.num_vars = 5_000;
        let class = InstanceClass::Structured;

        assert!(
            !should_disable_reorder(&features, &class),
            "reorder should remain enabled for small structured instances"
        );
    }

    #[test]
    fn test_adjust_small_horn_does_not_enable_bce() {
        // Rule 4 (removed in #8132): BCE is NOT force-enabled on small Horn-heavy
        // formulas. The old rule caused 4x regression on battleship.
        let num_vars = 500;
        let clauses: Vec<Vec<Literal>> = (0..1000)
            .map(|i| {
                let v0 = (i * 2) as u32 % num_vars as u32;
                let v1 = (i * 2 + 1) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Small);

        let mut profile = dimacs_default_profile(); // bce = false
        let _changed = adjust_features_for_instance(&features, &class, &mut profile);

        // Rule 3 may re-enable symmetry on small formulas, but BCE must stay off.
        assert!(
            !profile.bce,
            "BCE must NOT be force-enabled (#8132 regression fix)"
        );
    }

    #[test]
    fn test_adjust_no_change_on_typical_structured() {
        // Medium structured instance: no rule fires on dimacs default profile.
        let num_vars = 5000;
        let clauses: Vec<Vec<Literal>> = (0..10_000)
            .map(|i| {
                let v0 = (i * 2) as u32 % num_vars as u32;
                let v1 = (i * 2 + 1) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        let class = InstanceClass::classify(&features);
        assert_eq!(class, InstanceClass::Structured);

        let mut profile = dimacs_default_profile();
        let changed = adjust_features_for_instance(&features, &class, &mut profile);

        // clause_var_ratio = 10000/5000 = 2.0 (below 100)
        // not Random3Sat
        // not Small
        // conditioning already off in dimacs default
        assert!(
            !changed,
            "no adjustments expected for typical structured instance with dimacs default"
        );
    }
}
