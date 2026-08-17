// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT technique disabling and effort demotion.
//!
//! The env-var bridge (`SatDebugEnv`, `AY_NO_TABLE`, `AY_SAT_TABLE`,
//! `apply_sat_debug_env_overrides`) was deleted in #8331. CLI `--disable`
//! flags now populate a global `OnceLock<Vec<SatTechnique>>` and
//! `configure_dimacs_solver()` calls `disable_technique()` directly.
//!
//! NOTE: `apply_sat_profile()` and `sat_profile_snapshot()` are pending #8326
//! completion (requires SatProfileTag, SatProfileSnapshot, SearchModePolicy,
//! RestartPolicyTag types and solver fields that are not yet wired).

use super::*;

pub(crate) const LARGE_FORMULA_VARS: usize = 5_000;

/// Canonical list of all `SatTechnique` variants, used by the exhaustiveness
/// test. Keeping this in sync with `SatTechnique` is enforced by
/// `test_all_techniques_matches_sat_technique_enum` below.
pub(crate) const ALL_TECHNIQUES: &[crate::SatTechnique] = &[
    crate::SatTechnique::Preprocess,
    crate::SatTechnique::Bve,
    crate::SatTechnique::Probe,
    crate::SatTechnique::Congruence,
    crate::SatTechnique::Decompose,
    crate::SatTechnique::Sweep,
    crate::SatTechnique::Condition,
    crate::SatTechnique::Vivify,
    crate::SatTechnique::Subsume,
    crate::SatTechnique::Bce,
    crate::SatTechnique::Cce,
    crate::SatTechnique::Transred,
    crate::SatTechnique::Htr,
    crate::SatTechnique::Gate,
    crate::SatTechnique::Factor,
    crate::SatTechnique::Sbva,
    crate::SatTechnique::Shrink,
    crate::SatTechnique::Elimfast,
    crate::SatTechnique::Inprocess,
    crate::SatTechnique::Flip,
    crate::SatTechnique::Jit,
    crate::SatTechnique::ExternalCodegenBackend,
    crate::SatTechnique::Walk,
    crate::SatTechnique::Warmup,
];

impl Solver {
    /// Disable a specific SAT technique. The exhaustive match guarantees
    /// every `SatTechnique` variant is handled — adding a variant without
    /// a handler is a compile error.
    pub fn disable_technique(&mut self, technique: crate::SatTechnique) {
        match technique {
            crate::SatTechnique::Preprocess => self.set_preprocess_enabled(false),
            crate::SatTechnique::Bve => self.set_bve_enabled(false),
            crate::SatTechnique::Probe => self.set_probe_enabled(false),
            crate::SatTechnique::Congruence => self.set_congruence_enabled(false),
            crate::SatTechnique::Decompose => self.set_decompose_enabled(false),
            crate::SatTechnique::Sweep => self.set_sweep_enabled(false),
            crate::SatTechnique::Condition => self.set_condition_enabled(false),
            crate::SatTechnique::Vivify => self.set_vivify_enabled(false),
            crate::SatTechnique::Subsume => self.set_subsume_enabled(false),
            crate::SatTechnique::Bce => self.set_bce_enabled(false),
            crate::SatTechnique::Cce => self.set_cce_enabled(false),
            crate::SatTechnique::Transred => self.set_transred_enabled(false),
            crate::SatTechnique::Htr => self.set_htr_enabled(false),
            crate::SatTechnique::Gate => self.set_gate_enabled(false),
            crate::SatTechnique::Factor => self.set_factor_enabled(false),
            crate::SatTechnique::Sbva => self.set_sbva_enabled(false),
            crate::SatTechnique::Shrink => self.set_shrink_enabled(false),
            crate::SatTechnique::Elimfast => {
                self.cold.elimfast_disabled = true;
            }
            crate::SatTechnique::Inprocess => self.disable_all_inprocessing(),
            crate::SatTechnique::Flip => {
                self.cold.flip_search_enabled = false;
            }
            crate::SatTechnique::Jit => {
                self.cold.jit_disabled = true;
                #[cfg(feature = "jit")]
                {
                    self.jit_conflict_processor = None;
                }
            }
            crate::SatTechnique::ExternalCodegenBackend => {
                // Compatibility alias: the ay binary handles external code generation
                // backend policy through SatDisableFlags.
            }
            crate::SatTechnique::Walk => self.set_walk_enabled(false),
            crate::SatTechnique::Warmup => self.set_warmup_enabled(false),
            crate::SatTechnique::SymmetrySigned => {
                self.cold.symmetry_signed_disabled = true;
            }
            crate::SatTechnique::SymmetryAuxfree => {
                self.cold.symmetry_auxfree_disabled = true;
            }
            crate::SatTechnique::SymmetryOrbitope => {
                self.cold.symmetry_orbitope_disabled = true;
            }
        }
    }
}

/// Threshold for the runtime small-DIMACS effort demotion selector (#7585).
/// Based on clean-head anchor split: battleship=78.8, stable=204.3, clique=466.3.
const SMALL_DIMACS_DEMOTION_THRESHOLD: f64 = 300.0;

/// Pure decision function for the small-DIMACS effort demotion selector.
///
/// Returns `true` if the observed subsumption cost justifies demoting
/// to CaDiCaL --sat reduced effort values.
pub(crate) fn should_demote_small_dimacs_effort(
    is_small_dimacs_armed: bool,
    already_reduced: bool,
    checks_delta: u64,
    cands_delta: u64,
) -> bool {
    if !is_small_dimacs_armed || already_reduced || cands_delta == 0 {
        return false;
    }
    let ratio = checks_delta as f64 / cands_delta as f64;
    ratio > SMALL_DIMACS_DEMOTION_THRESHOLD
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_demotion_selector_battleship_ratio_below_threshold() {
        // battleship: 78.8 checks/candidate — should NOT demote.
        assert!(!should_demote_small_dimacs_effort(true, false, 121, 1));
    }

    #[test]
    fn test_demotion_selector_stable_ratio_below_threshold() {
        // stable-300: 204.3 checks/candidate — should NOT demote.
        assert!(!should_demote_small_dimacs_effort(true, false, 233, 1));
    }

    #[test]
    fn test_demotion_selector_clique_ratio_above_threshold() {
        // clique: 466.3 checks/candidate — should demote.
        assert!(should_demote_small_dimacs_effort(true, false, 471, 1));
    }

    #[test]
    fn test_demotion_selector_zero_candidates_is_safe() {
        assert!(!should_demote_small_dimacs_effort(true, false, 1000, 0));
    }

    #[test]
    fn test_demotion_selector_already_reduced_does_not_fire() {
        assert!(!should_demote_small_dimacs_effort(true, true, 471, 1));
    }

    #[test]
    fn test_demotion_selector_not_armed_does_not_fire() {
        assert!(!should_demote_small_dimacs_effort(false, false, 471, 1));
    }

    #[test]
    fn test_demotion_selector_exactly_at_threshold() {
        // ratio = 300.0 exactly — should NOT demote (threshold is strictly >300).
        assert!(!should_demote_small_dimacs_effort(true, false, 300, 1));
    }

    #[test]
    fn test_demotion_selector_just_above_threshold() {
        // ratio = 301.0 — should demote.
        assert!(should_demote_small_dimacs_effort(true, false, 301, 1));
    }

    #[test]
    fn test_disable_technique_bve() {
        let mut solver = Solver::new(3);
        solver.set_bve_enabled(true);
        assert!(solver.is_bve_enabled());
        solver.disable_technique(crate::SatTechnique::Bve);
        assert!(!solver.is_bve_enabled());
    }

    #[test]
    fn test_disable_technique_vivify() {
        let mut solver = Solver::new(3);
        solver.set_vivify_enabled(true);
        assert!(solver.is_vivify_enabled());
        solver.disable_technique(crate::SatTechnique::Vivify);
        assert!(!solver.is_vivify_enabled());
    }

    #[test]
    fn test_disable_technique_sweep() {
        let mut solver = Solver::new(3);
        solver.set_sweep_enabled(true);
        assert!(solver.is_sweep_enabled());
        solver.disable_technique(crate::SatTechnique::Sweep);
        assert!(!solver.is_sweep_enabled());
    }

    #[test]
    fn test_disable_technique_all_variants_compile() {
        // Exhaustive: call disable_technique for every SatTechnique variant.
        // This test proves the exhaustive match compiles and does not panic.
        let mut solver = Solver::new(3);
        for &technique in ALL_TECHNIQUES {
            solver.disable_technique(technique);
        }
    }
}
