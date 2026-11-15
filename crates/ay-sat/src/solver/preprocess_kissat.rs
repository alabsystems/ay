// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kissat 4.0.4's initial preprocessing (`--sat-preprocess-kissat`).
//!
//! Kissat's `preprocess` (`preprocess.c:29-120`, one round by default) runs
//! `probe_initially` (`probe.c:45-66`) and then `fastel`, which is off in
//! 4.0.4. `probe_initially` is, in order: congruence closure, substituting if
//! it found anything; the binary-implication backbone; sweeping, substituting
//! if it found anything; substitution if neither did; and factoring behind
//! `log10(active) <= eliminations + factordelay` (`factor.c:1068-1085`). No
//! elimination, failed-literal probing, ternary resolution, subsumption or
//! vivification runs before search, so elimination first runs in search at
//! Kissat's initial limit (`kimits.c:123-128`).
//!
//! Under the switch this module replaces the preprocessing round's passes
//! after the level-0 collection and symmetry breaking. It keeps AY's own
//! guards that are about AY's implementation rather than the schedule: the
//! congruence size caps (for decompose too), the dense-formula decompose
//! guard, and the AUTO collapse probe's verdict unless `--sat-subst-kissat`
//! overrides it. Sweeping runs at every size, as in Kissat. In-search elimination is armed where AY's
//! preprocessing would arm it (the post-collapse and giant raw unlocks), and
//! its first limit is Kissat's.

use super::config_preprocess_cleanup::PreprocessStageControl;
use super::inprocessing::kissat_eliminate_interval_nlog2n;
use super::*;

/// `--sat-preprocess-kissat`.
pub(super) fn preprocess_kissat_enabled() -> bool {
    ay_core::sat_ab_switches().preprocess_kissat == Some(true)
}

/// The preprocessing policy gates the Kissat round keeps.
#[derive(Clone, Copy)]
pub(super) struct KissatPreprocessGates {
    pub(super) skip_gate_dependent_passes: bool,
    pub(super) skip_congruence: bool,
    pub(super) skip_dense_formula: bool,
}

impl Solver {
    /// One round of Kissat's `probe_initially`, then the in-search
    /// elimination arming (see the module comment).
    pub(super) fn preprocess_kissat_round<F>(
        &mut self,
        gates: KissatPreprocessGates,
        should_stop: &F,
    ) -> PreprocessStageControl
    where
        F: Fn() -> bool + ?Sized,
    {
        let mut can_decompose = self.inproc_ctrl.decompose.enabled
            && !gates.skip_congruence
            && !gates.skip_dense_formula;
        let mut substituted = false;

        if self.preprocessing_should_stop(should_stop) {
            return PreprocessStageControl::ReturnFalse;
        }
        if self.inproc_ctrl.gate.enabled
            && self.inproc_ctrl.congruence.enabled
            && self.inproc_ctrl.decompose.enabled
            && !gates.skip_gate_dependent_passes
            && !gates.skip_congruence
        {
            let equivs_before = self.inproc.congruence.stats().equivalences_found;
            self.set_diagnostic_pass(DiagnosticPass::Congruence);
            let found = if self.subst_kissat_active() {
                self.congruence_kissat_delayed().unwrap_or(false)
            } else {
                self.congruence()
            };
            self.clear_diagnostic_pass();
            if self.propagate_check_unsat() {
                return PreprocessStageControl::Unsat;
            }
            // The AUTO collapse probe's verdict, as on the default path
            // (`config_preprocess.rs`), unless `--sat-subst-kissat` keeps
            // congruence and decompose on.
            if self.cold.subst_auto_collapse && !self.subst_kissat_active() {
                let equivs = self
                    .inproc
                    .congruence
                    .stats()
                    .equivalences_found
                    .saturating_sub(equivs_before);
                let active = self.num_vars.saturating_sub(self.count_fixed_vars()).max(1);
                if (equivs as f64) / (active as f64) < 0.05 {
                    self.inproc_ctrl.decompose.enabled = false;
                    self.inproc_ctrl.congruence.enabled = false;
                    can_decompose = false;
                }
            }
            if found && can_decompose {
                if self.preprocess_kissat_substitute() {
                    return PreprocessStageControl::Unsat;
                }
                substituted = true;
            }
        }

        if self.preprocessing_should_stop(should_stop) {
            return PreprocessStageControl::ReturnFalse;
        }
        if self.inproc_ctrl.backbone.enabled {
            self.set_diagnostic_pass(DiagnosticPass::Backbone);
            self.backbone_binary();
            self.clear_diagnostic_pass();
            if self.propagate_check_unsat() {
                return PreprocessStageControl::Unsat;
            }
        }

        if self.preprocessing_should_stop(should_stop) {
            return PreprocessStageControl::ReturnFalse;
        }
        if self.inproc_ctrl.sweep.enabled && !gates.skip_gate_dependent_passes {
            let rewrites_before = self.inproc.sweeper.stats().clauses_rewritten;
            self.set_diagnostic_pass(DiagnosticPass::Sweep);
            let unsat = self.sweep();
            self.clear_diagnostic_pass();
            if unsat || self.propagate_check_unsat() {
                return PreprocessStageControl::Unsat;
            }
            let rewrote = self.inproc.sweeper.stats().clauses_rewritten > rewrites_before;
            if rewrote && can_decompose {
                if self.preprocess_kissat_substitute() {
                    return PreprocessStageControl::Unsat;
                }
                substituted = true;
            }
        }

        if !substituted && can_decompose && self.preprocess_kissat_substitute() {
            return PreprocessStageControl::Unsat;
        }

        if self.preprocessing_should_stop(should_stop) {
            return PreprocessStageControl::ReturnFalse;
        }
        if self.should_preprocess_factor() {
            self.set_diagnostic_pass(DiagnosticPass::Factor);
            self.factorize();
            self.clear_diagnostic_pass();
            if self.propagate_check_unsat() {
                return PreprocessStageControl::Unsat;
            }
        }

        self.preprocess_kissat_arm_elimination();
        PreprocessStageControl::Continue
    }

    /// Kissat `kissat_substitute`: equivalent-literal substitution over the
    /// binary implication graph. Returns true on UNSAT.
    fn preprocess_kissat_substitute(&mut self) -> bool {
        self.set_diagnostic_pass(DiagnosticPass::Decompose);
        self.decompose();
        self.clear_diagnostic_pass();
        self.propagate_check_unsat()
    }

    /// Arm in-search elimination where AY's preprocessing would (above the
    /// sparse-band cap BVE is off unless a substitution collapse or the giant
    /// raw unlock reopens it) and set its first limit to Kissat's
    /// `INIT_CONFLICT_LIMIT (eliminate, true)`: 500 conflicts scaled by the
    /// irredundant clause count, `kissat_eliminate_interval_nlog2n(C, 1)`.
    fn preprocess_kissat_arm_elimination(&mut self) {
        if self.bve_post_collapse_unlock_active() || self.try_qualify_bve_giant_raw() {
            self.inproc_ctrl.bve.enabled = true;
            self.enforce_inprocessing_proof_overrides();
        }
        let first = kissat_eliminate_interval_nlog2n(self.arena.irredundant_count() as u64, 1);
        self.inproc_ctrl.bve.next_conflict = self.num_conflicts + first;
    }
}
