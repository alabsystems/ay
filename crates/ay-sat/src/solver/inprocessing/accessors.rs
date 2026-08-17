// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing control accessors and scheduling predicates.

use super::*;

/// Generate `set_*_enabled()`, `is_*_enabled()`, and `*_stats()` accessors
/// for inprocessing techniques. All scheduling state lives in `self.inproc_ctrl`.
///
/// Techniques with non-standard stats (factor: by-value, decompose: field access)
/// are kept manual below the macro invocation.
macro_rules! inprocessing_accessors {
    ($(
        $ctrl:ident,
        $(#[$set_attr:meta])*
        $set_vis:vis $set_fn:ident,
        $(#[$is_attr:meta])*
        $is_vis:vis $is_fn:ident,
        $(#[$stats_attr:meta])*
        $stats_vis:vis $stats_fn:ident -> $stats_ty:ty, $engine:ident
    );+ $(;)?) => {$(
        #[doc = "Enable or disable this inprocessing technique."]
        $(#[$set_attr])*
        $set_vis fn $set_fn(&mut self, enabled: bool) {
            self.inproc_ctrl.$ctrl.enabled = enabled;
            self.enforce_inprocessing_proof_overrides();
        }
        #[doc = "Returns whether this inprocessing technique is enabled."]
        $(#[$is_attr])*
        $is_vis fn $is_fn(&self) -> bool {
            self.inproc_ctrl.$ctrl.enabled
        }
        #[doc = "Get cumulative statistics for this inprocessing technique."]
        $(#[$stats_attr])*
        $stats_vis fn $stats_fn(&self) -> &$stats_ty {
            self.inproc.$engine.stats()
        }
    )+};
}

/// Generate `should_*()` scheduling predicates using `self.inproc_ctrl`.
macro_rules! should_inprocess {
    ($fn_name:ident, $ctrl:ident) => {
        pub(in crate::solver) fn $fn_name(&self) -> bool {
            self.inproc_ctrl.$ctrl.should_fire(self.num_conflicts)
        }
    };
}

impl Solver {
    /// Reapply proof-mode inprocessing clamps after public profile/toggle updates.
    ///
    /// Proof-output constructors apply these overrides up front, but callers can
    /// also enter LRAT/clause-trace mode after construction via `enable_lrat()`
    /// or `enable_clause_trace()`. Keep every public setter fail-closed so a
    /// later profile write cannot reopen a proof-incompatible transform.
    #[inline]
    pub(in crate::solver) fn enforce_inprocessing_proof_overrides(&mut self) {
        if self.proof_manager.is_some() || self.cold.lrat_enabled {
            // Snapshot the pristine controls once, before the first
            // (destructive) proof override, so #A2b budget exhaustion can
            // restore full inprocessing power mid-search.
            if self.inproc_ctrl_pre_proof.is_none() {
                self.inproc_ctrl_pre_proof = Some(self.inproc_ctrl.clone());
            }
            let ctrl = self.inproc_ctrl.clone();
            self.inproc_ctrl = ctrl.with_proof_overrides(self.cold.lrat_enabled);
        }
    }

    /// Degrade to no-proof search after the #A2b search-time proof
    /// bookkeeping budget is exhausted (synthesized-default certificates
    /// only; explicit proof modes are never budgeted).
    ///
    /// Called at a safe point (root decision level, between clause
    /// operations, from level-0 unit materialization). The verdict machinery
    /// is unaffected — `--no-proof` runs the whole search this way. The
    /// clause trace keeps its `proof_work_exhausted` marker (entries are
    /// dropped to reclaim memory), so downstream certificate reconstruction
    /// fails closed into the honest "no proof certificate emitted" warning.
    pub(in crate::solver) fn degrade_proof_bookkeeping_after_exhaustion(&mut self) {
        if !self.cold.lrat_enabled {
            return;
        }
        self.cold.lrat_enabled = false;
        if let Some(trace) = self.cold.clause_trace.as_mut() {
            trace.mark_proof_work_exhausted();
            trace.clear_entries();
        }
        // Restore the inprocessing techniques that proof-mode overrides
        // disabled: with no certificate left to protect, the search should
        // run at full (--no-proof) power.
        if let Some(pristine) = self.inproc_ctrl_pre_proof.take() {
            self.inproc_ctrl = pristine;
        }
        tracing::warn!(
            "search-time proof bookkeeping budget exhausted: degraded to              no-proof search (verdict unaffected; synthesized-default              certificate will not be emitted)"
        );
    }

    /// Enable the internal dense factor->BVE LRAT route.
    ///
    /// Default-off. Public LRAT profile/setter application remains fail-closed;
    /// the route driver temporarily opens only the checked preprocessing slice.
    pub(crate) fn set_dense_factor_bve_lrat_route_enabled(&mut self, enabled: bool) {
        self.cold.dense_factor_bve_lrat_route_enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }

    /// Return whether the internal dense factor->BVE LRAT route is enabled.
    pub(crate) fn dense_factor_bve_lrat_route_enabled(&self) -> bool {
        self.cold.dense_factor_bve_lrat_route_enabled
    }

    /// Enable the internal Circuit BVE LRAT retained-plan route.
    ///
    /// Default-off. Public LRAT profile/setter application remains fail-closed;
    /// the route driver temporarily opens only one bounded BVE preprocessing
    /// slice and restores caller controls before returning.
    pub(crate) fn set_circuit_bve_lrat_route_enabled(&mut self, enabled: bool) {
        self.cold.circuit_bve_lrat_route_enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }

    /// Return whether the internal Circuit BVE LRAT route is enabled.
    pub(crate) fn circuit_bve_lrat_route_enabled(&self) -> bool {
        self.cold.circuit_bve_lrat_route_enabled
    }

    /// Enable the internal Main/LRAT bounded BVE scout route.
    ///
    /// Default-off. Public LRAT profile/setter application remains fail-closed;
    /// the route driver temporarily opens only one bounded BVE inprocessing
    /// slice and restores caller controls before returning.
    pub(crate) fn set_bve_lrat_scout_route_enabled(&mut self, enabled: bool) {
        self.cold.bve_lrat_scout_route_enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }

    /// Return whether the internal Main/LRAT bounded BVE scout route is enabled.
    pub(crate) fn bve_lrat_scout_route_enabled(&self) -> bool {
        self.cold.bve_lrat_scout_route_enabled
    }

    /// Enable the sparse-band large-formula preprocess-BVE/fastelim unlock.
    ///
    /// Scoped + kill-switched via the variant sparse-band predicate. When set,
    /// the preprocess BVE pass may run past `skip_expensive_preprocessing_passes`
    /// on genuinely sparse large formulas only; the dense-skip guard is
    /// re-checked at BVE entry so this never runs expensive BVE on a dense
    /// formula, and the preprocess deadline + fastelim wall guard still bound
    /// its cost.
    pub(crate) fn set_sparse_band_bve_preprocess_unlock(&mut self, enabled: bool) {
        self.cold.sparse_band_bve_preprocess_unlock = enabled;
    }

    /// Arm the giant raw-BVE unlock ROUTE flag (lever 3, 2026-07-11
    /// sparse-prize completion round; OPT-IN via AY_AB_BVE_GIANT_RAW=1 —
    /// measured default-OFF, see `VariantConfig::bve_giant_raw_route_active`).
    ///
    /// Set from the resolved variant config when the PARSED shape sits in
    /// the elimination-giant band (Default DIMACS non-LRAT, 150K < vars <=
    /// 2M, clauses <= 8M, density <= 12 — see
    /// `VariantConfig::bve_giant_raw_route_active`). The flag alone changes
    /// nothing: qualification is completed at preprocess time by
    /// `try_qualify_bve_giant_raw` (no-collapse check + live dense-skip
    /// re-check), which latches `cold.bve_giant_raw_qualified`.
    pub(crate) fn set_bve_giant_raw_unlock(&mut self, enabled: bool) {
        self.cold.bve_giant_raw_unlock = enabled;
    }

    /// Arm the route-aware substitution-collapse AUTO probe (campaign #15;
    /// default ON since 2026-07-10, wf_55735963).
    ///
    /// Set from the resolved variant config (Default DIMACS variant only;
    /// kill-switch --sat-no-subst-auto). Gates the expensive
    /// congruence+decompose fixpoint on the one-round equivalence-density
    /// probe and raises the congruence size caps to the AUTO bounds — see
    /// `cold.subst_auto_collapse`.
    pub(crate) fn set_subst_auto_collapse(&mut self, enabled: bool) {
        self.cold.subst_auto_collapse = enabled;
    }

    /// Arm the dense-band guard rails for the DEFAULT-ON AUTO collapse
    /// path (2026-07-11 dense-band regression fix): the EARLY formula-
    /// density disarm in compute_preprocess_policy + the giant decompose
    /// re-run bail in inprocessing_schedule. Set from the resolved variant
    /// config ONLY when AUTO is on via the default path
    /// (`--sat-no-subst-auto` unset); explicit `=1` keeps the historical
    /// uncapped A/B semantics — see `cold.subst_auto_capped`.
    pub(crate) fn set_subst_auto_collapse_capped(&mut self, capped: bool) {
        self.cold.subst_auto_capped = capped;
    }

    /// Arm the giant-band AUTO probe raise (giant-3M loss fix, 2026-07):
    /// raised 4M/10M probe caps + 12s in-band preprocess budget. Set from
    /// the resolved variant config ONLY on the DEFAULT-ON capped path for
    /// NON-PROOF solves (kill-switch `AY_AB_SUBST_AUTO_GIANT=0`; also rides
    /// `--sat-no-subst-auto`) — see `cold.subst_auto_giant`.
    pub(crate) fn set_subst_auto_giant_band(&mut self, enabled: bool) {
        self.cold.subst_auto_giant = enabled;
    }

    /// Enable the internal Main/LRAT Fmla decompose preflight route.
    ///
    /// Default-off. Public LRAT profile/setter application remains fail-closed;
    /// the route driver runs only the existing decompose LRAT preflight and
    /// materializer admission path without enabling destructive decompose.
    pub(crate) fn set_fmla_decompose_lrat_preflight_route_enabled(&mut self, enabled: bool) {
        self.cold.fmla_decompose_lrat_preflight_route_enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }

    /// Return whether the internal Main/LRAT Fmla decompose preflight route is enabled.
    pub(crate) fn fmla_decompose_lrat_preflight_route_enabled(&self) -> bool {
        self.cold.fmla_decompose_lrat_preflight_route_enabled
    }

    /// Enable or disable bounded BVE occurrence-delta validation.
    ///
    /// This is a default-off cold-path saved-state experiment. It does not
    /// enable BVE itself and does not change proof-mode inprocessing clamps.
    pub fn set_bve_occ_delta_validation_enabled(&mut self, enabled: bool) {
        self.inproc.bve.set_occ_delta_validation_enabled(enabled);
    }

    /// Returns whether bounded BVE occurrence-delta validation is enabled.
    pub fn is_bve_occ_delta_validation_enabled(&self) -> bool {
        self.inproc.bve.occ_delta_validation_enabled()
    }

    /// Enable or disable retaining BVE occurrence state across preprocessing
    /// and restart-inprocessing round boundaries.
    ///
    /// This is a default-off measurement candidate. When disabled, BVE still
    /// uses occurrence lists inside the active round, then drops the live
    /// marker so later mutation hooks do not maintain saved state that cannot
    /// be reused.
    pub fn set_bve_occ_saved_state_reuse_enabled(&mut self, enabled: bool) {
        self.inproc.bve.set_occ_saved_state_reuse_enabled(enabled);
    }

    /// Returns whether cross-round BVE occurrence saved-state reuse is enabled.
    pub fn is_bve_occ_saved_state_reuse_enabled(&self) -> bool {
        self.inproc.bve.occ_saved_state_reuse_enabled()
    }

    /// Enable or disable vivification.
    ///
    /// The public vivify toggle controls both learned vivification and the
    /// irredundant-clause tier.
    pub fn set_vivify_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.vivify.enabled = enabled;
        self.inproc_ctrl.vivify_irred.enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }

    /// Returns whether learned vivification is enabled.
    pub fn is_vivify_enabled(&self) -> bool {
        self.inproc_ctrl.vivify.enabled
    }

    /// Get cumulative statistics for vivification.
    pub fn vivify_stats(&self) -> &VivifyStats {
        self.inproc.vivifier.stats()
    }

    // ======== Macro-generated inprocessing accessors (#3546) ========
    //
    // Each technique gets: `set_*_enabled(bool)` + `is_*_enabled()` + `*_stats()`.
    // Exceptions kept manual: vivify (dual control flags), factor_stats
    // (by-value), decompose_stats (field access).
    inprocessing_accessors! {
        subsume, pub set_subsume_enabled, pub is_subsume_enabled,
            pub subsume_stats -> SubsumeStats, subsumer;
        probe, pub set_probe_enabled, pub is_probe_enabled,
            pub probe_stats -> ProbeStats, prober;
        bve, pub set_bve_enabled, pub is_bve_enabled,
            pub bve_stats -> BVEStats, bve;
        bce, pub set_bce_enabled, pub is_bce_enabled,
            pub bce_stats -> BCEStats, bce;
        transred, pub set_transred_enabled, pub is_transred_enabled,
            pub transred_stats -> crate::transred::TransRedStats, transred_engine;
        htr, pub set_htr_enabled, pub is_htr_enabled,
            pub htr_stats -> HTRStats, htr;
        gate, pub set_gate_enabled, pub is_gate_enabled,
            pub gate_stats -> GateStats, gate_extractor;
        congruence, pub set_congruence_enabled, pub is_congruence_enabled,
            pub congruence_stats -> crate::congruence::CongruenceStats, congruence;
        sweep, pub set_sweep_enabled, pub is_sweep_enabled,
            pub sweep_stats -> SweepStats, sweeper;
        cce, pub set_cce_enabled, pub is_cce_enabled,
            pub cce_stats -> crate::cce::CCEStats, cce
    }

    /// Snapshot of root symmetry preprocessing (manual: the stats live on
    /// `cold`, not in the inprocessing bundle).
    pub fn symmetry_report(&self) -> crate::SymmetryReport {
        self.cold.symmetry_stats.report()
    }

    // Conditioning: manual accessors.
    /// Enable or disable conditioning inprocessing.
    pub fn set_condition_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.condition.enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }
    /// Returns whether conditioning inprocessing is enabled.
    pub fn is_condition_enabled(&self) -> bool {
        self.inproc_ctrl.condition.enabled
    }
    /// Get cumulative statistics for conditioning (GBCE).
    #[doc(hidden)]
    pub fn conditioning_stats(&self) -> &crate::condition::ConditioningStats {
        self.inproc.conditioning.stats()
    }

    // Non-standard stats: keep manual.
    /// Get decompose statistics.
    pub fn decompose_stats(&self) -> &crate::decompose::DecomposeStats {
        &self.inproc.decompose_engine.stats
    }
    /// Get formula component decomposition statistics.
    pub fn component_stats(&self) -> &crate::component::ComponentStats {
        &self.cold.component_stats
    }
    /// Get factorization statistics (constructed from solver fields).
    pub fn factor_stats(&self) -> FactorStats {
        FactorStats {
            rounds: self.cold.factor_rounds,
            factored_count: self.cold.factor_factored_total,
            extension_vars: self.cold.factor_extension_vars_total,
        }
    }

    /// Last LRAT factor dry-run sidecars built before fail-closed rejection.
    pub(crate) fn factor_lrat_dry_run_sidecars(&self) -> &[crate::factor::FactorLratDryRunSidecar] {
        self.inproc.factor_engine.lrat_dry_run_sidecars()
    }

    /// Last LRAT decompose dry-run sidecars built before fail-closed rejection.
    pub(crate) fn decompose_lrat_dry_run_sidecars(
        &self,
    ) -> &[crate::decompose::DecomposeLratDryRunSidecar] {
        self.inproc.decompose_engine.lrat_dry_run_sidecars()
    }

    /// LRAT factor preflight counters independent of applied factor stats.
    pub(crate) fn factor_lrat_preflight_stats(&self) -> crate::factor::FactorLratPreflightStats {
        self.inproc.factor_engine.lrat_preflight_stats()
    }

    /// LRAT decompose preflight counters independent of applied decompose stats.
    pub fn decompose_lrat_preflight_stats(&self) -> DecomposeLratPreflightStats {
        self.inproc.decompose_engine.lrat_preflight_stats()
    }

    /// Execution-path preprocessing transaction counters.
    pub fn preprocessing_transaction_stats(
        &self,
    ) -> crate::preprocess_transaction::PreprocessTransactionStats {
        self.inproc.preprocess_transactions.stats()
    }

    // Additional setters/getters for techniques with non-standard stats.
    /// Enable or disable factorization inprocessing.
    pub fn set_factor_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.factor.enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }
    /// Enable or disable SCC decomposition inprocessing.
    pub fn set_decompose_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.decompose.enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }
    /// Returns whether factorization inprocessing is enabled.
    #[cfg(test)]
    pub(crate) fn is_factor_enabled(&self) -> bool {
        self.inproc_ctrl.factor.enabled
    }
    /// Enable or disable SBVA inprocessing.
    pub fn set_sbva_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.sbva.enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }
    /// Returns whether SBVA inprocessing is enabled.
    #[cfg(test)]
    pub(crate) fn is_sbva_enabled(&self) -> bool {
        self.inproc_ctrl.sbva.enabled
    }
    /// Returns whether SCC decomposition inprocessing is enabled.
    #[cfg(test)]
    pub(crate) fn is_decompose_enabled(&self) -> bool {
        self.inproc_ctrl.decompose.enabled
    }
    /// Returns whether hyper-binary resolution is enabled during probing.
    pub fn is_hbr_enabled(&self) -> bool {
        self.hbr_enabled
    }
    /// Returns whether clause shrinking (vivification) is enabled.
    pub fn is_shrink_enabled(&self) -> bool {
        self.shrink_enabled
    }
    /// Enable or disable hyper-binary resolution during probing.
    pub fn set_hbr_enabled(&mut self, enabled: bool) {
        self.hbr_enabled = enabled;
    }
    /// Returns whether experimental LRAT probe parent-chain learning is enabled.
    pub fn is_lrat_probe_parent_chain_enabled(&self) -> bool {
        self.lrat_probe_parent_chain_enabled
    }
    /// Enable or disable experimental LRAT probe parent-chain learning.
    pub fn set_lrat_probe_parent_chain_enabled(&mut self, enabled: bool) {
        self.lrat_probe_parent_chain_enabled = enabled;
    }
    /// Returns whether experimental LRAT proof-clamp probe rescue is enabled.
    pub fn lrat_proof_clamp_probe_rescue_enabled(&self) -> bool {
        self.lrat_proof_clamp_probe_rescue_enabled
    }
    /// Enable or disable experimental LRAT proof-clamp probe rescue.
    pub fn set_lrat_proof_clamp_probe_rescue_enabled(&mut self, enabled: bool) {
        self.lrat_proof_clamp_probe_rescue_enabled = enabled;
    }
    /// Enable or disable the default-off #9084 scheduler productivity rescue.
    ///
    /// When enabled, a productive backbone or decompose pass counts as
    /// inprocessing round productivity for the round-level backoff decision.
    pub fn set_inprocessing_yield_productivity_rescue_enabled(&mut self, enabled: bool) {
        self.inprocessing_yield_productivity_rescue_enabled = enabled;
    }
    /// Returns whether the #9084 scheduler productivity rescue is enabled.
    pub fn inprocessing_yield_productivity_rescue_enabled(&self) -> bool {
        self.inprocessing_yield_productivity_rescue_enabled
    }
    /// Enable or disable the default-off #9084 yield-rescue backbone cooldown.
    ///
    /// When enabled, a low-simplification round that is productive only
    /// because the yield-rescue experiment observed backbone/decompose yield
    /// keeps the rescued inprobe cadence but delays the shared backbone row.
    pub fn set_inprocessing_yield_rescue_backbone_cooldown_enabled(&mut self, enabled: bool) {
        self.inprocessing_yield_rescue_backbone_cooldown_enabled = enabled;
    }
    /// Returns whether the #9084 yield-rescue backbone cooldown is enabled.
    pub fn inprocessing_yield_rescue_backbone_cooldown_enabled(&self) -> bool {
        self.inprocessing_yield_rescue_backbone_cooldown_enabled
    }
    /// Enable or disable the default-off #9084 bounded-backbone backoff.
    ///
    /// When enabled, zero-decompose-yield rounds with expensive bounded-CDCL
    /// backbone work can delay the next bounded-CDCL backbone pass without
    /// changing binary-backbone admission.
    pub fn set_bounded_backbone_zero_decompose_backoff_enabled(&mut self, enabled: bool) {
        self.bounded_backbone_zero_decompose_backoff_enabled = enabled;
    }
    /// Returns whether the #9084 bounded-backbone backoff is enabled.
    pub fn bounded_backbone_zero_decompose_backoff_enabled(&self) -> bool {
        self.bounded_backbone_zero_decompose_backoff_enabled
    }
    /// Enable or disable same-round post-vivify binary-backbone admission.
    pub fn set_backbone_post_vivify_binary_admission_enabled(&mut self, enabled: bool) {
        self.cold.backbone_post_vivify_binary_admission = enabled;
    }
    /// Returns whether same-round post-vivify binary-backbone admission is enabled.
    pub fn backbone_post_vivify_binary_admission_enabled(&self) -> bool {
        self.cold.backbone_post_vivify_binary_admission
    }
    /// Enable or disable backbone literal computation.
    pub fn set_backbone_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.backbone.enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }
    /// Returns whether backbone literal computation is enabled.
    pub fn is_backbone_enabled(&self) -> bool {
        self.inproc_ctrl.backbone.enabled
    }
    /// Enable or disable Kissat-style clause-weighted VMTF queue reorder.
    pub fn set_reorder_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.reorder.enabled = enabled;
        self.enforce_inprocessing_proof_overrides();
    }

    /// Returns whether Kissat-style clause-weighted VMTF queue reorder is enabled.
    pub fn is_reorder_enabled(&self) -> bool {
        self.inproc_ctrl.reorder.enabled
    }

    /// Disable all inprocessing techniques.
    ///
    /// For ephemeral solver instances (e.g., CHC DPLL(T) checks) where the solver
    /// is created fresh for each query, inprocessing is pure overhead: reductions
    /// don't carry over and the problems are typically small. This also eliminates
    /// noisy diagnostic output (CONDITIONING round messages) from repeated solves.
    pub fn disable_all_inprocessing(&mut self) {
        self.inproc_ctrl.vivify.enabled = false;
        self.inproc_ctrl.vivify_irred.enabled = false;
        self.inproc_ctrl.subsume.enabled = false;
        self.inproc_ctrl.probe.enabled = false;
        self.inproc_ctrl.bve.enabled = false;
        self.inproc_ctrl.bce.enabled = false;
        self.inproc_ctrl.condition.enabled = false;
        self.inproc_ctrl.decompose.enabled = false;
        self.inproc_ctrl.factor.enabled = false;
        self.inproc_ctrl.sbva.enabled = false;
        self.inproc_ctrl.transred.enabled = false;
        self.inproc_ctrl.htr.enabled = false;
        self.inproc_ctrl.gate.enabled = false;
        self.inproc_ctrl.congruence.enabled = false;
        self.inproc_ctrl.sweep.enabled = false;
        self.inproc_ctrl.backbone.enabled = false;
        self.inproc_ctrl.cce.enabled = false;
        self.inproc_ctrl.reorder.enabled = false;
    }

    /// Enable or disable block-level shrinking in conflict analysis.
    pub fn set_shrink_enabled(&mut self, enabled: bool) {
        self.shrink_enabled = enabled;
    }

    // ======== Destructive inprocessing guard (#5031, #3662) ========

    /// Permanently disable destructive inprocessing techniques.
    ///
    /// Called when the solver enters incremental mode (push/pop) or when a
    /// second solve() is performed on the same instance (#5031, #3662).
    /// Destructive techniques (conditioning, BVE, BCE, sweep, congruence,
    /// factorize, decompose) rewrite the clause database in ways that cannot
    /// be reversed across solve boundaries or push/pop scopes.
    ///
    /// Sets `has_been_incremental` which is checked by each destructive
    /// technique's entry function. Does NOT modify `inproc_ctrl.*.enabled`
    /// flags, preserving the user-facing feature profile (#5166).
    pub fn disable_destructive_inprocessing(&mut self) {
        self.cold.has_been_incremental = true;
    }

    // ======== Inprocessing precondition helpers (#5074) ========

    /// Level-0 precondition check shared by all inprocessing entry points.
    ///
    /// Asserts (in debug) that the solver is at decision level 0 and returns
    /// `false` in release builds when the precondition is violated, allowing
    /// callers to bail out with their own return convention (`return;` or
    /// `return false;`).
    #[inline]
    pub(super) fn require_level_zero(&self) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: inprocessing at decision level {}",
            self.decision_level,
        );
        self.decision_level == 0
    }

    /// Combined inprocessing entry guard: level-0 check + reason mark sync.
    ///
    /// Most inprocessing techniques need both `require_level_zero()` and
    /// `ensure_reason_clause_marks_current()` at entry. This method combines
    /// them into a single call to reduce boilerplate.
    ///
    /// Techniques that call `ensure_reason_clause_marks_current()` later
    /// (e.g., congruence, factorize) or not at all (e.g., probe, backbone)
    /// should continue using `require_level_zero()` directly.
    #[inline]
    pub(super) fn enter_inprocessing(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }
        self.ensure_reason_clause_marks_current();
        true
    }

    // ======== Adaptive tick-threshold scaling (#8099) ========

    /// Adaptive tick-threshold scaling factor (#8099).
    ///
    /// When the measured per-round inprocessing overhead (rebuild_watches,
    /// trail re-propagation) is low, techniques benefit from more frequent
    /// firing because the cost of entering an inprocessing round is small.
    /// Returns a factor in `(0, 1]` that is multiplied into tick thresholds.
    ///
    /// Granular scaling based on measured overhead (#8099):
    /// - <1ms overhead: 0.25x (very aggressive, incremental maintenance working)
    /// - <3ms overhead: 0.5x  (aggressive, low per-round cost)
    /// - <8ms overhead: 0.75x (moderate, typical with incremental state)
    /// - >=8ms or no data: 1.0x (conservative, full rebuild overhead)
    #[inline]
    pub(in crate::solver) fn adaptive_tick_scale(&self) -> f64 {
        let overhead = self.cold.last_inprocessing_overhead_ms;
        if overhead > 0.0 && overhead < 1.0 {
            0.25
        } else if overhead > 0.0 && overhead < 3.0 {
            0.5
        } else if overhead > 0.0 && overhead < 8.0 {
            0.75
        } else {
            1.0
        }
    }

    // ======== Scheduling predicates (#3546, #8148) ========
    //
    // Standard: uses TechniqueControl::should_fire(num_conflicts).
    // Exceptions kept manual: should_vivify (dual schedule), should_bve (fixpoint guard),
    // should_probe/subsume/bce/transred (tick-threshold gating #8148).
    should_inprocess!(should_condition, condition);
    should_inprocess!(should_congruence, congruence);
    should_inprocess!(should_sbva, sbva);
    should_inprocess!(should_decompose, decompose);
    should_inprocess!(should_cce, cce);

    /// Check if we should run Kissat-style clause-weighted reorder.
    ///
    /// Stable-mode gate (#8149): reorder is restricted to stable mode except
    /// for Main-track small-dense formulas. In focused mode, VMTF is already
    /// updated by the search loop, so clause-weighted reordering usually adds
    /// overhead without proportional benefit. Small-dense clique-style
    /// formulas are the exception: the O(vars + irredundant_clauses) scan is
    /// bounded, proof-safe, and lets the existing Kissat focused reorder path
    /// rebuild VMTF from structural clause weights during the hard tail.
    pub(in crate::solver) fn should_reorder(&self) -> bool {
        if !self.stable_mode && !self.small_dense_learned_reduce_policy() {
            return false;
        }
        self.inproc_ctrl.reorder.should_fire(self.num_conflicts)
    }

    /// Evaluate the probe pass skip reason with tick-threshold gating (#8148).
    ///
    /// CaDiCaL uses `probethresh = 0`, so the tick threshold is a no-op for probe.
    /// The threshold gate exists for consistency and future tuning.
    #[allow(clippy::absurd_extreme_comparisons)]
    pub(in crate::solver) fn probe_skip_reason(&self) -> Option<ProbeSkipReason> {
        let control = &self.inproc_ctrl.probe;
        if !control.enabled {
            return Some(ProbeSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(ProbeSkipReason::IntervalNotDue);
        }

        // Tick-threshold gate (#8148): skip if not enough search ticks have
        // accumulated since the last probe call. PROBE_TICK_THRESHOLD=0 means
        // this gate is always satisfied (no-op), matching CaDiCaL probethresh=0.
        if PROBE_TICK_THRESHOLD > 0 && self.cold.last_probe_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_probe_ticks);
            let base_threshold = PROBE_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(ProbeSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run probing (interval + tick-threshold delay).
    pub(in crate::solver) fn should_probe(&self) -> bool {
        self.probe_skip_reason().is_none()
    }

    /// Evaluate the subsumption pass skip reason with tick-threshold gating (#8148).
    pub(in crate::solver) fn subsume_skip_reason(&self) -> Option<SubsumeSkipReason> {
        let control = &self.inproc_ctrl.subsume;
        if !control.enabled {
            return Some(SubsumeSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(SubsumeSkipReason::IntervalNotDue);
        }

        // Tick-threshold gate (#8148): skip if not enough search ticks have
        // accumulated since the last subsume call.
        if self.cold.last_subsume_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_subsume_ticks);
            let base_threshold = SUBSUME_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(SubsumeSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run subsumption (interval + tick-threshold delay).
    pub(in crate::solver) fn should_subsume(&self) -> bool {
        self.subsume_skip_reason().is_none()
    }

    /// Evaluate the BVE pass skip reason with tick-threshold gating (#8148).
    ///
    /// Uses a growing interval (CaDiCaL pattern) so BVE runs less frequently
    /// in later phases. Dual fixed-point guard (CaDiCaL `ineliminating()`,
    /// elim.cpp:60-84): re-fire when new level-0 units have been discovered
    /// OR when irredundant clauses were modified by other inprocessing passes.
    #[allow(clippy::absurd_extreme_comparisons)]
    pub(in crate::solver) fn bve_skip_reason(&self) -> Option<BveSkipReason> {
        if !self.inproc_ctrl.bve.should_fire(self.num_conflicts) {
            if !self.inproc_ctrl.bve.enabled {
                return Some(BveSkipReason::DisabledFlag);
            }
            return Some(BveSkipReason::IntervalNotDue);
        }
        if self.cold.last_bve_fixed == self.fixed_count
            && self.cold.last_bve_marked == self.cold.bve_marked
            && !self.inproc.bve.has_dirty_candidates()
        {
            return Some(BveSkipReason::FixpointGuard);
        }

        // Clause growth guard (#8135): suppress BVE when irredundant clause
        // count has grown beyond BVE_GROWTH_INHIBIT_FACTOR times the count
        // recorded at the end of the last BVE phase. Uses irredundant count
        // (not total active) because learned clauses from CDCL search should
        // not penalize BVE. On clique_n2_k10, BVE resolvents inflate the
        // irredundant clause count from 1409 to 148K+ per round.
        if self.cold.last_bve_clauses > 0 {
            let irred = self.arena.irredundant_count();
            let threshold = self
                .cold
                .last_bve_clauses
                .saturating_mul(BVE_GROWTH_INHIBIT_FACTOR);
            if irred > threshold {
                return Some(BveSkipReason::ClauseGrowthGuard);
            }
        }

        // Tick-threshold gate (#8148): BVE_TICK_THRESHOLD=0 means this gate
        // is always satisfied (no-op), matching CaDiCaL which uses fixpoint
        // guards instead of tick thresholds for elimination.
        if BVE_TICK_THRESHOLD > 0 && self.cold.last_bve_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_bve_ticks);
            let base_threshold = BVE_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(BveSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run BVE (interval + fixpoint guard + tick-threshold delay).
    pub(in crate::solver) fn should_bve(&self) -> bool {
        self.bve_skip_reason().is_none()
    }

    /// Shadow BVE eligibility when the enabled flag is closed by proof mode.
    ///
    /// This mirrors `bve_skip_reason()` except for the enabled-bit check. It is
    /// used only for LRAT telemetry and the default-off proof-safe probe rescue;
    /// it never runs BVE or relaxes LRAT proof clamps.
    #[allow(clippy::absurd_extreme_comparisons)]
    pub(in crate::solver) fn bve_would_be_due_if_enabled(&self) -> bool {
        if self.num_conflicts < self.inproc_ctrl.bve.next_conflict {
            return false;
        }
        if self.cold.last_bve_fixed == self.fixed_count
            && self.cold.last_bve_marked == self.cold.bve_marked
            && !self.inproc.bve.has_dirty_candidates()
        {
            return false;
        }
        if self.cold.last_bve_clauses > 0 {
            let irred = self.arena.irredundant_count();
            let threshold = self
                .cold
                .last_bve_clauses
                .saturating_mul(BVE_GROWTH_INHIBIT_FACTOR);
            if irred > threshold {
                return false;
            }
        }
        if BVE_TICK_THRESHOLD > 0 && self.cold.last_bve_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_bve_ticks);
            let base_threshold = BVE_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return false;
            }
        }
        true
    }

    /// Evaluate the transitive reduction pass skip reason with tick-threshold gating (#8148).
    pub(in crate::solver) fn transred_skip_reason(&self) -> Option<TransredSkipReason> {
        let control = &self.inproc_ctrl.transred;
        if !control.enabled {
            return Some(TransredSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(TransredSkipReason::IntervalNotDue);
        }

        // Tick-threshold gate (#8148): skip if not enough search ticks have
        // accumulated since the last transred call.
        if self.cold.last_transred_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_transred_ticks);
            let base_threshold = TRANSRED_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(TransredSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run transitive reduction (interval + tick-threshold delay).
    pub(in crate::solver) fn should_transred(&self) -> bool {
        self.transred_skip_reason().is_none()
    }

    /// Evaluate the BCE pass skip reason with tick-threshold gating (#8148).
    pub(in crate::solver) fn bce_skip_reason(&self) -> Option<BceSkipReason> {
        let control = &self.inproc_ctrl.bce;
        if !control.enabled {
            return Some(BceSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(BceSkipReason::IntervalNotDue);
        }

        // Tick-threshold gate (#8148): skip if not enough search ticks have
        // accumulated since the last BCE call.
        if self.cold.last_bce_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_bce_ticks);
            let base_threshold = BCE_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(BceSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run BCE (interval + tick-threshold delay).
    pub(in crate::solver) fn should_bce(&self) -> bool {
        self.bce_skip_reason().is_none()
    }

    /// Check if we should run vivification (dual schedule: learned + irredundant,
    /// with CaDiCaL-style tick-threshold gating).
    pub(in crate::solver) fn should_vivify(&self) -> bool {
        self.vivify_skip_reason().is_none()
    }

    #[inline]
    pub(in crate::solver) fn should_vivify_learned(&self) -> bool {
        self.num_conflicts >= self.inproc_ctrl.vivify.next_conflict
    }

    /// Check if we should run irredundant vivification
    #[inline]
    pub(in crate::solver) fn should_vivify_irred(&self) -> bool {
        self.inproc_ctrl.vivify.enabled
            && self.inproc_ctrl.vivify_irred.enabled
            && self.num_conflicts >= self.inproc_ctrl.vivify_irred.next_conflict
    }

    #[inline]
    fn floor_log10(mut value: usize) -> u64 {
        let mut log = 0_u64;
        while value >= 10 {
            value /= 10;
            log += 1;
        }
        log
    }

    /// Evaluate the factor pass skip reason with CaDiCaL-style delay and
    /// mark-watermark gates.
    pub(in crate::solver) fn factor_skip_reason(&self) -> Option<FactorSkipReason> {
        let control = &self.inproc_ctrl.factor;
        if !control.enabled {
            return Some(FactorSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(FactorSkipReason::IntervalNotDue);
        }

        // CaDiCaL factor.cpp: delay gate based on active vars and elimination rounds.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let active_log10 = Self::floor_log10(active_vars);
        let delay_limit = u64::from(self.cold.bve_phases) + FACTOR_DELAY;
        if active_log10 > delay_limit {
            return Some(FactorSkipReason::DelayGuard);
        }

        // CaDiCaL limit.hpp:136-164 + factor.cpp:961-964:
        // later factor rounds require enough accumulated search ticks relative
        // to the current clause database. The first round skips this threshold
        // and uses FACTOR_INIT_TICKS instead.
        // Adaptive scaling (#8099): when inprocessing overhead is low, lower
        // the threshold so factorization fires more frequently.
        if self.cold.factor_rounds > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_factor_ticks);
            let base_threshold = FACTOR_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(FactorSkipReason::ThresholdDelay);
            }
        }

        // CaDiCaL factor.cpp: skip if no new factor marks since last completed pass.
        if self.cold.factor_last_completed_epoch >= self.cold.factor_marked_epoch {
            return Some(FactorSkipReason::NoNewMarks);
        }

        None
    }

    /// Evaluate the HTR pass skip reason with a CaDiCaL-style tick-threshold delay.
    pub(in crate::solver) fn htr_skip_reason(&self) -> Option<HtrSkipReason> {
        let control = &self.inproc_ctrl.htr;
        if !control.enabled {
            return Some(HtrSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(HtrSkipReason::IntervalNotDue);
        }

        // CaDiCaL ternary.cpp:360 + options.hpp:244:
        // later HTR calls are delayed until enough search ticks accumulate
        // relative to the current clause database.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        if let Some(last_ticks) = self.inproc.htr.last_search_ticks() {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(last_ticks);
            let base_threshold = HTR_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(HtrSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run HTR (interval + tick-threshold delay).
    pub(in crate::solver) fn should_htr(&self) -> bool {
        self.htr_skip_reason().is_none()
    }

    /// Check if we should run factorization (interval + delay + mark-watermark).
    pub(in crate::solver) fn should_factor(&self) -> bool {
        self.factor_skip_reason().is_none()
    }

    /// Shadow factor eligibility when the enabled flag is closed by proof mode.
    ///
    /// Mirrors `factor_skip_reason()` except for the enabled-bit check. This
    /// records proof-clamped productivity opportunities without enabling
    /// extension-variable transforms in LRAT.
    pub(in crate::solver) fn factor_would_be_due_if_enabled(&self) -> bool {
        let control = &self.inproc_ctrl.factor;
        if self.num_conflicts < control.next_conflict {
            return false;
        }

        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let active_log10 = Self::floor_log10(active_vars);
        let delay_limit = u64::from(self.cold.bve_phases) + FACTOR_DELAY;
        if active_log10 > delay_limit {
            return false;
        }

        if self.cold.factor_rounds > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_factor_ticks);
            let base_threshold = FACTOR_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return false;
            }
        }

        self.cold.factor_last_completed_epoch < self.cold.factor_marked_epoch
    }

    /// Return whether proof-clamped BVE/factor would be eligible in LRAT mode.
    pub(in crate::solver) fn lrat_proof_clamped_elimination_due(&self) -> (bool, bool) {
        if !self.cold.lrat_enabled || self.proof_manager.is_none() {
            return (false, false);
        }
        let bve_due = !self.inproc_ctrl.bve.enabled && self.bve_would_be_due_if_enabled();
        let factor_due = !self.inproc_ctrl.factor.enabled && self.factor_would_be_due_if_enabled();
        (bve_due, factor_due)
    }

    /// Check if preprocessing should run factorization.
    ///
    /// Preprocessing has no meaningful conflict-based interval yet, so it uses
    /// only the CaDiCaL-style delay guard plus the factor mark-watermark gate.
    pub(in crate::solver) fn should_preprocess_factor(&self) -> bool {
        if !self.inproc_ctrl.factor.enabled {
            return false;
        }

        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let active_log10 = Self::floor_log10(active_vars);
        let delay_limit = u64::from(self.cold.bve_phases) + FACTOR_DELAY;
        if active_log10 > delay_limit {
            return false;
        }

        self.cold.factor_last_completed_epoch < self.cold.factor_marked_epoch
    }

    /// Evaluate the backbone pass skip reason with a CaDiCaL-style tick-threshold
    /// delay (limit.hpp:136-164, options.hpp: `backbonethresh = 5`).
    ///
    /// CaDiCaL NEVER permanently disables backbone — it relies on
    /// `backbonemaxrounds=1000` and tick-based effort limits. AY matches via
    /// `BACKBONE_MAX_ROUNDS` (checked in inprocessing_schedule.rs) plus 1.5x
    /// growing backoff on unproductive rounds (#8450).
    pub(in crate::solver) fn backbone_skip_reason(&self) -> Option<BackboneSkipReason> {
        let control = &self.inproc_ctrl.backbone;
        if !control.enabled {
            return Some(BackboneSkipReason::DisabledFlag);
        }

        if self.num_conflicts < control.next_conflict {
            return Some(BackboneSkipReason::IntervalNotDue);
        }

        // CaDiCaL backbone.cpp + limit.hpp SET_EFFORT_LIMIT:
        // skip if not enough search ticks have accumulated since the last
        // backbone call relative to the current clause database size.
        // The first call (last_backbone_ticks == 0 and num_conflicts > 0)
        // always passes since ticks_delta equals the full search tick count.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        if self.cold.last_backbone_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_backbone_ticks);
            let base_threshold = BACKBONE_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(BackboneSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run backbone (interval + tick-threshold delay).
    pub(in crate::solver) fn should_backbone(&self) -> bool {
        // AY_XP_NO_BACKBONE=1 (default-OFF measured-infra, see
        // xp_probe_vivify.rs) skips both backbone passes for the whole run.
        // Unset => normal scheduling, byte-for-byte unchanged.
        if no_backbone() {
            return false;
        }
        self.backbone_skip_reason().is_none()
    }

    /// Evaluate the sweep pass skip reason with a CaDiCaL-style tick-threshold
    /// delay (limit.hpp:136-164, options.hpp: `sweepthresh = 5`).
    pub(in crate::solver) fn sweep_skip_reason(&self) -> Option<SweepSkipReason> {
        let control = &self.inproc_ctrl.sweep;
        if !control.enabled {
            return Some(SweepSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(SweepSkipReason::IntervalNotDue);
        }

        // CaDiCaL sweep.cpp + limit.hpp SET_EFFORT_LIMIT:
        // skip if not enough search ticks have accumulated since the last
        // sweep call relative to the current clause database size.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        if self.cold.last_sweep_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_sweep_ticks);
            let base_threshold = SWEEP_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(SweepSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run sweep (interval + tick-threshold delay).
    pub(in crate::solver) fn should_sweep(&self) -> bool {
        self.sweep_skip_reason().is_none()
    }

    /// Record an affected trail position for minimal trail rewind (#8095).
    ///
    /// Called when inprocessing derives a new unit (enqueued at `trail.len()`)
    /// or deletes/clears a reason clause for a variable at a given trail position.
    /// Updates `earliest_affected_trail_pos` to the minimum of the current value
    /// and the given position.
    #[inline]
    pub(in crate::solver) fn mark_trail_affected(&mut self, pos: usize) {
        self.earliest_affected_trail_pos = Some(
            self.earliest_affected_trail_pos
                .map_or(pos, |cur| cur.min(pos)),
        );
    }

    /// Apply minimal trail rewind after inprocessing (#8095).
    ///
    /// Uses `earliest_affected_trail_pos` to set `qhead` precisely:
    /// - `None` (no changes): qhead stays at trail.len() (zero re-propagation)
    /// - `Some(0)`: full rewind to position 0
    /// - `Some(pos)` where pos > 0: partial rewind, saving re-propagation of
    ///   trail[0..pos]
    ///
    /// At non-zero decision levels (rare during inprocessing), always rewinds
    /// to the level start for safety.
    ///
    /// Records stats for observability: skipped/partial/full counts and
    /// cumulative trail entries saved.
    #[inline]
    pub(in crate::solver) fn apply_minimal_trail_rewind(&mut self) {
        if self.decision_level == 0 {
            let trail_len = self.trail.len();
            match self.earliest_affected_trail_pos {
                None => {
                    // No inprocessing changes affected any trail position.
                    // Skip re-propagation entirely.
                    self.qhead = trail_len;
                    self.stats.trail_rewind_skipped += 1;
                }
                Some(0) => {
                    // Full rewind to position 0 (BVE, decompose, sweep, etc.).
                    self.qhead = 0;
                    self.stats.trail_rewind_full += 1;
                }
                Some(pos) => {
                    // Partial rewind: re-propagate only from `pos` onward.
                    self.qhead = pos;
                    self.stats.trail_rewind_partial += 1;
                    self.stats.trail_rewind_saved_entries += pos as u64;
                }
            }
        } else {
            self.qhead = self.trail_lim[self.decision_level as usize - 1];
        }
    }

    /// Evaluate the vivify pass skip reason with a CaDiCaL-style tick-threshold
    /// delay (limit.hpp:136-164, options.hpp: `vivifythresh = 20`).
    ///
    /// Vivification uses a dual schedule (learned + irredundant). The tick
    /// threshold is checked against the learned vivify tick watermark, since
    /// that is the primary vivification pass (CaDiCaL's vivify uses a single
    /// learned tick watermark for the SET_EFFORT_LIMIT threshold).
    pub(in crate::solver) fn vivify_skip_reason(&self) -> Option<VivifySkipReason> {
        if !self.inproc_ctrl.vivify.enabled {
            return Some(VivifySkipReason::DisabledFlag);
        }
        if !self.should_vivify_learned() && !self.should_vivify_irred() {
            return Some(VivifySkipReason::IntervalNotDue);
        }

        // Skip inprocessing vivification on small very-dense formulas (#8448).
        //
        // On small dense SAT instances (stable-300: 300 vars, 17540 clauses,
        // density 58.5), vivification shortens irredundant clauses which
        // disrupts the search trajectory. The solver goes from 1.3s (no vivify)
        // to 19.9s (with vivify) — a 15x slowdown. This is because vivification
        // removes literal information from irredundant clauses that the BCP
        // engine relies on for efficient propagation in dense formulas where
        // every literal participates in many watched clauses.
        //
        // Skip during search only (num_conflicts > 0) — preprocessing vivify
        // is still beneficial for initial simplification.
        //
        // Threshold: < 1000 vars AND density > 30 clauses/var. This catches
        // stable-300 (300v, density 58.5) without affecting medium/large
        // formulas where vivification is essential (mp1-klieber: 30K vars).
        // Reference: CaDiCaL's vivification on stable-300 also has minimal
        // impact because CaDiCaL's tick-based effort budget is much tighter,
        // preventing the deep clause modification cascade that hurts AY.
        if self.num_conflicts > 0 && self.num_vars < 1000 {
            let density = if self.num_vars > 0 {
                self.num_original_clauses as f64 / self.num_vars as f64
            } else {
                0.0
            };
            if density > 30.0 {
                return Some(VivifySkipReason::SmallDenseSkip);
            }
        }

        // CaDiCaL vivify.cpp + limit.hpp SET_EFFORT_LIMIT:
        // skip if not enough search ticks have accumulated since the last
        // vivify call relative to the current clause database size.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        //
        // Large-formula sqrt cap (#8655): on BMC formulas with millions of
        // clauses, the linear threshold grows to billions of ticks, which
        // prevents vivification from ever firing. Use sqrt(clause_count)
        // for formulas above the threshold.
        if self.cold.last_vivify_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_vivify_ticks);
            let active_clauses = self.arena.active_clause_count();
            let scaled_count = if active_clauses > VIVIFY_LARGE_FORMULA_SQRT_THRESHOLD {
                (active_clauses as f64).sqrt() as u64
            } else {
                active_clauses as u64
            };
            let base_threshold = VIVIFY_TICK_THRESHOLD.saturating_mul(scaled_count);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(VivifySkipReason::ThresholdDelay);
            }
        }

        None
    }
}
