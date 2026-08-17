// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `LraSolver`.
//!
//! The three large methods (`register_atom`, `check`, `propagate`) are
//! implemented in sibling submodules as inherent methods on `LraSolver`
//! and delegated from the trait impl here. Short delegator and
//! lifecycle methods stay inline.

use super::*;

mod check;
mod propagation;
mod registration;

impl TheorySolver for LraSolver {
    fn register_atom(&mut self, atom: TermId) {
        self.register_atom_impl(atom)
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.assert_literal_impl(literal, value)
    }

    fn check(&mut self) -> TheoryResult {
        self.drain_lra_basis_region_requests_at_safe_boundary();
        let _ = self.pivot_row_cache.install_ready_results();
        let result = self.check_impl();
        // Term-level arithmetic ITEs parsed as opaque variables need their
        // SAT-level branch link lemmas before a Sat can be trusted.
        self.request_ite_link_lemmas_on_sat(result)
    }

    /// Lightweight BCP-time check: runs simplex but defers disequality/model-only
    /// work to the final full check.
    fn check_during_propagate(&mut self) -> TheoryResult {
        self.drain_lra_basis_region_requests_at_safe_boundary();
        let _ = self.pivot_row_cache.install_ready_results();
        self.check_during_propagate_impl()
    }

    /// The BCP-time check skips disequality/model-equality work, so the eager
    /// solver must run one final full check before accepting SAT.
    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        self.drain_lra_basis_region_requests_at_safe_boundary();
        let _ = self.pivot_row_cache.install_ready_results();
        self.propagate_impl()
    }

    fn has_pending_propagations(&self) -> bool {
        !self.pending_propagations.is_empty()
    }

    fn has_pending_analysis(&self) -> bool {
        // #8422: `propagate_direct_touched_rows_pending` is now the single
        // freshness signal for touched-row analysis. It is set by direct bound
        // assertions and by capped implied-bound fixpoints that leave real
        // cascade rows queued; it is cleared when the fixpoint converges. Do
        // not also require a new direct-bound or simplex flag here, because
        // capped cascades clear those flags after deriving the first hop.
        self.propagate_direct_touched_rows_pending && !self.touched_rows.is_empty()
    }

    fn drain_pending_propagations(&mut self) -> Vec<TheoryPropagation> {
        self.drain_pending_propagations_impl()
    }

    /// Forward buffered single-var disequality splits so the DPLL(T) split
    /// loop can encode all of them in one round (#8762). See
    /// `LraSolver::drain_pending_diseq_splits` at `lifecycle.rs` for the
    /// inherent implementation.
    fn drain_pending_diseq_splits(&mut self) -> Vec<DisequalitySplitRequest> {
        Self::drain_pending_diseq_splits(self)
    }

    fn push(&mut self) {
        self.push_inner();
    }

    fn pop(&mut self) {
        self.pop_inner();
    }

    fn reset(&mut self) {
        self.reset_inner();
    }

    fn soft_reset(&mut self) {
        self.soft_reset_inner();
    }

    fn soft_reset_warm(&mut self) {
        // Delegate to the inherent method which preserves simplex basis
        // and variable values for warm-start (#2138).
        Self::soft_reset_warm(self);
    }

    fn set_warm_reuse_hint(&mut self, reused: bool) {
        self.warm_reuse_hint = reused;
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }

    fn registered_atom_count(&self) -> usize {
        self.registered_atoms.len()
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        true
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        self.propagate_equalities_inner()
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.assert_shared_equality_inner(lhs, rhs, reason);
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.assert_shared_disequality_inner(lhs, rhs, reason);
    }

    fn explain_propagation(&mut self, lit: TermId, reason_data: u64) -> Option<Vec<TheoryLit>> {
        let reason = self.explain_propagation_inner(lit, reason_data)?;
        // Self-reference soundness guard (tautological reason): a reason that
        // mentions the propagated atom's own term yields a circular,
        // tautological reason clause `(lit \/ ... \/ ¬lit \/ ...)` that does not
        // justify the propagation. Reject it (return None) so the SAT layer
        // treats the variable as a decision (sound, only weakens the learned
        // clause) instead of storing a duplicate-variable reason clause that
        // corrupts the two-watched-literal invariant.
        if reason.iter().any(|r| r.term == lit) {
            return None;
        }
        Some(reason)
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        // Clear the propagated_atoms cache entry so the same atom can be
        // re-derived with better reasons on the next propagation round.
        // #8467: Literal polarity is encoded in bit 33 of reason_data.
        let polarity = (reason_data >> 33) & 1 != 0;
        self.propagated_atoms.remove(&(lit, polarity));
        self.stats.lazy_rejected_count += 1;
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let mut stats = vec![
            ("lra_checks", self.stats.check_count),
            ("lra_conflicts", self.stats.conflict_count),
            ("lra_propagations", self.stats.propagation_count),
            ("lra_bcp_simplex_skips", self.stats.bcp_simplex_skips),
            (
                "lra_bcp_post_simplex_fast_skips",
                self.stats.bcp_post_simplex_fast_skips,
            ),
            ("lra_assert_dirty_skips", self.stats.assert_dirty_skips),
            (
                "lra_propagate_implied_fresh_skips",
                self.stats.propagate_implied_bounds_fresh_skips,
            ),
            (
                "lra_full_check_conflicts",
                self.stats.full_check_conflict_count,
            ),
            ("lra_reasons_eager", self.stats.eager_reason_count),
            ("lra_reasons_deferred", self.stats.deferred_reason_count),
            (
                "lra_reasons_deferred_direct",
                self.stats.deferred_direct_count,
            ),
            (
                "lra_reasons_deferred_interval",
                self.stats.deferred_interval_count,
            ),
            (
                "lra_reasons_deferred_implied",
                self.stats.deferred_implied_count,
            ),
            ("lra_reasons_lazy_emitted", self.stats.lazy_emitted_count),
            ("lra_reasons_lazy_rejected", self.stats.lazy_rejected_count),
            ("lra_emitted_direct", self.stats.emitted_direct_count),
            ("lra_emitted_implied", self.stats.emitted_implied_count),
            (
                "lra_emitted_implied_row",
                self.stats.emitted_implied_row_count,
            ),
            (
                "lra_stale_reason_filtered",
                self.stats.stale_reason_filtered_count,
            ),
            (
                "lra_stale_conflict_rejected",
                self.stats.stale_conflict_rejected_count,
            ),
            ("lra_simplex_sat", self.stats.simplex_sat_count),
            ("lra_snapshot_pivot_skips", self.stats.snapshot_pivot_skips),
            ("lra_total_pivots", self.stats.total_pivots),
            ("lra_full_check_pivots", self.stats.full_check_pivots),
            (
                "lra_simplex_budget_exhaustions",
                self.stats.simplex_budget_exhaustions,
            ),
            (
                "lra_global_budget_exhaustions",
                self.stats.global_budget_exhaustions,
            ),
            (
                "lra_check_pivot_budget_exhaustions",
                self.stats.check_pivot_budget_exhaustions,
            ),
            (
                "lra_compound_use_vars",
                self.compound_use_index.len() as u64,
            ),
            (
                "lra_compound_wake_dirty_hits",
                self.last_compound_wake_dirty_hits as u64,
            ),
            (
                "lra_compound_wake_candidates",
                self.last_compound_wake_candidates as u64,
            ),
            (
                "lra_compound_queued",
                self.last_compound_propagations_queued as u64,
            ),
            ("lra_precision_i64_rows", self.stats.precision_i64_rows),
            ("lra_precision_i128_rows", self.stats.precision_i128_rows),
            ("lra_precision_big_rows", self.stats.precision_big_rows),
            ("lra_jit_propagations", self.stats.jit_propagation_count),
            (
                "lra_jit_compiled_vars",
                u64::from(self.theory_prop_jit.compiled_vars()),
            ),
            (
                "lra_jit_native_vars",
                u64::from(self.theory_prop_jit.native_compiled_vars()),
            ),
            (
                "lra_jit_total_atoms",
                u64::from(self.theory_prop_jit.total_atoms()),
            ),
            (
                "lra_jit_small_atoms",
                u64::from(self.theory_prop_jit.small_atoms()),
            ),
            ("lra_jit_compilations", self.pivot_row_cache.compilations()),
            ("lra_jit_applies", self.pivot_row_cache.jit_applies()),
            (
                "lra_jit_batch_compilations",
                self.pivot_row_cache.batch_compilations(),
            ),
            (
                "lra_jit_batch_applies",
                self.pivot_row_cache.batch_jit_applies(),
            ),
            (
                "lra_jit_batch_rows_updated",
                self.pivot_row_cache.batch_rows_updated(),
            ),
            (
                "lra_jit_i64_fast_path_rows",
                self.pivot_row_cache.i64_fast_path_rows(),
            ),
            (
                "lra_jit_i64_overflow_fallbacks",
                self.pivot_row_cache.i64_overflow_fallbacks(),
            ),
            (
                "lra_external_codegen_backend_substitute_compile_attempts",
                self.pivot_row_cache.substitute_compile_attempts(),
            ),
            (
                "lra_external_codegen_backend_substitute_compilations",
                self.pivot_row_cache
                    .substitute_external_codegen_compilations(),
            ),
            (
                "lra_external_codegen_backend_substitute_compile_failures",
                self.pivot_row_cache.substitute_compile_failures(),
            ),
            (
                "lra_external_codegen_backend_substitute_backoff_skips",
                self.pivot_row_cache.substitute_compile_backoff_skips(),
            ),
            (
                "lra_external_codegen_backend_substitute_disabled_skips",
                self.pivot_row_cache.substitute_compile_disabled_skips(),
            ),
            (
                "lra_external_codegen_backend_substitute_applies",
                self.pivot_row_cache.substitute_external_codegen_applies(),
            ),
            (
                "lra_external_codegen_backend_substitute_wrapper_applies",
                self.pivot_row_cache.substitute_compiled_applies(),
            ),
            (
                "lra_external_codegen_backend_substitute_native_applies",
                self.pivot_row_cache.substitute_external_codegen_applies(),
            ),
            (
                "lra_external_codegen_backend_substitute_native_empty_target_applies",
                self.pivot_row_cache
                    .substitute_external_codegen_empty_target_applies(),
            ),
            (
                "lra_external_codegen_backend_substitute_native_non_empty_target_applies",
                self.pivot_row_cache
                    .substitute_external_codegen_non_empty_target_applies(),
            ),
            (
                "lra_external_codegen_backend_substitute_runtime_applies",
                self.pivot_row_cache.substitute_compiled_runtime_applies(),
            ),
            (
                "lra_external_codegen_backend_substitute_fallback_applies",
                self.pivot_row_cache.substitute_fallback_applies(),
            ),
            (
                "lra_external_codegen_backend_substitute_overflow_fallbacks",
                self.pivot_row_cache.substitute_overflow_fallbacks(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_submissions",
                self.pivot_row_cache.substitute_queue_submissions(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_installs",
                self.pivot_row_cache.substitute_queue_installs(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_budget_rejects",
                self.pivot_row_cache.substitute_queue_budget_rejects(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_dropped_stale",
                self.pivot_row_cache.substitute_queue_dropped_stale(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_compile_us_total",
                self.pivot_row_cache.substitute_queue_compile_us_total(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_compile_us_max",
                self.pivot_row_cache.substitute_queue_compile_us_max(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_submit_to_install_us_total",
                self.pivot_row_cache
                    .substitute_queue_submit_to_install_us_total(),
            ),
            (
                "lra_external_codegen_backend_substitute_queue_submit_to_install_us_max",
                self.pivot_row_cache
                    .substitute_queue_submit_to_install_us_max(),
            ),
            (
                "lra_external_codegen_backend_substitute_evidence_wait_attempts",
                self.stats
                    .lra_external_codegen_backend_substitute_evidence_wait_attempts,
            ),
            (
                "lra_external_codegen_backend_substitute_evidence_wait_hits",
                self.stats
                    .lra_external_codegen_backend_substitute_evidence_wait_hits,
            ),
            (
                "lra_external_codegen_backend_substitute_evidence_wait_timeouts",
                self.stats
                    .lra_external_codegen_backend_substitute_evidence_wait_timeouts,
            ),
            (
                "lra_external_codegen_backend_substitute_evidence_wait_polls",
                self.stats
                    .lra_external_codegen_backend_substitute_evidence_wait_polls,
            ),
            (
                "lra_external_codegen_backend_substitute_evidence_wait_us_total",
                self.stats
                    .lra_external_codegen_backend_substitute_evidence_wait_us_total,
            ),
            (
                "lra_basis_region_boundary_checks",
                self.stats.lra_basis_region_boundary_checks,
            ),
            (
                "lra_basis_region_requests_queued",
                self.stats.lra_basis_region_requests_queued,
            ),
            (
                "lra_basis_region_disabled_skips",
                self.stats.lra_basis_region_disabled_skips,
            ),
            (
                "lra_basis_region_ineligible_skips",
                self.stats.lra_basis_region_ineligible_skips,
            ),
            (
                "lra_basis_region_queue_full_skips",
                self.stats.lra_basis_region_queue_full_skips,
            ),
            (
                "lra_basis_region_queue_submissions",
                self.pivot_row_cache.lra_basis_region_queue_submissions(),
            ),
            (
                "lra_basis_region_queue_installs",
                self.pivot_row_cache.lra_basis_region_queue_installs(),
            ),
            (
                "lra_basis_region_queue_budget_rejects",
                self.pivot_row_cache.lra_basis_region_queue_budget_rejects(),
            ),
            (
                "lra_basis_region_queue_dropped_stale",
                self.pivot_row_cache.lra_basis_region_queue_dropped_stale(),
            ),
            (
                "lra_basis_region_unsupported_fallbacks",
                self.pivot_row_cache
                    .lra_basis_region_unsupported_fallbacks(),
            ),
            (
                "lra_basis_region_compile_failures",
                self.pivot_row_cache.lra_basis_region_compile_failures(),
            ),
            (
                "lra_basis_region_native_applies",
                self.pivot_row_cache.lra_basis_region_native_applies(),
            ),
            (
                "lra_basis_region_batch_native_applies",
                self.pivot_row_cache.lra_basis_region_batch_native_applies(),
            ),
            (
                "lra_basis_region_queue_compile_us_total",
                self.pivot_row_cache
                    .lra_basis_region_queue_compile_us_total(),
            ),
            (
                "lra_basis_region_queue_compile_us_max",
                self.pivot_row_cache.lra_basis_region_queue_compile_us_max(),
            ),
            (
                "lra_basis_region_evidence_wait_attempts",
                self.stats.lra_basis_region_evidence_wait_attempts,
            ),
            (
                "lra_basis_region_evidence_wait_hits",
                self.stats.lra_basis_region_evidence_wait_hits,
            ),
            (
                "lra_basis_region_evidence_wait_timeouts",
                self.stats.lra_basis_region_evidence_wait_timeouts,
            ),
            (
                "lra_basis_region_evidence_wait_polls",
                self.stats.lra_basis_region_evidence_wait_polls,
            ),
            (
                "lra_basis_region_evidence_wait_us_total",
                self.stats.lra_basis_region_evidence_wait_us_total,
            ),
            ("lra_jit_cache_entries", self.pivot_row_cache.len() as u64),
            (
                "lra_phase_hint_cache_size",
                self.phase_hint_cache.len() as u64,
            ),
            (
                "lra_max_inner_cascade_depth",
                u64::from(self.stats.max_inner_cascade_depth),
            ),
            (
                "lra_total_inner_cascade_rounds",
                self.stats.total_inner_cascade_rounds,
            ),
            ("lra_f64_rows_skipped", self.stats.f64_rows_skipped),
            ("lra_f64_vars_skipped", self.stats.f64_vars_skipped),
            (
                "lra_max_outer_fixpoint_iters",
                u64::from(self.stats.max_outer_fixpoint_iters),
            ),
            (
                "lra_total_outer_fixpoint_iters",
                self.stats.total_outer_fixpoint_iters,
            ),
            (
                "lra_cascade_depth_throttles",
                self.stats.cascade_depth_throttles,
            ),
        ];

        let lra_sparse_substitute_enabled = false && !self.pivot_row_cache.is_substitute_disabled();
        let lra_basis_region_enabled = false
            && !ay_jit::no_external_codegen_backend_cached()
            && !self.pivot_row_cache.is_substitute_disabled();
        let solver_program_stats = ay_jit::SolverProgramStableStats::lra(
            ay_jit::SolverProgramProfileToggles::lra(
                lra_sparse_substitute_enabled,
                lra_basis_region_enabled,
            ),
            ay_jit::SolverProgramLraSparseSubstituteStats {
                compile_attempts: self.pivot_row_cache.substitute_compile_attempts(),
                compile_successes: self
                    .pivot_row_cache
                    .substitute_external_codegen_compilations(),
                compile_failures: self.pivot_row_cache.substitute_compile_failures(),
                compile_backoff_skips: self.pivot_row_cache.substitute_compile_backoff_skips(),
                disabled_skips: self.pivot_row_cache.substitute_compile_disabled_skips(),
                applies: self.pivot_row_cache.substitute_external_codegen_applies(),
                wrapper_applies: self.pivot_row_cache.substitute_compiled_applies(),
                native_applies: self.pivot_row_cache.substitute_external_codegen_applies(),
                native_empty_target_applies: self
                    .pivot_row_cache
                    .substitute_external_codegen_empty_target_applies(),
                native_non_empty_target_applies: self
                    .pivot_row_cache
                    .substitute_external_codegen_non_empty_target_applies(),
                runtime_applies: self.pivot_row_cache.substitute_compiled_runtime_applies(),
                fallback_applies: self.pivot_row_cache.substitute_fallback_applies(),
                overflow_fallbacks: self.pivot_row_cache.substitute_overflow_fallbacks(),
                queue_submissions: self.pivot_row_cache.substitute_queue_submissions(),
                queue_installs: self.pivot_row_cache.substitute_queue_installs(),
                queue_budget_rejects: self.pivot_row_cache.substitute_queue_budget_rejects(),
                stale_drops: self.pivot_row_cache.substitute_queue_dropped_stale(),
                queue_compile_us_total: self.pivot_row_cache.substitute_queue_compile_us_total(),
                queue_compile_us_max: self.pivot_row_cache.substitute_queue_compile_us_max(),
                queue_submit_to_install_us_total: self
                    .pivot_row_cache
                    .substitute_queue_submit_to_install_us_total(),
                queue_submit_to_install_us_max: self
                    .pivot_row_cache
                    .substitute_queue_submit_to_install_us_max(),
            },
            ay_jit::SolverProgramLraBasisRegionStats {
                boundary_checks: self.stats.lra_basis_region_boundary_checks,
                requests_queued: self.stats.lra_basis_region_requests_queued,
                disabled_skips: self.stats.lra_basis_region_disabled_skips,
                ineligible_skips: self.stats.lra_basis_region_ineligible_skips,
                queue_full_skips: self.stats.lra_basis_region_queue_full_skips,
                queue_submissions: self.pivot_row_cache.lra_basis_region_queue_submissions(),
                queue_installs: self.pivot_row_cache.lra_basis_region_queue_installs(),
                queue_budget_rejects: self.pivot_row_cache.lra_basis_region_queue_budget_rejects(),
                stale_drops: self.pivot_row_cache.lra_basis_region_queue_dropped_stale(),
                unsupported_fallbacks: self
                    .pivot_row_cache
                    .lra_basis_region_unsupported_fallbacks(),
                compile_failures: self.pivot_row_cache.lra_basis_region_compile_failures(),
                native_applies: self.pivot_row_cache.lra_basis_region_native_applies(),
                batch_native_applies: self.pivot_row_cache.lra_basis_region_batch_native_applies(),
                queue_compile_us_total: self
                    .pivot_row_cache
                    .lra_basis_region_queue_compile_us_total(),
                queue_compile_us_max: self.pivot_row_cache.lra_basis_region_queue_compile_us_max(),
                evidence_wait_attempts: self.stats.lra_basis_region_evidence_wait_attempts,
                evidence_wait_hits: self.stats.lra_basis_region_evidence_wait_hits,
                evidence_wait_timeouts: self.stats.lra_basis_region_evidence_wait_timeouts,
                evidence_wait_polls: self.stats.lra_basis_region_evidence_wait_polls,
                evidence_wait_us_total: self.stats.lra_basis_region_evidence_wait_us_total,
            },
        );
        stats.extend(solver_program_stats.rows());
        stats
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        // #8008: Fast path — use pre-computed phase hint cache when available.
        // The cache is rebuilt in save_feasible_snapshot() after each feasible
        // simplex result. This makes suggest_phase() O(1) instead of
        // O(coefficients) Rational arithmetic per atom. Z3's get_phase()
        // calls lp().compare_values() which is a single comparison; the cache
        // gives AY the same O(1) semantics.
        //
        // The cache covers all registered atoms evaluated against the last
        // feasible model. When the cache is populated, it is authoritative —
        // no need to fall through to expensive evaluation.
        if let Some(&phase) = self.phase_hint_cache.get(&atom) {
            return Some(phase);
        }

        // Cache miss: atom was registered after the last feasible snapshot,
        // or no feasible snapshot exists yet. Fall back to evaluation.
        let info = self.atom_cache.get(&atom)?.as_ref()?;

        // #8064: Use the feasible value snapshot when the current simplex state
        // is infeasible. On benchmarks where simplex rarely/never returns Sat
        // during BCP (e.g., sc-21, vpm2-30), the current variable values are
        // left in whatever state the last infeasible pivot produced — evaluating
        // atoms against these values gives meaningless phase hints. The snapshot
        // captures variable values from the last known feasible solution.
        let use_snapshot = !self.last_simplex_feasible && !self.feasible_value_snapshot.is_empty();

        // Evaluate the expression in the simplex model (current or snapshot).
        let mut val = info.expr.constant.clone();
        for &(var, ref coeff) in &info.expr.coeffs {
            let vi = var as usize;
            if use_snapshot {
                let var_val = self.feasible_value_snapshot.get(vi)?;
                val += coeff * var_val;
            } else {
                let var_info = self.vars.get(vi)?;
                val += coeff * &var_info.value.x_rational();
            }
        }

        // Equality atoms: (= x y) is true iff expr evaluates to 0 in the model.
        if info.is_eq {
            return Some(val.is_zero());
        }

        // Distinct atoms: (distinct x y) is true iff expr != 0 in the model.
        if info.is_distinct {
            return Some(!val.is_zero());
        }

        // Inequality atoms with boundary-case fix (#8008): strict atoms at
        // val == 0 now return Some(false) instead of None. Z3's
        // compare_values() returns false for strict inequalities at the
        // boundary (0 < 0 is false, 0 > 0 is false). Returning None caused
        // the SAT solver to use its default phase (positive), which may be
        // theory-inconsistent.
        if info.is_le {
            if info.strict {
                // atom asserts expr < 0
                Some(val.is_negative())
            } else {
                // atom asserts expr <= 0
                Some(!val.is_positive())
            }
        } else {
            // atom asserts expr >= 0 (or expr > 0 if strict)
            if info.strict {
                Some(val.is_positive())
            } else {
                Some(!val.is_negative())
            }
        }
    }

    fn phase_hint_epoch(&self) -> Option<u64> {
        // `suggest_phase` is a pure function of `phase_hint_cache` (fast path)
        // and the feasible-value snapshot (fall back). Both are refreshed
        // together in `save_feasible_snapshot`, which bumps `phase_hint_epoch`
        // exactly when it rebuilds the cache (and the snapshot), and skips the
        // bump when no variable value changed. Cache clears on pop/reset also
        // bump it. So a stable epoch guarantees identical suggestions, letting
        // the SAT seeder skip an O(atoms) re-seed per BCP quiescence — the
        // dominant in-solver cost on QF_LRA induction benchmarks.
        Some(self.phase_hint_epoch)
    }

    fn supports_theory_aware_branching(&self) -> bool {
        // Disabled: A/B testing on 100 SMT-COMP QF_LRA benchmarks (10s timeout)
        // showed 48/100 (disabled) vs 46/100 (enabled). Theory-aware branching
        // overrides VSIDS variable selection, which is too aggressive — Z3 only
        // uses LP-consistent *phase* selection (PS_THEORY/get_phase), not variable
        // ordering. suggest_phase() already provides LP-consistent polarity when
        // VSIDS picks a theory variable (solve.rs:704), matching Z3's approach.
        // Re-enabled with fractional gating (#8008). Regressions: sc-6.induction3.cvc.smt2 (sat→timeout),
        //              windowreal-no_t_deadlock-16.smt2 (unsat→timeout).
        // With 1-in-8 fractional gating, VSIDS remains dominant.
        true
    }

    fn sort_atom_index(&mut self) {
        for atoms in self.atom_index.values_mut() {
            atoms.sort_by(|a, b| a.bound_value.cmp(&b.bound_value));
        }
        // #8008: Build the negation_partners map for cross-negation bound
        // propagation. This scans expr_to_slack to find pairs of slack variables
        // whose expressions are negations of each other (S1 + S2 = K).
        // Must run after all atoms are registered and slacks are created.
        self.build_negation_partners();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        // #8008: Re-enable bound axiom generation for LRA. Delegates to the
        // inner method which uses Z3-style nearest-neighbor axiom generation.
        // These encode transitivity implications between bound atoms as SAT
        // binary clauses (e.g., x >= 5 => x >= 3).
        //
        // Previously disabled (#8254) due to InvalidSatModel. Re-enabled
        // because the eager-persistent pipeline arm was missing the axiom
        // injection call entirely.
        //
        // #8319: AY_NO_BOUND_AXIOMS disables this at runtime.
        // Use centralized TheoryDisableFlags (cached OnceLock) instead of
        // per-call std::env::var syscall (#8092 audit).
        if ay_core::debug_channel::theory_disable_flags().no_bound_axioms {
            return Vec::new();
        }
        self.generate_bound_axiom_terms_inner()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        // #8008: Re-enable incremental bound axiom generation.
        // Use centralized TheoryDisableFlags (cached OnceLock) instead of
        // per-call std::env::var syscall (#8092 audit).
        if ay_core::debug_channel::theory_disable_flags().no_bound_axioms {
            return Vec::new();
        }
        self.generate_incremental_bound_axioms_inner(atom)
    }

    /// Reconstruct an `LraSolver` from a structural snapshot previously created
    /// by `export_structural_snapshot` (#6590).
    fn restore_from_structural_snapshot(
        terms: &TermStore,
        snapshot: Box<dyn std::any::Any>,
    ) -> Result<Self, Box<dyn std::any::Any>> {
        Self::restore_from_structural_snapshot_inner(terms, snapshot)
    }

    /// Export full structural state for fast reconstruction across split-loop
    /// iterations (#6590).
    ///
    /// Captures all fields that `soft_reset()` preserves: tableau rows, variable
    /// mappings, atom cache, atom/compound indices, slack state, and column index.
    /// The snapshot is consumed by `import_structural_snapshot` on a fresh
    /// `LraSolver` to skip all `register_atom` parsing and indexing work.
    fn export_structural_snapshot(&self) -> Option<Box<dyn std::any::Any>> {
        self.export_structural_snapshot_inner()
    }

    /// Import structural state from a previous LraSolver instance (#6590).
    ///
    /// Restores all structural fields and then performs soft-reset-equivalent
    /// initialization (clear bounds, populate touched_rows, etc.) so the solver
    /// is ready for `register_atom` (which will be a no-op for known atoms)
    /// followed by `assert_literal` / `check`.
    fn import_structural_snapshot(&mut self, snapshot: Box<dyn std::any::Any>) {
        self.import_structural_snapshot_inner(snapshot);
    }

    /// LP-model-guided decision atom suggestion for LRA.
    ///
    /// For structured LP problems (ranking function synthesis, Motzkin/Farkas
    /// encodings), VSIDS alone produces large learned clauses and high
    /// decision levels because it cannot exploit the LP structure. This method
    /// uses the current simplex model to identify atoms that will maximally
    /// constrain the search:
    ///
    /// 1. **Equality atoms at LP zero**: When the LP model evaluates an
    ///    equality atom's expression to exactly 0, deciding it `true` is
    ///    consistent with the model and adds a strong constraint.
    ///
    /// 2. **Boundary inequality atoms**: Atoms where the LP model is exactly
    ///    at the boundary (expr = 0 for `<= 0` or `>= 0`) are critical
    ///    decision points. Deciding them cuts the search space maximally.
    ///
    /// Reference: Z3 `arith_solver::get_phase()` + `theory_case_split_queue`.
    fn suggest_decision_atom(&self) -> Option<(TermId, bool)> {
        // Only suggest when we have a feasible LP model to query.
        if !self.last_simplex_feasible && self.feasible_value_snapshot.is_empty() {
            return None;
        }
        // Only activate for problems with enough theory atoms to benefit from
        // LP-guided decisions. Small problems are handled well by VSIDS alone.
        if self.registered_atoms.len() < 100 {
            return None;
        }

        // STAGE B: the incremental candidate index (`decision_index`) collapses
        // the two full O(registered_atoms) scans below into an O(degree)/O(1)
        // amortized lookup. It is soundness-neutral — a heuristic that only
        // *suggests* a decision atom (the SAT core owns the sat/unsat verdict)
        // — and returns from the same candidate set the slow path would (same
        // phase-hint / not-asserted / category filters), only in a different
        // order. Gated behind --no-lra-fast-decision (default on) so the exact
        // legacy scan can be restored for differential comparison.
        if fast_decision_enabled() {
            self.suggest_decision_atom_fast()
        } else {
            self.suggest_decision_atom_slow()
        }
    }
}

/// STAGE B decision-index maintenance and fast/slow suggestion paths.
impl LraSolver {
    /// Fast path for `suggest_decision_atom`: iterate the maintained
    /// unasserted-candidate index instead of every registered atom.
    ///
    /// Same result semantics as `suggest_decision_atom_slow`: priority 1 is an
    /// unasserted equality atom with an LP-consistent phase hint; priority 2 is
    /// an unasserted non-strict inequality atom with a phase hint. Only the
    /// iteration order (hence *which* qualifying atom is returned) may differ,
    /// which is soundness-neutral because this merely orders decisions.
    ///
    /// The `!asserted.contains_key` guard is a defensive net: the index invariant
    /// already excludes asserted atoms, so a stale entry (impossible if every
    /// maintenance site fired) is skipped rather than returned — never an
    /// unsound suggestion, at worst a missed heuristic hit.
    pub(crate) fn suggest_decision_atom_fast(&self) -> Option<(TermId, bool)> {
        for &atom in self.decision_index.eq.items() {
            if let Some(&phase) = self.phase_hint_cache.get(&atom) {
                if self.asserted.contains_key(&atom) {
                    continue;
                }
                return Some((atom, phase));
            }
        }
        for &atom in self.decision_index.ineq.items() {
            if let Some(&phase) = self.phase_hint_cache.get(&atom) {
                if self.asserted.contains_key(&atom) {
                    continue;
                }
                return Some((atom, phase));
            }
        }
        None
    }

    /// Legacy two-scan path, preserved verbatim for `--no-lra-fast-decision`
    /// differential comparison. Two full O(registered_atoms) passes.
    pub(crate) fn suggest_decision_atom_slow(&self) -> Option<(TermId, bool)> {
        // Priority 1: Equality atoms with LP-model-consistent phase. Equality
        // atoms are the most constraining: they fix a linear combination to a
        // point. Deciding them first prunes the search space maximally.
        for &atom in &self.registered_atoms {
            if self.asserted.contains_key(&atom) {
                continue; // Already decided
            }
            if let Some(Some(info)) = self.atom_cache.get(&atom) {
                if !info.is_eq {
                    continue;
                }
                if let Some(&phase) = self.phase_hint_cache.get(&atom) {
                    return Some((atom, phase));
                }
            }
        }

        // Priority 2: Non-strict inequality atoms with LP-model-consistent phase.
        // These atoms bound linear combinations. Deciding them in the
        // LP-consistent direction avoids exploring LP-infeasible branches.
        for &atom in &self.registered_atoms {
            if self.asserted.contains_key(&atom) {
                continue;
            }
            if let Some(Some(info)) = self.atom_cache.get(&atom) {
                if info.is_eq || info.is_distinct {
                    continue;
                }
                if let Some(&phase) = self.phase_hint_cache.get(&atom) {
                    return Some((atom, phase));
                }
            }
        }

        None
    }

    /// Record a freshly-registered atom in the decision-candidate index.
    /// Distinct atoms are never decision candidates; already-asserted terms are
    /// excluded to preserve the "unasserted" invariant. Called at every
    /// `registered_atoms.insert` site.
    #[inline]
    pub(crate) fn decision_index_note_registered(
        &mut self,
        term: TermId,
        is_eq: bool,
        is_distinct: bool,
    ) {
        if is_distinct || self.asserted.contains_key(&term) {
            return;
        }
        if is_eq {
            self.decision_index.eq.insert(term);
        } else {
            self.decision_index.ineq.insert(term);
        }
    }

    /// Rebuild the decision-candidate index from scratch: every registered,
    /// non-distinct, currently-unasserted atom, partitioned by category. Used at
    /// bulk boundaries (reset / soft_reset / snapshot import) where `asserted`
    /// or `registered_atoms` changed wholesale. O(registered_atoms), but only at
    /// these rare boundaries — not per decision.
    pub(crate) fn rebuild_decision_index(&mut self) {
        self.decision_index.eq.clear();
        self.decision_index.ineq.clear();
        // Collect first to avoid holding a borrow on `self` while inserting.
        let atoms: Vec<TermId> = self.registered_atoms.iter().copied().collect();
        for atom in atoms {
            if self.asserted.contains_key(&atom) {
                continue;
            }
            let is_eq = match self.atom_cache.get(&atom) {
                Some(Some(info)) if !info.is_distinct => info.is_eq,
                _ => continue,
            };
            if is_eq {
                self.decision_index.eq.insert(atom);
            } else {
                self.decision_index.ineq.insert(atom);
            }
        }
    }
}

/// Whether the STAGE B fast decision-suggestion path is enabled (default on;
/// `--no-lra-fast-decision` forces the legacy scan). The index is maintained
/// unconditionally so the fast and slow paths can be compared directly in
/// tests regardless of this switch; only which path `suggest_decision_atom`
/// takes is gated.
pub(crate) fn fast_decision_enabled() -> bool {
    !ay_core::theory_disable_flags().no_lra_fast_decision
}

/// Helper methods for `suggest_decision_atom` LP-model evaluation.
impl LraSolver {
    /// Reconstruct the reason for a lazy theory propagation (#8467).
    ///
    /// Read-only (`&self`): no statistics are bumped here so the same logic can
    /// be reused by the pre-trail self-reference probe in `propagate_impl`
    /// without inflating counters or double-mutating state. The public
    /// `explain_propagation` wrapper owns the self-reference soundness guard.
    fn explain_propagation_inner(&self, _lit: TermId, reason_data: u64) -> Option<Vec<TheoryLit>> {
        // #8467: Lazy justification for DirectBound and ImpliedBound propagations.
        //
        // DirectBound reasons read vars[var].upper/lower.reason_pairs() which
        // are set by assert_literal() and only cleared by pop(). Between
        // propagation and conflict analysis within the same decision level,
        // these are stable.
        //
        // ImpliedBound reasons reconstruct from BoundExplanation chain stored
        // in implied_bounds[var]. The chain references contributing_vars whose
        // direct bounds (set by assert_literal, cleared by pop) are stable
        // within a decision level. Fallback strategies (single-row, interval)
        // use current tableau state which is also stable within a level.
        //
        // Interval reasons are eagerly materialized in propagate_impl() because
        // they depend on compute_expr_interval which can change with basis pivots.
        //
        // Encoding: bits63=0, bits62=0, bit33=polarity, bit32=need_upper,
        // bits0-31=var (DirectBound).
        // Encoding: bits63=0, bits62=1, bit33=polarity, bit32=need_upper,
        // bits0-31=var (ImpliedBound).
        let is_interval = (reason_data >> 63) & 1 != 0;
        let is_implied = !is_interval && ((reason_data >> 62) & 1 != 0);

        if is_interval {
            // Interval reasons are eagerly materialized in propagate_impl().
            // Return None to safely reject; the SAT solver converts to a
            // decision (sound but weaker learned clause).
            return None;
        }

        let var = (reason_data & 0xFFFF_FFFF) as u32;
        let need_upper = (reason_data >> 32) & 1 != 0;
        let vi = var as usize;

        if is_implied {
            // #8467: ImpliedBound lazy justification. Reconstruct the reason
            // from BoundExplanation chain, with single-row and interval fallbacks.
            // This matches the eager materialization in eagerly_materialize_deferred()
            // but is called on-demand during conflict analysis (~90% of propagations
            // never reach this point).

            // Strategy 1: BoundExplanation chain.
            if let Some(reasons) = self.make_eager_implied_propagation_reasons(vi, need_upper) {
                if !reasons.is_empty()
                    && reasons
                        .iter()
                        .all(|r| self.asserted.get(&r.term) == Some(&r.value))
                {
                    return Some(reasons);
                }
            }

            // Strategy 2: Single-row reason collection.
            if let Some(ib_pair) = self.implied_bounds.get(vi) {
                let ib = if need_upper {
                    ib_pair.1.as_ref()
                } else {
                    ib_pair.0.as_ref()
                };
                if let Some(ib) = ib {
                    if ib.row_idx != usize::MAX && self.max_row_width <= 50 {
                        if let Some(reasons) =
                            self.collect_single_row_reasons(var, need_upper, ib.row_idx)
                        {
                            if !reasons.is_empty()
                                && reasons
                                    .iter()
                                    .all(|r| self.asserted.get(&r.term) == Some(&r.value))
                            {
                                return Some(reasons);
                            }
                        }
                    }
                }
            }

            // Strategy 3: Interval-based reasons from atom expression.
            let atom_term = _lit;
            if let Some(Some(info)) = self.atom_cache.get(&atom_term) {
                let is_le = info.is_le;
                let strict = info.strict;
                let polarity = (reason_data >> 33) & 1 != 0;
                let for_upper = if polarity { is_le } else { !is_le };
                // #8754 soundness fix: Before returning interval-based reasons,
                // verify the direct-only interval actually IMPLIES the
                // propagated literal. Without this check, Strategy 3 returns
                // reasons that are syntactically valid but do not prove the
                // propagation, because the ImpliedBound propagation was
                // enqueued against a tighter implied bound (from post-simplex
                // cascade or cross-negation overlay) while the reasons only
                // witness the looser direct-bound interval of the atom
                // expression. The missing-premise shape appeared as unsound
                // `:rule trust` lemmas in the Alethe proof on LP-family
                // benchmarks (rand_70_300, tsp_rand).
                let (lb, ub) = self.compute_expr_interval_direct_only(&info.expr);
                let implied_true = if polarity {
                    if is_le {
                        ub.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
                    } else {
                        lb.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
                    }
                } else if is_le {
                    lb.as_ref()
                        .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
                } else {
                    ub.as_ref()
                        .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
                };
                if !implied_true {
                    // Direct-bound interval does not imply the literal --
                    // reasons would be unsound. Reject this lazy propagation.
                    return None;
                }
                let reason = self.collect_interval_reasons(&info.expr, for_upper);
                if !reason.is_empty()
                    && reason
                        .iter()
                        .all(|r| self.asserted.get(&r.term) == Some(&r.value))
                {
                    return Some(reason);
                }
            }

            return None;
        }

        // DirectBound reason reconstruction.
        let info = self.vars.get(vi)?;
        let bound = if need_upper {
            info.upper.as_ref()
        } else {
            info.lower.as_ref()
        };
        let bound = bound?;
        let reason: Vec<TheoryLit> = bound
            .reason_pairs()
            .filter(|(term, _)| !term.is_sentinel())
            .map(|(term, val)| TheoryLit::new(term, val))
            .collect();
        if reason.is_empty() {
            return None;
        }
        Some(reason)
    }

    /// Record cross-theory reason literals so stale-reason guards accept them
    /// while they remain live in the surrounding DPLL trail.
    ///
    /// Exposed as `pub` (#8784) so sibling theories (e.g. LIA) can mark
    /// EUF-propagated shared-equality reasons as live — without this, LIA's
    /// stale-reason guard (which delegates to LRA's
    /// `conflict_literals_all_asserted`) would reject legitimate conflicts
    /// whose reasons were never added to LRA's own trail.
    pub fn record_cross_theory_reasons(&mut self, reasons: &[(TermId, bool)]) {
        for &(term, value) in reasons {
            if term.is_sentinel() {
                continue;
            }
            let prev = self.cross_theory_asserted.insert(term, value);
            self.cross_theory_asserted_trail.push((term, prev));
        }
    }

    /// Variant of `record_cross_theory_reasons` for TheoryLit slices.
    pub fn record_cross_theory_reasons_from_lits(&mut self, reasons: &[TheoryLit]) {
        for lit in reasons {
            if lit.term.is_sentinel() {
                continue;
            }
            let prev = self.cross_theory_asserted.insert(lit.term, lit.value);
            self.cross_theory_asserted_trail.push((lit.term, prev));
        }
    }

    /// Evaluate a linear expression against the current feasible LP model.
    ///
    /// Uses the feasible value snapshot when the current simplex state is
    /// infeasible (same logic as `suggest_phase`). Returns `None` if any
    /// referenced variable is out of bounds (shouldn't happen in practice).
    #[allow(dead_code)]
    fn eval_expr_in_model(&self, expr: &LinearExpr) -> Option<Rational> {
        let use_snapshot = !self.last_simplex_feasible && !self.feasible_value_snapshot.is_empty();

        let mut val = expr.constant.clone();
        for &(var, ref coeff) in &expr.coeffs {
            let vi = var as usize;
            if use_snapshot {
                let var_val = self.feasible_value_snapshot.get(vi)?;
                val += coeff * var_val;
            } else {
                let var_info = self.vars.get(vi)?;
                val += coeff * &var_info.value.x_rational();
            }
        }
        Some(val)
    }
}
