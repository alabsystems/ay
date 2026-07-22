// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::mutate::ReasonPolicy;
use super::*;

pub(super) struct PreprocessBveOutcome {
    pub(super) found_unsat: bool,
    pub(super) rebuilt_watches: bool,
}

impl Solver {
    pub(super) fn circuit_bve_lrat_preprocess_route_active(&self) -> bool {
        let sat_flags = ay_core::sat_disable_flags();
        self.cold.circuit_bve_lrat_route_enabled
            && self.cold.lrat_enabled
            && self.proof_manager.is_some()
            && !self.cold.has_been_incremental
            && !self.cold.elimfast_disabled
            && !sat_flags.no_inprocess
            && !sat_flags.no_bve
    }

    pub(super) fn run_circuit_bve_lrat_preprocess_route(
        &mut self,
        skip_expensive_preprocessing_passes: bool,
    ) -> PreprocessBveOutcome {
        if !self.circuit_bve_lrat_preprocess_route_active()
            || skip_expensive_preprocessing_passes
            || self.is_interrupted()
            || self.preprocess_timed_out()
        {
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        let inproc_ctrl_before_route = self.inproc_ctrl.clone();
        let bve_limit_before_route = self.cold.bve_limit;
        let instantiate_rebuilt_watches_before_route = self.cold.instantiate_rebuilt_watches;
        let bve_growth_bound_before_route = self.inproc.bve.growth_bound();
        let bve_fastelim_mode_before_route = self.inproc.bve.is_fastelim_mode();
        let bve_quick_elim_mode_before_route = self.inproc.bve.is_quick_elim_mode();

        self.inproc_ctrl.bve.enabled = true;
        self.inproc_ctrl.factor.enabled = false;
        self.inproc_ctrl.gate.enabled = false;
        self.cold.bve_limit = Some(1);

        // SOUNDNESS (push/pop clause-leak): scope selector variables stay
        // UNASSIGNED in vals[] during BVE. The selector literal +S is the
        // scope guard of every scoped clause [C, +S]; resolvents inherit it,
        // and pop()'s gc_scoped_clauses() reclaims them. The former #8579
        // fixup (vals[+S] = -1) made BVE's root-false pruning strip the
        // guard from resolvents, leaking guardless irredundant clauses
        // derived from scoped assertions across pop() — a spurious-UNSAT
        // hazard. See solve/inprocessing_incremental.rs for the full
        // analysis. (These preprocess routes additionally cannot run with
        // active scopes — push() latches has_been_incremental — so the
        // fixup was unreachable here in practice.)
        self.cold.instantiate_rebuilt_watches = false;
        self.watches.clear();
        self.watches_disconnected = true;
        self.cold.disconnected_deletions = 0;
        self.inproc.bve.set_growth_bound(16);
        self.inproc.bve.set_quick_elim_mode(false);
        self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);

        self.set_diagnostic_pass(DiagnosticPass::BVE);
        let mut bve_unsat = self.bve();
        self.clear_diagnostic_pass();

        self.cold.instantiate_rebuilt_watches = false;
        self.clear_stale_reasons();
        self.flush_learned_with_eliminated_vars();
        if !bve_unsat && self.inproc.bve.is_occ_populated() && self.qhead < self.trail.len() {
            bve_unsat = self.propagate_dense_check_unsat();
        }
        self.inproc.bve.finish_occ_saved_state_round();
        self.mark_trail_affected(0);
        self.watches_disconnected = false;
        self.reconnect_bve_watches(0);
        self.cold.bve_limit = bve_limit_before_route;
        self.cold.instantiate_rebuilt_watches = instantiate_rebuilt_watches_before_route;
        self.inproc.bve.restore_budget_mode(
            bve_growth_bound_before_route,
            bve_fastelim_mode_before_route,
            bve_quick_elim_mode_before_route,
        );
        self.inproc_ctrl = inproc_ctrl_before_route;

        if bve_unsat || self.propagate_check_unsat() {
            return PreprocessBveOutcome {
                found_unsat: true,
                rebuilt_watches: true,
            };
        }

        PreprocessBveOutcome {
            found_unsat: false,
            rebuilt_watches: true,
        }
    }

    pub(super) fn dense_factor_bve_lrat_preprocess_route_active(&self) -> bool {
        let sat_flags = ay_core::sat_disable_flags();
        self.cold.dense_factor_bve_lrat_route_enabled
            && self.cold.lrat_enabled
            && self.proof_manager.is_some()
            && !self.cold.has_been_incremental
            && !self.cold.elimfast_disabled
            && !sat_flags.no_inprocess
            && !sat_flags.no_bve
            && !sat_flags.no_factor
    }

    pub(super) fn run_dense_factor_bve_lrat_preprocess_route(
        &mut self,
        _skip_gate_dependent_passes: bool,
        skip_expensive_preprocessing_passes: bool,
    ) -> PreprocessBveOutcome {
        if !self.dense_factor_bve_lrat_preprocess_route_active()
            || skip_expensive_preprocessing_passes
            || self.is_interrupted()
            || self.preprocess_timed_out()
        {
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        let inproc_ctrl_before_route = self.inproc_ctrl.clone();
        self.inproc_ctrl.factor.enabled = true;
        self.inproc_ctrl.bve.enabled = true;
        self.inproc_ctrl.gate.enabled = false;

        if !self.should_preprocess_factor() {
            self.inproc_ctrl = inproc_ctrl_before_route;
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        let extension_start = self.num_vars;
        self.set_diagnostic_pass(DiagnosticPass::Factor);
        self.factorize();
        self.clear_diagnostic_pass();
        if self.propagate_check_unsat() {
            self.inproc_ctrl = inproc_ctrl_before_route;
            return PreprocessBveOutcome {
                found_unsat: true,
                rebuilt_watches: false,
            };
        }

        let extension_end = self.num_vars;
        if extension_end <= extension_start || self.is_interrupted() || self.preprocess_timed_out()
        {
            self.inproc_ctrl = inproc_ctrl_before_route;
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        let freeze_counts_before_bve = self.cold.freeze_counts.clone();
        for (var_idx, freeze_count) in self.cold.freeze_counts.iter_mut().enumerate() {
            if var_idx < extension_start || var_idx >= extension_end {
                *freeze_count = freeze_count.saturating_add(1);
            }
        }

        self.cold.instantiate_rebuilt_watches = false;
        self.watches.clear();
        self.watches_disconnected = true;
        self.cold.disconnected_deletions = 0;
        // Use additive BVE semantics for the extension surface. Fastelim caps
        // resolvents at the removed-clause count and rejects this route's
        // small factor-created surfaces before the LRAT preflight can apply.
        self.inproc.bve.reset_growth_bound_for_inprocessing();
        self.inproc.bve.increment_growth_bound();
        self.inproc.bve.increment_growth_bound();
        self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
        self.set_diagnostic_pass(DiagnosticPass::BVE);
        let mut bve_unsat = self.bve();
        self.clear_diagnostic_pass();
        self.cold.instantiate_rebuilt_watches = false;
        self.clear_stale_reasons();
        self.flush_learned_with_eliminated_vars();
        if !bve_unsat && self.inproc.bve.is_occ_populated() && self.qhead < self.trail.len() {
            bve_unsat = self.propagate_dense_check_unsat();
        }
        self.inproc.bve.finish_occ_saved_state_round();
        self.mark_trail_affected(0);
        self.watches_disconnected = false;
        // This private route clears watches up front, so reconnect all active
        // clauses instead of relying on the incremental arena baseline.
        self.reconnect_bve_watches(0);
        self.cold.freeze_counts = freeze_counts_before_bve;
        self.inproc_ctrl = inproc_ctrl_before_route;
        if bve_unsat || self.propagate_check_unsat() {
            return PreprocessBveOutcome {
                found_unsat: true,
                rebuilt_watches: true,
            };
        }

        PreprocessBveOutcome {
            found_unsat: false,
            rebuilt_watches: true,
        }
    }

    /// Whether the sparse-band large-formula preprocess-BVE unlock may bypass
    /// `skip_expensive_preprocessing_passes` for THIS formula.
    ///
    /// The flag is armed by the variant sparse-band predicate (density<=12,
    /// num_vars<=AY_BVE_SPARSE_MAX_VARS, non-LRAT Default route, AY_AB_BVE_SPARSE
    /// not killed). Here we additionally RE-CHECK the dense-skip guard on the
    /// current active clause/var counts so the bypass can never run expensive
    /// preprocess BVE on a dense formula, even if the formula densified after the
    /// header-derived flag was set. The sparse band (density<=12) cannot overlap
    /// the dense-skip thresholds (active>2M && density>20, or density>50), so on
    /// a genuinely sparse formula this returns the armed flag unchanged.
    ///
    /// This is BVE-specific: it does not relax the shared
    /// `skip_expensive_preprocessing_passes` used by congruence/subsume/probe.
    /// Cost stays bounded by the preprocess deadline (`preprocess_timed_out`) and
    /// the fastelim wall-clock guard (`FASTELIM_WALL_CLOCK_LIMIT_SECS`).
    pub(super) fn sparse_band_bve_preprocess_unlock_active(&self) -> bool {
        if !self.cold.sparse_band_bve_preprocess_unlock {
            return false;
        }
        let active_clauses = self.arena.active_clause_count();
        let active_vars_est = self.num_vars.saturating_sub(self.trail.len());
        let density = if active_vars_est > 0 {
            active_clauses as f64 / active_vars_est as f64
        } else {
            0.0
        };
        !config_preprocess_policy::PreprocessPolicy::skip_dense_formula(active_clauses, density)
    }

    /// Whether the post-collapse BVE eligibility re-derivation unlock is
    /// engaged for THIS formula RIGHT NOW (kill-switched, DEFAULT ON since
    /// 2026-07-10 wf_55735963 — `AY_AB_BVE_POST_COLLAPSE=0` disables).
    ///
    /// The congruence/decompose collapse (preprocess steps 1/2/2a, which fire
    /// under the default-ON AY_AB_SUBST_AUTO probe) can substitute away
    /// hundreds of thousands of variables, but every BVE gate keys on the
    /// ORIGINAL `self.num_vars`, which is never re-derived. This predicate
    /// RE-derives eligibility from the live lifecycle counts, so it is
    /// intrinsically ordered AFTER the collapse: before decompose runs,
    /// `count_removed() == 0` and the predicate is `false` (the collapse
    /// requirement), which also keeps it inert on elimination-only instances
    /// where congruence finds no gates.
    ///
    /// Guards, in evaluation order:
    ///   - env knob not killed (cheap OnceLock check first so the
    ///     kill-switched path costs nothing — G3 inertness);
    ///   - fail-closed on LRAT (`Bve { lrat: false }` in the capability
    ///     registry; the official route keeps BVE behind the scout knobs) and
    ///     on incremental (push/pop scope selectors);
    ///   - respects the AY_SAT_NO_BVE disable flag;
    ///   - the pure size predicate [`config_preprocess_policy::bve_post_collapse_reopens`]:
    ///     original `num_vars` ABOVE the 200K cap (only OPENS above-cap cases,
    ///     never touches in-band ones), a nonzero collapse, and re-derived
    ///     active vars <= AY_BVE_POST_COLLAPSE_MAX_VARS (default 600K — see
    ///     BVE_POST_COLLAPSE_MAX_VARS for the fast-inner rationale);
    ///   - live clause-side re-checks mirroring the shared expensive-pass
    ///     gate: active clauses <= PREPROCESS_EXPENSIVE_MAX_CLAUSES and the
    ///     dense-skip guard re-evaluated on the COLLAPSED counts, so the
    ///     unlock can never run expensive BVE on a residual that is still
    ///     huge or dense.
    ///
    /// Cost stays bounded by the fastelim wall guards; verdicts stay guarded
    /// by the model-validation gate and DRAT verification — this is
    /// scheduling/eligibility only, never a soundness relaxation.
    pub(in crate::solver) fn bve_post_collapse_unlock_active(&self) -> bool {
        if !config_preprocess_policy::bve_post_collapse_enabled() {
            return false;
        }
        if self.cold.lrat_enabled || self.cold.has_been_incremental {
            return false;
        }
        if ay_core::sat_disable_flags().no_bve {
            return false;
        }
        // O(1) prefilter hoisted out of `bve_post_collapse_reopens` (which
        // re-checks it): the unlock only OPENS above-cap cases, so bail on
        // in-band originals BEFORE the two O(num_vars) lifecycle scans below.
        // With the knob default-ON (wf_55735963) this predicate runs on every
        // solve (preprocess start + inprocessing elimination entries); the
        // hoist keeps the default in-band path at the same O(1) cost it had
        // when the knob was opt-in.
        if self.num_vars <= PREPROCESS_EXPENSIVE_MAX_VARS {
            return false;
        }
        let collapsed_vars = self.var_lifecycle.count_removed();
        let rederived_active_vars = self.var_lifecycle.count_active();
        if !config_preprocess_policy::bve_post_collapse_reopens(
            true,
            self.num_vars,
            rederived_active_vars,
            collapsed_vars,
            config_preprocess_policy::bve_post_collapse_max_vars(),
        ) {
            return false;
        }
        let active_clauses = self.arena.active_clause_count();
        if active_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES {
            return false;
        }
        let density = if rederived_active_vars > 0 {
            active_clauses as f64 / rederived_active_vars as f64
        } else {
            0.0
        };
        !config_preprocess_policy::PreprocessPolicy::skip_dense_formula(active_clauses, density)
    }

    /// Complete the giant raw-BVE unlock qualification for THIS formula
    /// (lever 3, 2026-07-11 sparse-prize completion round; OPT-IN via
    /// `AY_AB_BVE_GIANT_RAW=1` through the route flag — measured
    /// default-OFF, see `VariantConfig::bve_giant_raw_route_active`).
    ///
    /// Called once from the preprocess pipeline IMMEDIATELY after the
    /// collapse stage (the same placement as the post-collapse arming block
    /// — earlier the "no collapse" check is vacuous because decompose has
    /// not had its chance yet). Latches `cold.bve_giant_raw_qualified` so
    /// later predicates (`bve_giant_raw_unlock_active`,
    /// `bve_sparse_deep_active`) stay O(1) and — critically — stay TRUE
    /// after BVE itself starts eliminating variables (`count_removed()`
    /// flips nonzero on the first elimination, which would otherwise
    /// disqualify the deep budgets mid-phase).
    ///
    /// Guards, in evaluation order:
    ///   - the variant route/band flag (Default DIMACS non-LRAT, 150K <
    ///     parsed vars <= 2M, parsed clauses <= 8M, parsed density <= 12 —
    ///     see `VariantConfig::bve_giant_raw_route_active`);
    ///   - fail-closed on LRAT and incremental (mirrors the post-collapse
    ///     unlock; the official route keeps BVE behind the scout knobs);
    ///   - respects the AY_SAT_NO_BVE disable flag;
    ///   - the pure predicate
    ///     [`config_preprocess_policy::bve_giant_raw_qualifies`]: collapse
    ///     substituted NOTHING (collapsed instances belong to the
    ///     post-collapse lever — the two unlocks are disjoint by
    ///     construction) and the live dense-skip re-check passes.
    ///
    /// Returns whether the latch is set after the call. Scheduling only —
    /// verdicts stay guarded by model validation and DRAT verification.
    pub(in crate::solver) fn try_qualify_bve_giant_raw(&mut self) -> bool {
        if self.cold.bve_giant_raw_qualified {
            return true;
        }
        if !self.cold.bve_giant_raw_unlock {
            return false;
        }
        if self.cold.lrat_enabled || self.cold.has_been_incremental {
            return false;
        }
        if ay_core::sat_disable_flags().no_bve {
            return false;
        }
        let collapsed_vars = self.var_lifecycle.count_removed();
        let active_clauses = self.arena.active_clause_count();
        let active_vars = self.var_lifecycle.count_active();
        if config_preprocess_policy::bve_giant_raw_qualifies(
            true,
            collapsed_vars,
            active_clauses,
            active_vars,
        ) {
            self.cold.bve_giant_raw_qualified = true;
        }
        self.cold.bve_giant_raw_qualified
    }

    /// Whether the giant raw-BVE unlock is engaged for THIS formula RIGHT
    /// NOW (lever 3; O(1) — the heavy checks were latched by
    /// [`Self::try_qualify_bve_giant_raw`]). Fail-closed re-checks on
    /// LRAT/incremental/AY_SAT_NO_BVE keep later state changes (e.g. a
    /// push() after preprocess latching) from riding the latch.
    pub(in crate::solver) fn bve_giant_raw_unlock_active(&self) -> bool {
        self.cold.bve_giant_raw_qualified
            && !self.cold.lrat_enabled
            && !self.cold.has_been_incremental
            && !ay_core::sat_disable_flags().no_bve
    }

    /// Complete the post-factor BVE clause-reopen qualification for THIS
    /// formula (opt-in `AY_AB_BVE_POST_FACTOR`, DEFAULT OFF — MEASURED-NEGATIVE
    /// on the class it targets; see
    /// [`config_preprocess_policy::bve_post_factor_reopens`] and
    /// [`BVE_POST_FACTOR_MIN_COLLAPSE_RATIO`]).
    ///
    /// Called once from the preprocess pipeline IMMEDIATELY AFTER the factor
    /// step (the CLAUSE-axis analogue of the post-collapse arming block — the
    /// re-derivation is meaningless earlier because factoring has not run yet).
    /// Reads the pre-factor active-clause count and num_vars latched right
    /// before `factorize()`, re-derives eligibility on the FACTORED residual,
    /// and latches `cold.bve_post_factor_qualified` so later predicates stay
    /// O(1) and — critically — stay TRUE after BVE itself starts eliminating
    /// (which shrinks the live active-clause count).
    ///
    /// Guards, in evaluation order (mirror of `try_qualify_bve_giant_raw`):
    ///   - the env knob (default OFF — the whole lever is opt-in);
    ///   - fail-closed on LRAT and incremental (the official route keeps BVE
    ///     behind the scout knobs; push/pop scope selectors);
    ///   - respects the AY_SAT_NO_BVE disable flag;
    ///   - the pure predicate
    ///     [`config_preprocess_policy::bve_post_factor_reopens`]: the ORIGINAL
    ///     active clauses were above the expensive-pass cap (only OPENS
    ///     above-cap cases), factoring created extension vars, the residual is
    ///     under the cap, and the collapse was large-ratio; AND
    ///   - the live dense-skip re-check on the COLLAPSED counts, so the reopen
    ///     can never run expensive BVE on a residual that is still dense (same
    ///     defense the sparse-band / giant-raw / post-collapse unlocks apply).
    ///
    /// Returns whether the latch is set after the call. Scheduling/eligibility
    /// only — verdicts stay guarded by model validation and DRAT verification;
    /// BVE reconstruction and proof emission are untouched.
    pub(in crate::solver) fn try_qualify_bve_post_factor(&mut self) -> bool {
        if self.cold.bve_post_factor_qualified {
            return true;
        }
        if !config_preprocess_policy::bve_post_factor_enabled() {
            return false;
        }
        if self.cold.lrat_enabled || self.cold.has_been_incremental {
            return false;
        }
        if ay_core::sat_disable_flags().no_bve {
            return false;
        }
        let rederived_active_clauses = self.arena.active_clause_count();
        let factored_vars = self.num_vars.saturating_sub(self.cold.pre_factor_num_vars);
        if !config_preprocess_policy::bve_post_factor_reopens(
            true,
            self.cold.pre_factor_active_clauses,
            rederived_active_clauses,
            factored_vars,
            PREPROCESS_EXPENSIVE_MAX_CLAUSES,
            config_preprocess_policy::bve_post_factor_min_collapse_ratio(),
        ) {
            return false;
        }
        // Live dense-skip re-check on the collapsed counts (mirror of the
        // sparse-band / giant-raw unlocks): never run expensive BVE on a
        // residual that is still dense even after the clause collapse.
        let active_vars_est = self.num_vars.saturating_sub(self.trail.len());
        let density = if active_vars_est > 0 {
            rederived_active_clauses as f64 / active_vars_est as f64
        } else {
            0.0
        };
        if config_preprocess_policy::PreprocessPolicy::skip_dense_formula(
            rederived_active_clauses,
            density,
        ) {
            return false;
        }
        self.cold.bve_post_factor_qualified = true;
        true
    }

    /// Whether the post-factor BVE clause-reopen is engaged for THIS formula
    /// RIGHT NOW (opt-in `AY_AB_BVE_POST_FACTOR`; O(1) — the heavy checks were
    /// latched by [`Self::try_qualify_bve_post_factor`]). Fail-closed re-checks
    /// on LRAT/incremental/AY_SAT_NO_BVE keep later state changes from riding
    /// the latch. Mirror of `bve_giant_raw_unlock_active`.
    pub(in crate::solver) fn bve_post_factor_unlock_active(&self) -> bool {
        self.cold.bve_post_factor_qualified
            && !self.cold.lrat_enabled
            && !self.cold.has_been_incremental
            && !ay_core::sat_disable_flags().no_bve
    }

    /// Whether the DEEP sparse-band preprocess-BVE lever is engaged for THIS
    /// formula (kill-switched, DEFAULT ON since 2026-07-10 — wf_55735963
    /// collapse+BVE default flip; kill-switch AY_AB_BVE_SPARSE_DEEP=0).
    ///
    /// Requires ALL of:
    ///   - the sparse-band unlock flag is armed (density<=12, non-LRAT Default,
    ///     AY_AB_BVE_SPARSE not killed) — reuses `sparse_band_bve_preprocess_unlock`
    ///     — OR the post-collapse unlock qualified this formula (see
    ///     COMPOSITION below);
    ///   - num_vars > BVE_SPARSE_DEEP_MIN_VARS (150K). This keeps every
    ///     default-band (<=150K var) input on the existing path so the deep
    ///     wall/effort/round increases can never regress small/medium in-band
    ///     solves. Above the floor, the sparse-band arm still needs the
    ///     operator to raise AY_BVE_SPARSE_MAX_VARS; the DEFAULT-reachable
    ///     entry is the post-collapse composition;
    ///   - AY_AB_BVE_SPARSE_DEEP not killed ("0" disables; unset/anything
    ///     else enables). Default flipped ON with the 3-knob stack
    ///     (SUBST_AUTO + BVE_POST_COLLAPSE + BVE_SPARSE_DEEP), measured on
    ///     the main2025 scoreboard protocol: +7 UNSAT flips (df813fe7 80s
    ///     with 188,557 deep-budget eliminations), 0 hard losses, dense band
    ///     inert.
    ///
    /// The predicate is deliberately size-gated rather than clause-gated so
    /// its budget raises stay off every default-band input even with the
    /// knob default-ON.
    ///
    /// COMPOSITION (post-collapse lever): the deep budgets also engage when
    /// the post-collapse unlock (`AY_AB_BVE_POST_COLLAPSE`, default ON) is what opened
    /// BVE — the two knobs compose (deep budgets applied to the
    /// post-collapse-opened pass) without being folded: each keeps its own
    /// enable env and its own scope predicate. Ordering keeps the default
    /// path cheap: the sparse-band flag short-circuits first, and the
    /// post-collapse check starts with its own OnceLock env read.
    ///
    /// COMPOSITION (giant raw lever, 2026-07-11 sparse-prize completion
    /// round): the deep budgets equally engage when the giant raw-BVE
    /// unlock (`AY_AB_BVE_GIANT_RAW`) opened BVE on an elimination-shaped
    /// no-collapse giant — deep is the whole point there (9d7caee5 needs
    /// ~1.57M eliminations; the non-deep 2s wall + scaled effort reach <1%).
    /// O(1): the giant-raw check reads the preprocess-latched qualification.
    pub(in crate::solver) fn bve_sparse_deep_active(&self) -> bool {
        if !self.cold.sparse_band_bve_preprocess_unlock
            && !self.bve_giant_raw_unlock_active()
            && !self.bve_post_collapse_unlock_active()
            && !self.bve_post_factor_unlock_active()
        {
            return false;
        }
        use std::sync::OnceLock;
        // Min-var floor for deep. Default BVE_SPARSE_DEEP_MIN_VARS (150K);
        // overridable via AY_BVE_SPARSE_DEEP_MIN_VARS (used to validate the deep
        // reconstruction/proof path on smaller BVE-heavy instances).
        static MIN_VARS: OnceLock<usize> = OnceLock::new();
        let min_vars = *MIN_VARS.get_or_init(|| {
            std::env::var("AY_BVE_SPARSE_DEEP_MIN_VARS")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(BVE_SPARSE_DEEP_MIN_VARS)
        });
        if self.num_vars <= min_vars {
            return false;
        }
        static ENABLED: OnceLock<bool> = OnceLock::new();
        *ENABLED.get_or_init(|| {
            !matches!(
                std::env::var("AY_AB_BVE_SPARSE_DEEP").ok().as_deref(),
                Some("0")
            )
        })
    }

    /// Wall-clock multiplier for the preprocess-BVE budgets: 4x
    /// (PROOF_WALL_BUDGET_SCALE) when DRAT proof emission is active, 1
    /// otherwise. DRAT step-tracking inflates the per-step cost of the
    /// collapse+BVE work ~4x, so an unscaled wall admits ~1/4 of the work
    /// under --proof and the deep-path flips never materialize (df813fe7:
    /// 188,557 eliminations no-proof vs 4,473 truncated under proof — see
    /// PROOF_WALL_BUDGET_SCALE). Scaling the wall (not the work metric)
    /// keeps admitted WORK roughly proof-invariant; behavior is exactly
    /// unchanged for non-proof runs. Scheduling only — verdict soundness
    /// stays guarded by DRAT verification itself.
    ///
    /// Keyed on `proof_manager` (DRAT emission), not `lrat_enabled`: the
    /// LRAT route clamps BVE off in the capability registry anyway, and the
    /// walls this scales are all on BVE/collapse paths.
    pub(in crate::solver) fn bve_wall_budget_scale(&self) -> u64 {
        if self.proof_manager.is_some() {
            PROOF_WALL_BUDGET_SCALE
        } else {
            1
        }
    }

    pub(super) fn run_preprocess_bve(
        &mut self,
        skip_gate_dependent_passes: bool,
        _skip_expensive_preprocessing_passes: bool,
    ) -> PreprocessBveOutcome {
        if !self.inproc_ctrl.bve.enabled {
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        // (#8448) Skip BVE on very large dense formulas where the O(clauses)
        // watch teardown + occ-list rebuild + watch reconnection overhead
        // exceeds the benefit of variable elimination. On shuffling-2
        // (4.7M clauses, density=33.8), BVE's infrastructure costs:
        //   - watches.clear(): ~0.1s
        //   - occ-list rebuild: ~1s per pass
        //   - flush_learned_with_eliminated_vars: ~0.5s
        //   - reconnect_bve_watches: ~6s
        // Total: ~8-10s, while CDCL search alone solves in <2s.
        // CaDiCaL's BVE is effective on shuffling-2 (eliminates 39% of vars),
        // but AY's watch reconnection is ~4x slower than CaDiCaL's due to
        // different watch list implementation. Until watch reconnection is
        // optimized, skip BVE when the per-variable overhead is net-negative.
        // Sparse-band large-formula unlock: allow preprocess BVE/fastelim to run
        // even when the shared expensive-pass skip is set (num_vars>200K or
        // num_clauses>3M), but ONLY inside the sparse band and only for BVE. On
        // huge sparse formulas (e.g. 1.69M vars / 5.96M clauses, density 3.5)
        // this is the only way AY engages kissat-style dense elimination in
        // PREPROCESSING; without it only interval-scheduled inproc BVE runs and
        // reaches <1% elimination. The dense-skip guard is re-checked inside
        // sparse_band_bve_preprocess_unlock_active(), and the preprocess deadline
        // + fastelim wall guard below bound the cost. The gate-based Passes 2+
        // stay gated on _skip_expensive to avoid gate-extraction overhead on huge
        // formulas — this unlock is fastelim-only.
        //
        // Post-collapse re-derivation (AY_AB_BVE_POST_COLLAPSE, default ON
        // since 2026-07-10 wf_55735963; =0 kill-switch):
        // a second, independent bypass for formulas whose ORIGINAL num_vars
        // exceeded the 200K cap but whose ACTIVE count collapsed under the
        // post-collapse cap after congruence+decompose substitution — see
        // bve_post_collapse_unlock_active() for the full guard set. Like the
        // sparse-band unlock, it is fastelim-only (Passes 2+ stay gated).
        // Giant raw-BVE unlock (lever 3, AY_AB_BVE_GIANT_RAW; 2026-07-11
        // sparse-prize completion round): a third independent bypass for
        // elimination-shaped no-collapse giants (150K < vars <= 2M, clauses
        // <= 8M, density <= 12, zero substitutions) — the class where kissat
        // wins purely by dense elimination (9d7caee5: 93% eliminated,
        // unsat@66s) but AY had NO preprocess-BVE route at all. Qualified
        // once post-collapse-stage by try_qualify_bve_giant_raw; fastelim-only
        // like the other two bypasses (Passes 2+ stay gated).
        // Post-factor clause-reopen (lever, AY_AB_BVE_POST_FACTOR; DEFAULT OFF
        // — MEASURED-NEGATIVE, see bve_post_factor_unlock_active): a fourth
        // independent bypass for formulas whose ORIGINAL clause count exceeded
        // the 3M cap but whose ACTIVE count factor-collapsed under it (the
        // density-264 huge-binary cluster: f6a085f3 11.1M → ~371K). Qualified
        // once post-factor-stage by try_qualify_bve_post_factor; fastelim-only
        // like the other three bypasses (Passes 2+ stay gated).
        let post_collapse_unlock =
            _skip_expensive_preprocessing_passes && self.bve_post_collapse_unlock_active();
        let giant_raw_unlock =
            _skip_expensive_preprocessing_passes && self.bve_giant_raw_unlock_active();
        let post_factor_unlock =
            _skip_expensive_preprocessing_passes && self.bve_post_factor_unlock_active();
        if _skip_expensive_preprocessing_passes
            && !post_collapse_unlock
            && !giant_raw_unlock
            && !post_factor_unlock
            && !self.sparse_band_bve_preprocess_unlock_active()
        {
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        // (#8448) BVE deadline check: skip BVE when the global preprocessing
        // budget is already exhausted. BVE is the most expensive preprocessing
        // pass and runs last in the pipeline. If earlier passes (congruence,
        // sweep, decompose, HTR, probing, factor, subsumption) have already
        // consumed the budget, search is more productive than additional
        // preprocessing.
        //
        // On ecarev-110 (127K vars, 742K clauses, 2s budget), skipping BVE
        // when the budget is exhausted gives search the full remaining time,
        // recovering it from timeout to ~6s solve time.
        //
        // On shuffling-2 (138K vars, 4.7M clauses), the sweep budget fixes
        // (first-call detection, per-variable kitten limit) enable solving
        // without BVE. The 7/23 SAT-COMP score was achieved with this
        // deadline check active (commit e8dfdce4d).
        //
        // BVE has its own wall-clock guards (FASTELIM_WALL_CLOCK_LIMIT_SECS,
        // intra-round clock checks) that bound its execution when it DOES run.
        //
        // Post-collapse unlock deadline extension: the collapse that QUALIFIED
        // this formula (congruence probe + decompose + fixpoint on a >200K-var
        // input) typically consumes the whole 2s large-formula preprocess
        // budget itself, so without an extension the deadline check below
        // would skip the just-unlocked BVE every time — the lever would be
        // dead on arrival. Push the deadline out by the BVE wall budget (the
        // same pattern the substitution fixpoint uses for its own rounds):
        // 2x the fastelim per-call wall (Pass 0 + Pass 1) in the default
        // shape, or the deep preprocess budget when AY_AB_BVE_SPARSE_DEEP
        // composes (mirroring the budget raise deep gets at preprocess start
        // when it is armed pre-collapse). Bounded and knob-scoped: no-op
        // unless AY_AB_BVE_POST_COLLAPSE (default ON, =0 kills) actually
        // unlocked this call.
        if post_collapse_unlock || giant_raw_unlock || post_factor_unlock {
            // Proof-aware (wf_0c7d84e9): see PROOF_WALL_BUDGET_SCALE.
            let extension_secs = self.bve_wall_budget_scale()
                * if self.bve_sparse_deep_active() {
                    BVE_SPARSE_DEEP_PREPROCESS_BUDGET_SECS
                } else {
                    2 * FASTELIM_WALL_CLOCK_LIMIT_SECS
                };
            let extended =
                ay_core::time::Instant::now() + std::time::Duration::from_secs(extension_secs);
            match self.cold.preprocess_deadline.as_mut() {
                Some(deadline) if *deadline < extended => *deadline = extended,
                _ => {}
            }
        }
        if self.preprocess_timed_out() {
            return PreprocessBveOutcome {
                found_unsat: false,
                rebuilt_watches: false,
            };
        }

        // SOUNDNESS (push/pop clause-leak): scope selector variables stay
        // UNASSIGNED in vals[] during BVE. The selector literal +S is the
        // scope guard of every scoped clause [C, +S]; resolvents inherit it,
        // and pop()'s gc_scoped_clauses() reclaims them. The former #8579
        // fixup (vals[+S] = -1) made BVE's root-false pruning strip the
        // guard from resolvents, leaking guardless irredundant clauses
        // derived from scoped assertions across pop() — a spurious-UNSAT
        // hazard. See solve/inprocessing_incremental.rs for the full
        // analysis. (These preprocess routes additionally cannot run with
        // active scopes — push() latches has_been_incremental — so the
        // fixup was unreachable here in practice.)

        // Instantiate gate (lever 2, AY_AB_BVE_INST_GATE — see
        // bve_inst_gate_enabled): stamp a new elimination phase. The passes
        // below call bve_body 2-7 times (quick + fastelim + gate passes);
        // under the gate only the first productive one runs instantiate,
        // wall-bounded, instead of every one paying the measured
        // 6.5-13.2s unbudgeted tax.
        self.cold.bve_elim_phase_seq = self.cold.bve_elim_phase_seq.wrapping_add(1);

        // Disconnect watches for BVE (#8093). BVE operates on occurrence
        // lists, not 2WL watches. Clear watches before BVE because
        // instantiate() (called from bve_body) does a temporary full rebuild
        // then tears down with watches.clear(). After all BVE rounds,
        // reconnect_bve_watches(0) re-attaches all active clauses from
        // scratch. CaDiCaL elim.cpp:1046, Kissat eliminate.c:587.
        self.watches.clear();
        self.watches_disconnected = true;
        self.cold.disconnected_deletions = 0; // #8093: reset for purge-skip optimization
        let bve_wall_start = ay_core::time::Instant::now();

        let mut bve_unsat = false;

        // Pass 0: quick elimination (CaDiCaL elimfast pattern, #8242).
        // Runs a tight BVE pre-pass with bound=8, targeting only trivially
        // eliminable variables (few occurrences, small clauses). This catches
        // "free" eliminations before the main fastelim pass raises the bound
        // to 16, reducing the candidate pool for subsequent passes.
        // Reference: CaDiCaL elimfast.cpp:186-255, Kissat eliminate.c.
        if !self.cold.elimfast_disabled {
            let elim_before_quick = self.var_lifecycle.count_removed();
            let cls_before_quick = self.arena.active_clause_count();
            self.inproc
                .bve
                .set_growth_bound(crate::bve::fast_eliminate::QUICK_ELIM_BOUND);
            self.inproc.bve.set_quick_elim_mode(true);
            self.set_diagnostic_pass(DiagnosticPass::BVE);
            bve_unsat = (self.cold.last_bve_fixed != self.fixed_count
                || self.cold.last_bve_marked != self.cold.bve_marked)
                && self.bve();
            self.clear_diagnostic_pass();
            self.inproc.bve.set_quick_elim_mode(false);
            let elim_after_quick = self.var_lifecycle.count_removed();
            let cls_after_quick = self.arena.active_clause_count();
            self.inproc.bve.stats_mut().fast_elim_vars +=
                (elim_after_quick - elim_before_quick) as u64;
            self.inproc.bve.stats_mut().fast_elim_clauses +=
                cls_before_quick.saturating_sub(cls_after_quick) as u64;
            if bve_unsat || self.is_interrupted() {
                self.clear_stale_reasons();
                // Flush learned clauses containing eliminated variables (#8482)
                // before reconnecting watches, even on early exit.
                self.flush_learned_with_eliminated_vars();
                self.mark_trail_affected(0);
                self.watches_disconnected = false;
                self.reconnect_bve_watches(0);
                return PreprocessBveOutcome {
                    found_unsat: bve_unsat,
                    rebuilt_watches: true,
                };
            }
        }

        // Pass 1: fastelim (bound=16). Runs on all formulas, including uniform
        // random k-SAT, because it relies on occurrence counting rather than
        // gate structure. Bound=16 matches Kissat's eliminatebound default
        // (options.h:42), up from the previous 8 (#8134).
        // Force the fixpoint guards to re-fire after Pass 0 ran bve(),
        // which updates last_bve_fixed and last_bve_marked. Without this
        // reset, Pass 1 guard short-circuits to false (#8242).
        //
        // (#8448) Check both preprocessing deadline AND total BVE wall-clock
        // budget before running Pass 1. On shuffling-2 (4.7M clauses), Pass 0
        // alone takes ~4s (1s occ-rebuild + 2s elimination + 1s GC). The
        // per-pass FASTELIM_WALL_CLOCK_LIMIT_SECS only bounds individual bve()
        // calls, but the aggregate across Pass 0 + Pass 1 can reach 8s+.
        // This check uses the outer bve_wall_start (from run_preprocess_bve)
        // to cap total BVE time including occ-list rebuilds and inter-pass GC.
        // DEEP band: use the larger cumulative wall so Pass 1 (bound 16) still
        // starts after Pass 0 (quick-elim) consumed up to the deep per-call
        // wall, and do not let the (extended) preprocess deadline gate Pass 1.
        // Proof-aware (wf_0c7d84e9): see PROOF_WALL_BUDGET_SCALE.
        let pass1_wall_limit = self.bve_wall_budget_scale()
            * if self.bve_sparse_deep_active() {
                BVE_SPARSE_DEEP_TOTAL_WALL_SECS
            } else {
                FASTELIM_WALL_CLOCK_LIMIT_SECS
            };
        if (self.bve_sparse_deep_active() || !self.preprocess_timed_out())
            && bve_wall_start.elapsed().as_secs() < pass1_wall_limit
        {
            if !self.cold.elimfast_disabled {
                self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
            }
            self.inproc.bve.set_growth_bound(16);
            self.set_diagnostic_pass(DiagnosticPass::BVE);
            bve_unsat = (self.cold.last_bve_fixed != self.fixed_count
                || self.cold.last_bve_marked != self.cold.bve_marked)
                && self.bve();
            self.clear_diagnostic_pass();
        }

        // Passes 2+: gate-based BVE with progressive growth bounds (#8134).
        // Kissat runs up to 7 elimination rounds at bounds 0->1->2->4->8->16,
        // interleaving subsumption between them. AY does fastelim(16) first,
        // then gate-BVE at additive bounds 1,2,4,8,16. Each pass enables
        // further elimination as the growth bound relaxes. Interleave
        // subsumption between passes to expose new candidates via clause
        // strengthening. Skip on uniform non-binary formulas (no profitable
        // gates) and large formulas where gate extraction overhead dominates.
        if self.inproc_ctrl.gate.enabled
            && !skip_gate_dependent_passes
            && !_skip_expensive_preprocessing_passes
            && !self.preprocess_timed_out()
        {
            let elim_before_gate = self.var_lifecycle.count_removed();
            // Cumulative clause growth guard (#8398): track active clause
            // count at the start of gate-based BVE passes. On dense binary
            // instances (clique/graph-coloring), each gate-based pass adds
            // resolvents that make the formula progressively harder. Stop
            // escalating bounds when active clauses grow beyond 10% of the
            // baseline. Without this guard, 5 gate-based passes on
            // clique_n2_k10 grow active clauses from 887 to 1455 (+64%),
            // causing search timeout.
            let gate_bve_baseline_clauses = self.arena.active_clause_count();
            // Track the minimum (best) clause count seen across passes.
            // Break when clauses grow above this running minimum. This
            // catches the pattern where early passes reduce clauses but
            // later passes add net resolvents: e.g. braun.9 goes
            // 4630->4619->4436->4543->4664->5053. With a running minimum,
            // we stop at pass 4 (4543 > 4436) instead of pass 6 (5053).
            let mut best_clause_count = gate_bve_baseline_clauses;
            for pass_bound in [1, 2, 4, 8, 16] {
                if bve_unsat || self.is_interrupted() || self.preprocess_timed_out() {
                    break;
                }
                // Wall-clock guard (#8361): stop adding gate-based BVE passes
                // if preprocessing is already taking too long. Reduced from 5s
                // to 2s: gate-BVE consumed ~4s for marginal benefit on medium
                // instances. Kissat spends only 0.89s on eliminate.
                if bve_wall_start.elapsed().as_secs() >= 2 {
                    break;
                }
                // Cumulative clause growth guard (#8398, #8482): stop escalating
                // gate-based BVE bounds when the formula has grown beyond the
                // best (minimum) clause count observed so far. This catches
                // the pathological pattern where early passes reduce clauses
                // productively but later passes cause net resolvent growth.
                //
                // #8482: Uses running-minimum with tight threshold. On
                // braun.9, the original baseline approach (10%) allowed 7
                // passes growing from 4436 (best) to 5800+ clauses. The
                // running-minimum approach stops after pass 3 (bound=4)
                // when pass 4 (bound=8) grows clauses from 4436 to 4543.
                // A 2% slack on the running minimum allows minor fluctuations
                // from subsumption interleaving while catching sustained
                // resolvent accumulation.
                let current_clauses = self.arena.active_clause_count();
                best_clause_count = best_clause_count.min(current_clauses);
                if current_clauses > best_clause_count + best_clause_count / 50 {
                    break;
                }
                let elim_before = self.var_lifecycle.count_removed();
                self.inproc.bve.reset_growth_bound_for_inprocessing();
                let mut current = 0u32;
                while current < pass_bound {
                    self.inproc.bve.increment_growth_bound();
                    current = if current == 0 { 1 } else { current * 2 };
                }
                self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
                self.set_diagnostic_pass(DiagnosticPass::BVE);
                bve_unsat = self.bve();
                self.clear_diagnostic_pass();
                // Interleave subsumption between BVE passes (Kissat pattern:
                // eliminate.c interleaves forward/backward subsumption).
                // This strengthens/removes clauses exposed by the latest
                // round of BVE, enabling further eliminations.
                // Only run subsumption when the preceding BVE pass was productive,
                // to avoid overhead on formulas where gate-BVE has little effect.
                let elim_after_bve = self.var_lifecycle.count_removed();
                if elim_after_bve > elim_before && !bve_unsat && !self.is_interrupted() {
                    self.subsume();
                }
                // Post-pass clause growth check (#8482): if this pass caused
                // the formula to grow beyond the running minimum, stop
                // immediately. On braun.9, pass 4 (bound=8) grows from
                // 4436 to ~4500+ even after subsumption recovery. Any net
                // growth above the best count signals diminishing returns
                // since each added resolvent makes CDCL search harder on
                // circuit-structured formulas.
                let post_pass_clauses = self.arena.active_clause_count();
                if post_pass_clauses > best_clause_count {
                    break;
                }
                best_clause_count = best_clause_count.min(post_pass_clauses);
                // Early termination: stop escalating bounds if the last pass
                // was unproductive (no new eliminations). Higher bounds won't
                // help if the formula is already saturated at this bound.
                // Use threshold >= 4 (#8134): on structured formulas, the first
                // gate-BVE rounds at bound 1-2 may be unproductive but
                // subsumption cascade effects enable eliminations at bound 4+.
                if elim_after_bve == elim_before && pass_bound >= 4 {
                    break;
                }
            }
            let _elim_gate_total = self.var_lifecycle.count_removed() - elim_before_gate;
        }

        self.clear_stale_reasons();

        // Flush learned clauses containing eliminated variables (#8482)
        // before reconnecting watches.
        self.flush_learned_with_eliminated_vars();

        // Dense propagation before watch rebuild (#8088): run occ-list-based
        // propagation while BVE occurrence lists are still live, catching
        // units/conflicts before the expensive O(clauses) watch rebuild.
        if !bve_unsat && self.inproc.bve.is_occ_populated() && self.qhead < self.trail.len() {
            bve_unsat = self.propagate_dense_check_unsat();
        }
        self.inproc.bve.finish_occ_saved_state_round();

        // Reconnect watches after preprocessing BVE (#8093): use
        // reconnect_bve_watches(0) instead of rebuild_watches(). With
        // baseline=0 on cleared watch lists, this attaches all active
        // clauses from scratch — functionally equivalent to rebuild_watches()
        // but unified with the incremental reconnection infrastructure.
        // Full re-propagation needed (#8095).
        self.mark_trail_affected(0);
        self.watches_disconnected = false;
        self.reconnect_bve_watches(0);

        if bve_unsat || self.propagate_check_unsat() {
            return PreprocessBveOutcome {
                found_unsat: true,
                rebuilt_watches: true,
            };
        }

        PreprocessBveOutcome {
            found_unsat: false,
            rebuilt_watches: true,
        }
    }

    /// Flush learned clauses containing eliminated variables (#8482).
    ///
    /// BVE only deletes irredundant clauses from occurrence lists. Learned
    /// (redundant) clauses are not tracked by occ lists and survive BVE.
    /// When watches are reconnected after BVE, these stale learned clauses
    /// get watched. Post-BVE probing (or search) can then propagate through
    /// a stale learned clause, assigning an eliminated variable. This causes
    /// a debug_assert panic in backtrack (removed variable on trail) and can
    /// produce invalid models in release mode.
    ///
    /// CaDiCaL: `flush_eliminated` (elim.cpp) removes both irredundant AND
    /// redundant clauses containing eliminated variables after BVE. AY's BVE
    /// already handles irredundant clauses via occurrence-list-driven deletion;
    /// this method handles the redundant (learned) clauses that BVE misses.
    pub(in crate::solver) fn flush_learned_with_eliminated_vars(&mut self) {
        let mut to_flush: Vec<usize> = Vec::new();
        for idx in self.arena.indices() {
            if !self.arena.is_learned(idx) {
                continue;
            }
            let len = self.arena.len_of(idx);
            let has_eliminated = (0..len).any(|k| {
                let lit = self.arena.literal(idx, k);
                self.var_lifecycle.is_removed(lit.variable().index())
            });
            if has_eliminated {
                to_flush.push(idx);
            }
        }
        for idx in to_flush {
            self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
        }
    }
}
