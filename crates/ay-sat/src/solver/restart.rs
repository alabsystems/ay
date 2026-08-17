// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Restart decisions (Luby + glucose EMA), phase saving, and trail reuse.
//!
//! Rephasing logic is in `rephase.rs`.

use super::*;
use crate::solver::solver_stats::RestartAttribution;

/// Focused-mode restart margin. (B4: the AY_AB_FOCUSED_MARGIN env override is
/// deleted; the constant stands.)
fn ab_focused_margin() -> f64 {
    RESTART_MARGIN_FOCUSED
}

impl Solver {
    /// Equiticks progress-gate window in conflicts (`--sat-eqt-progress`),
    /// read once per solve and cached. Returns 0 when disabled (the default),
    /// which makes the progress-gated stable-phase extension fully inert. A
    /// value of `1` selects `EQT_PROGRESS_WINDOW_DEFAULT`; any `N > 1` sets the
    /// window directly (used to sweep the window in A/B). The gate additionally
    /// requires equiticks to be active (`stable_tick_hardcap > 0`), so setting
    /// this without `--sat-mode-equiticks` has no effect.
    fn eqt_progress_window(&mut self) -> u64 {
        match self.cold.eqt_progress_cached {
            Some(w) => w,
            None => {
                let w = match ay_core::sat_ab_switches().eqt_progress {
                    Some(1) => EQT_PROGRESS_WINDOW_DEFAULT,
                    Some(n) if n > 1 => n,
                    _ => 0,
                };
                self.cold.eqt_progress_cached = Some(w);
                w
            }
        }
    }

    pub(super) fn dense_mutex_focused_restart_gate(active_vars: usize) -> u64 {
        let quarter = (active_vars / 4) as u64;
        DENSE_MUTEX_FOCUSED_RESTART_MIN_GATE.max(DENSE_MUTEX_FOCUSED_RESTART_MAX_GATE.min(quarter))
    }

    pub(super) fn dense_mutex_focused_restart_candidate(
        active_vars: usize,
        active_clauses: usize,
        active_binary_clauses: usize,
    ) -> bool {
        active_vars > 0
            && active_vars < DENSE_MUTEX_FOCUSED_RESTART_MAX_ACTIVE_VARS
            && active_clauses.saturating_mul(100)
                > active_vars.saturating_mul(DENSE_MUTEX_FOCUSED_RESTART_MIN_DENSITY_TIMES_100)
            && active_binary_clauses.saturating_mul(100)
                >= active_clauses.saturating_mul(DENSE_MUTEX_FOCUSED_RESTART_MIN_BINARY_PERCENT)
    }

    /// Update target and best phases if we've reached a new maximum trail length
    ///
    /// Target phases track the assignment at the longest conflict-free trail in the
    /// current search. Best phases track the longest trail ever seen, for use in
    /// rephasing. This is called before backtracking to capture phases at the
    /// maximum trail length.
    pub(super) fn update_target_and_best_phases(&mut self) {
        let conflict_free_len = self.no_conflict_until;
        debug_assert!(
            conflict_free_len <= self.trail.len(),
            "BUG: no_conflict_until ({conflict_free_len}) > trail.len() ({})",
            self.trail.len()
        );

        // CaDiCaL target=1 semantics: `target` is an INTRA-stable-phase
        // near-miss signal, so only stable-mode trajectories may write it.
        // Focused mode deliberately diversifies polarities (see the
        // `if !self.stable_mode` cycle in preprocess_reset.rs) and must not
        // contaminate the target that pick_phase consumes stable-only
        // (preprocess_reset.rs `if self.stable_mode { target_phase[idx] }`,
        // #8466). `best` stays cross-mode (global frontier), so Best-kind
        // rephases still carry it across the focused/stable boundary.
        if self.stable_mode && conflict_free_len > self.target_trail_len {
            self.target_trail_len = conflict_free_len;
            // Equiticks progress gate (--sat-eqt-progress): stamp the conflict at
            // which the stable frontier last deepened. The switch test reads this
            // to keep a still-converging stable phase alive past the equal-effort
            // budget. Unconditional write (one field store); only READ when the
            // gate is enabled, so this is inert for the default build.
            self.cold.last_target_improve_conflicts = self.num_conflicts;
            // CaDiCaL phases.cpp:5-12: copy from saved phase, not current assignment.
            self.target_phase[..self.num_vars].copy_from_slice(&self.phase[..self.num_vars]);
        }

        if conflict_free_len > self.best_trail_len {
            self.best_trail_len = conflict_free_len;
            self.best_phase[..self.num_vars].copy_from_slice(&self.phase[..self.num_vars]);
        }
    }

    /// Compute the i-th element of the Luby sequence: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
    ///
    /// The Luby sequence is defined as:
    /// - luby(i) = 2^(k-1) if i = 2^k - 1
    /// - luby(i) = luby(i - 2^(k-1) + 1) if 2^(k-1) <= i < 2^k - 1
    ///
    /// This provides a universal restart strategy that adapts to different problem
    /// structures without knowing optimal restart intervals in advance.
    pub(super) fn get_luby(i: u32) -> u32 {
        if i == 0 {
            return 1; // Edge case, shouldn't happen with 1-indexed sequence
        }

        // Find k such that 2^k - 1 >= i
        // Start with k=1, p=1 (p = 2^k - 1)
        let mut k = 1u32;
        let mut p = 1u32;

        while p < i {
            k += 1;
            // Guard against overflow: 1u32 << 32 is undefined.
            // For k >= 32, p = u32::MAX satisfies p >= i for any u32 i.
            if k >= 32 {
                p = u32::MAX;
                break;
            }
            p = (1u32 << k) - 1;
        }

        // Now 2^(k-1) - 1 < i <= 2^k - 1
        if p == i {
            // i = 2^k - 1: return 2^(k-1)
            // k < 32 guaranteed here since p == i < u32::MAX when k < 32,
            // and p == u32::MAX when k >= 32 which only equals i if i == u32::MAX.
            if k >= 32 {
                return 1u32 << 31;
            }
            1u32 << (k - 1)
        } else {
            // i < 2^k - 1: recursively compute luby(i - (2^(k-1) - 1))
            let prev_p = if k > 32 {
                u32::MAX
            } else {
                (1u32 << (k - 1)) - 1
            };
            Self::get_luby(i - prev_p)
        }
    }

    /// Check if we should restart
    ///
    /// Uses CaDiCaL-style stabilization: alternates between focused mode (frequent
    /// Glucose restarts) and stable mode (infrequent reluctant doubling restarts).
    pub(super) fn should_restart(&mut self) -> bool {
        self.should_restart_impl::<true>()
    }

    /// Check if the pure SAT search should restart.
    ///
    /// Pure SAT never records theory-originated conflicts, so skip the
    /// theory-heavy Luby override entirely on the main CDCL route.
    pub(super) fn should_restart_pure(&mut self) -> bool {
        self.should_restart_impl::<false>()
    }

    fn should_restart_impl<const USE_THEORY_RESTARTS: bool>(&mut self) -> bool {
        self.stats.clear_pending_restart_attribution();

        // EMA sanity: values must be non-negative and not NaN (NaN from
        // division-by-zero would be invisible without this check).
        debug_assert!(
            self.cold.lbd_ema_fast >= 0.0 && !self.cold.lbd_ema_fast.is_nan(),
            "BUG: lbd_ema_fast is invalid ({})",
            self.cold.lbd_ema_fast
        );
        debug_assert!(
            self.cold.lbd_ema_slow >= 0.0 && !self.cold.lbd_ema_slow.is_nan(),
            "BUG: lbd_ema_slow is invalid ({})",
            self.cold.lbd_ema_slow
        );

        // Fast early-return guards (#8465): skip the entire stabilization mode
        // check and restart logic when we trivially know no restart is needed.
        //
        // conflicts_since_restart == 0: no conflicts since the last restart.
        // Restart decisions are meaningless without conflicts to evaluate.
        // The stabilization mode switch (tick-based) only needs to fire once
        // when the tick limit is exceeded; delaying by at most one conflict
        // cycle is harmless because mode switches happen at multi-thousand
        // tick intervals (CaDiCaL restart.cpp:27). Moving this check BEFORE
        // the stabilization logic eliminates ~200 lines of mode-switch
        // evaluation on every no-conflict CDCL iteration — the dominant case
        // since BCP propagates many literals between conflicts.
        if self.conflicts_since_restart == 0 {
            return false;
        }

        // Don't restart too early - need to build up EMA statistics.
        if self.num_conflicts < self.cold.restart_min_conflicts {
            return false;
        }

        // Check if we should switch stabilization modes.
        // IMPORTANT: This must run BEFORE the restart decision logic below.
        //
        // Kissat mode.c uses conflicts for focused-mode limits and search ticks
        // for stable-mode limits. AY keeps one limit field, so its unit depends
        // on the current mode after bootstrap:
        // - focused mode: absolute conflict limit
        // - stable mode: absolute stable search-tick limit
        //
        // The initial stabilization phase remains conflict-limited by
        // `modeinit`; large formulas may start that phase in stable mode.
        // Equiticks progress-gate window (0 = disabled; see eqt_progress_window).
        // Read here so the stable branch below stays a pure boolean expression.
        let eqt_window = self.eqt_progress_window();
        let should_switch = if self.cold.stabilize_tick_inc == 0 {
            let conflict_limit = self
                .cold
                .stable_mode_start_conflicts
                .saturating_add(self.cold.stable_phase_length);
            self.num_conflicts >= conflict_limit
        } else if self.stable_mode {
            let stable_ticks = self.search_ticks[usize::from(true)];
            if stable_ticks < self.cold.stabilize_tick_limit {
                // Equal-effort tick budget not yet spent.
                false
            } else if eqt_window > 0
                && self.cold.stable_tick_hardcap > self.cold.stabilize_tick_limit
                && stable_ticks < self.cold.stable_tick_hardcap
                && self
                    .num_conflicts
                    .saturating_sub(self.cold.last_target_improve_conflicts)
                    < eqt_window
            {
                // Equiticks progress gate (H1 fix): the equal-effort budget is
                // spent, but we are (a) still below the nlogpow4 hardcap and
                // (b) the stable frontier (`target_trail_len`) deepened within
                // the last `eqt_window` conflicts. This stable phase is still
                // CONVERGING toward a model (474e9594), so DEFER the switch
                // instead of starving it. Plateaued phases (no target progress
                // for `eqt_window` conflicts, e.g. 3ef7fa06) fall through and
                // switch at the equal-effort budget exactly as plain equiticks.
                // The hardcap bounds the deferral so it can never run unbounded,
                // and the stable EMA is never touched (avoids the prior negative
                // from AY_AB_STABLE_EMA_GATE=MAX).
                false
            } else {
                stable_ticks >= self.cold.stabilize_tick_limit
            }
        } else {
            self.num_conflicts >= self.cold.stabilize_tick_limit
        };
        // DIMACS stable-only runs must never alternate back to focused mode.
        if should_switch && self.cold.mode_lock == cold::ModeLock::None {
            // Bootstrap tick increment from first phase's tick delta.
            // CaDiCaL restart.cpp:53-54.
            if self.cold.stabilize_tick_inc == 0 {
                let delta = self.search_ticks[usize::from(self.stable_mode)];
                self.cold.stabilize_tick_inc = delta.max(1);
            }

            // Compute next phase limit for the OTHER mode. Stable phases are
            // tick-limited by work done in focused search. Focused phases are
            // conflict-limited with Kissat's nlogpow4 growth.
            let entering_stable = !self.stable_mode;
            if entering_stable {
                // Equal-ticks stable budget (2026-07 wf_0370e641 "light-preproc"
                // batch-3 root cause): Kissat mode.c `update_mode_limit` gives
                // each stable phase EXACTLY the ticks the just-ended focused
                // phase consumed (equal-effort split). AY's default path scales
                // the bootstrap-frozen tick_inc (ticks of the FIRST 1000 cheap
                // conflicts) by nlogpow4, which starves stable mode once
                // ticks/conflict grows with the learned-clause DB (measured 6%
                // stable decision share vs kissat's 64% stable clause-use).
                //
                // DEFAULT: BANDED ON for small/mid non-dense formulas —
                // active clauses <= 300K AND clause/var ratio <= 20. Measured
                // flips inside the band (serial, competition 120s):
                //   59fc779f (2,200v/9,086c, r4.1)    UNKNOWN -> SAT@47-56s x2
                //   3ef7fa06 (87,738v/256,580c, r2.9) UNKNOWN -> UNSAT@75-88s x2
                //   cbd09330 (8,713v/99,699c, r11.4)  coin-flip -> SAT@48s
                // Measured exclusions (why the band edges sit where they do):
                //   43fbacb2 (802v/48,439c, r60.4): equiticks REGRESSES it
                //     SAT@4s -> UNKNOWN (dense small formulas want the
                //     focused-heavy split) -> ratio cap 20 excludes it (1.75x
                //     headroom over cbd09330's 11.4).
                //   6f354fbe (48,032v/448,719c, r9.3): +13s (104->117s wall,
                //     3s margin) -> clause cap 300K excludes it (449K).
                // In-band floor members hold under equiticks: 70da0b78@1s,
                // 31e843c5@105s (improved from ~109s), 3f67f676@90s.
                // CLI override: `--sat-mode-equiticks true` forces ON
                // everywhere, `false` forces OFF everywhere (kill-switch).
                let equiticks = match self.cold.mode_equiticks_cached {
                    Some(v) => v,
                    None => {
                        let v = match ay_core::sat_ab_switches().mode_equiticks {
                            Some(forced) => forced,
                            // DEFAULT OFF (2026-07-16 full-400 certification):
                            // the <=300K & ratio<=20 banded default was NOT
                            // net-positive — it flipped 59fc779f/3ef7fa06/
                            // cbd09330 (+3) but REGRESSED prior in-band wins
                            // 416e33a8 (SAT@57s with =0, unknown@120s banded;
                            // kill-switch-confirmed), 602c8a20 (SAT@16.8s
                            // with =0; confirmed) and 474e9594 (presumed) —
                            // no clean band separator exists (loser ratios
                            // 2.44-9.0 interleave winner ratios 2.92-11.4).
                            // Net <= 0 with unquantified in-band tail risk =>
                            // opt-in until a full in-band A/B designs a real
                            // discriminator (the retired band was: PARSED
                            // original_ledger.num_clauses() <= 300_000 AND
                            // parsed clause/var ratio <= 20, with vars = the
                            // pre-extension count first_extension_var_index).
                            None => false,
                        };
                        self.cold.mode_equiticks_cached = Some(v);
                        v
                    }
                };
                let next_delta = if equiticks {
                    self.search_ticks[usize::from(false)]
                        .saturating_sub(self.cold.focused_ticks_at_entry)
                        .max(1)
                } else {
                    let stable_phase = self.cold.stable_phase_count + 1;
                    self.cold
                        .stabilize_tick_inc
                        .saturating_mul(rephase::nlogpow4(stable_phase))
                };
                let base_ticks = self.search_ticks[usize::from(true)];
                self.cold.stabilize_tick_limit = base_ticks.saturating_add(next_delta);
                if self.cold.stabilize_tick_limit <= base_ticks {
                    self.cold.stabilize_tick_limit = base_ticks + 1;
                }
                // Equiticks progress-gate hardcap (--sat-eqt-progress): the
                // default nlogpow4 schedule delta is the absolute ceiling a
                // deferred (still-converging) stable phase may run to. Compute
                // it only under equiticks; the non-equiticks path already uses
                // the schedule delta as its budget, so its hardcap is left 0
                // (gate branch inert). This bounds the extension so a deferred
                // phase can bridge from the equal-effort budget UP TO — but
                // never beyond — the default schedule.
                if equiticks {
                    let stable_phase = self.cold.stable_phase_count + 1;
                    let sched_delta = self
                        .cold
                        .stabilize_tick_inc
                        .saturating_mul(rephase::nlogpow4(stable_phase));
                    self.cold.stable_tick_hardcap = base_ticks
                        .saturating_add(sched_delta)
                        .max(self.cold.stabilize_tick_limit);
                } else {
                    self.cold.stable_tick_hardcap = 0;
                }
            } else {
                // Entering focused: snapshot the focused tick counter so the
                // NEXT stable phase can be budgeted with this phase's delta.
                self.cold.focused_ticks_at_entry = self.search_ticks[usize::from(false)];
                let focused_phase = self.cold.stable_phase_count.max(1);
                let next_delta = self
                    .cold
                    .stable_phase_length
                    .saturating_mul(rephase::nlogpow4(focused_phase));
                let base_conflicts = self.num_conflicts;
                self.cold.stabilize_tick_limit = base_conflicts.saturating_add(next_delta);
                if self.cold.stabilize_tick_limit <= base_conflicts {
                    self.cold.stabilize_tick_limit = base_conflicts + 1;
                }
            }

            // Switch modes.
            self.stable_mode = !self.stable_mode;
            self.cold.stable_mode_start_conflicts = self.num_conflicts;
            self.cold.mode_switch_count += 1;

            // When entering focused mode, rebuild deferred VMTF linked list
            // so focused-mode decisions have a consistent queue (#7998).
            if !self.stable_mode && self.vsids.vmtf_is_deferred() {
                self.vsids.rebuild_vmtf_from_bump_order(&self.vals);
            }

            self.sync_active_branch_heuristic();
            if matches!(self.cold.branch_selector_mode, BranchSelectorMode::MabUcb1) {
                // MAB rewards are stable-mode only, so never let a scored
                // epoch span a focused/stable mode boundary.
                self.start_branch_heuristic_epoch();
            }

            // Swap LBD EMA averages including bias correction state (CaDiCaL swap_averages).
            if self.cold.ema_swapped {
                std::mem::swap(
                    &mut self.cold.lbd_ema_fast,
                    &mut self.cold.saved_lbd_ema_fast,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_slow,
                    &mut self.cold.saved_lbd_ema_slow,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_fast_biased,
                    &mut self.cold.saved_lbd_ema_fast_biased,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_slow_biased,
                    &mut self.cold.saved_lbd_ema_slow_biased,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_fast_exp,
                    &mut self.cold.saved_lbd_ema_fast_exp,
                );
                std::mem::swap(
                    &mut self.cold.lbd_ema_slow_exp,
                    &mut self.cold.saved_lbd_ema_slow_exp,
                );
            } else {
                self.cold.saved_lbd_ema_fast = self.cold.lbd_ema_fast;
                self.cold.saved_lbd_ema_slow = self.cold.lbd_ema_slow;
                self.cold.saved_lbd_ema_fast_biased = self.cold.lbd_ema_fast_biased;
                self.cold.saved_lbd_ema_slow_biased = self.cold.lbd_ema_slow_biased;
                self.cold.saved_lbd_ema_fast_exp = self.cold.lbd_ema_fast_exp;
                self.cold.saved_lbd_ema_slow_exp = self.cold.lbd_ema_slow_exp;
                self.cold.lbd_ema_fast = 0.0;
                self.cold.lbd_ema_slow = 0.0;
                self.cold.lbd_ema_fast_biased = 0.0;
                self.cold.lbd_ema_slow_biased = 0.0;
                self.cold.lbd_ema_fast_exp = 1.0;
                self.cold.lbd_ema_slow_exp = 1.0;
                self.cold.ema_swapped = true;
            }

            if self.stable_mode {
                // Entering stable mode -- reset reluctant doubling state.
                self.cold.stable_phase_count += 1;
                self.cold.reluctant_u = 1;
                self.cold.reluctant_v = 1;
                self.cold.reluctant_countdown = RELUCTANT_INIT;
                self.cold.reluctant_ticked_at = self.num_conflicts;
                // Reset the target high-water mark so each stable phase
                // rediscovers its own near-satisfying frontier from scratch
                // (mirrors the per-rephase reset in rephase.rs). A stale
                // inflated target_trail_len carried over from a prior phase
                // would otherwise lock this stable phase out of ever updating
                // its target, defeating target phasing on deep structured
                // instances.
                self.target_trail_len = 0;
                // Equiticks progress gate: a fresh stable phase counts as
                // "just improved" so it is not immediately treated as plateaued
                // before its first target update (which lands within a few
                // conflicts). Inert unless the gate is enabled.
                self.cold.last_target_improve_conflicts = self.num_conflicts;
            }

            // Emit diagnostic event for mode switch (#4674).
            self.emit_diagnostic_mode_switch(self.stable_mode, self.cold.stabilize_tick_limit);

            // Start a random decision burst after every mode switch (Kissat mode.c:214).
            // Diversifies the search space at mode boundaries.
            self.start_random_sequence();
        }

        // --- Restart decision logic (guards already checked at function entry). ---

        // Geometric restart schedule: next_restart = initial * factor^n.
        // Z3 uses this for QF_LRA (RS_GEOMETRIC with restart_adaptive=false).
        // Bypasses stabilization and glucose/Luby logic entirely.
        if self.cold.geometric_restarts {
            let restart_exponent = self.cold.restarts.min(i32::MAX as u64) as i32;
            let threshold =
                self.cold.geometric_initial * self.cold.geometric_factor.powi(restart_exponent);
            // Clamp to u64::MAX to prevent overflow; at that point restarts are
            // effectively disabled which is fine for extremely long runs.
            let threshold_u64 = if threshold >= u64::MAX as f64 {
                u64::MAX
            } else {
                threshold as u64
            };
            let fires = self.conflicts_since_restart >= threshold_u64;
            if fires {
                self.stats.set_pending_restart_attribution(
                    RestartAttribution::Geometric,
                    self.stable_mode,
                );
            }
            return fires;
        }

        // #8452: Theory-aware Luby restart policy.
        // When >80% of conflicts originate from the theory/extension solver,
        // the Glucose EMA restart strategy is counterproductive: it restarts
        // every ~3-7 conflicts, throwing away theory-guided search progress.
        // Switch to Luby restarts with a longer base interval (128 conflicts),
        // giving the theory solver time to propagate LP-derived bounds and
        // guide the search toward a satisfying assignment.
        //
        // This is the single most impactful change for QF_LRA performance:
        // on sc-6.induction3, Z3 solves in 0.01s with 69 conflicts / 597
        // decisions. Without this, AY makes 15460 decisions and times out.
        if USE_THEORY_RESTARTS
            && self.cold.theory_conflict_ratio > THEORY_CONFLICT_RATIO_THRESHOLD
            && self.cold.ext_conflict_count > 20
        {
            // Use Luby restarts with a dedicated theory Luby index.
            // The global luby_idx is shared with Glucose/focused-mode restarts
            // and can be very large (50+) by the time theory mode activates,
            // producing enormous Luby values (16, 32, ...) that make
            // THEORY_LUBY_BASE * Luby(luby_idx) >> 1000 and effectively
            // disable restarts. The dedicated index starts at 1 and only
            // advances on theory restarts, keeping intervals reasonable.
            let threshold = THEORY_LUBY_BASE * u64::from(Self::get_luby(self.cold.theory_luby_idx));
            let fires = self.conflicts_since_restart >= threshold;
            if fires {
                self.stats.set_pending_restart_attribution(
                    RestartAttribution::TheoryLuby,
                    self.stable_mode,
                );
            }
            return fires;
        }

        if self.stable_mode {
            // Stable mode: Knuth's reluctant doubling (Luby sequence x period).
            //
            // CaDiCaL restart.cpp:99-100: in stable mode, `restarting()` returns
            // ONLY the reluctant boolean, without the Glucose EMA check.
            //
            // AY adds a gated Glucose EMA check for medium/large formulas (#8448):
            // On small dense binary formulas (clique_n2_k10: 180 vars, 99.7%
            // binary), the EMA fires every ~2 conflicts, producing 110K restarts
            // in 1.15M conflicts and preventing stable-mode deep searches (#8135).
            // But on medium/large crafted SAT instances (ecarev-110: 4099 vars),
            // reluctant doubling alone lets stable mode run too deep without
            // quality gating, causing timeouts on benchmarks that previously
            // solved quickly (1.2s → timeout). The fix: gate the stable-mode EMA
            // behind a minimum conflict count (STABLE_EMA_MIN_CONFLICTS=50) that
            // prevents the pathological high-frequency firing on small dense
            // formulas while still providing quality-based restart triggering on
            // larger instances where reluctant doubling intervals become too long.
            let new_conflicts = self.num_conflicts - self.cold.reluctant_ticked_at;
            self.cold.reluctant_ticked_at = self.num_conflicts;
            self.cold.reluctant_countdown =
                self.cold.reluctant_countdown.saturating_sub(new_conflicts);
            let reluctant_fires = self.cold.reluctant_countdown == 0;
            if reluctant_fires {
                // Advance Knuth's (u, v) state: produces Luby sequence values
                if (self.cold.reluctant_u & self.cold.reluctant_u.wrapping_neg())
                    == self.cold.reluctant_v
                {
                    self.cold.reluctant_u += 1;
                    self.cold.reluctant_v = 1;
                } else {
                    self.cold.reluctant_v *= 2;
                }
                // Cap v to prevent unbounded interval growth (CaDiCaL reluctantmax)
                if self.cold.reluctant_v >= RELUCTANT_MAX {
                    self.cold.reluctant_u = 1;
                    self.cold.reluctant_v = 1;
                }
                self.cold.reluctant_countdown = self.cold.reluctant_v * RELUCTANT_INIT;
                self.stats.stable_reluctant_fires += 1;
            }

            // Glucose EMA check for stable mode (wider margin than focused).
            // Gated by stable_ema_gate (default STABLE_EMA_MIN_CONFLICTS=50)
            // to prevent pathological high-frequency firing on small dense
            // formulas (#8135, #8448). On small dense UNSAT formulas
            // (clique_n2_k10: 180 vars, density 17.5), stable_ema_gate is
            // set to u64::MAX to disable EMA entirely, relying on pure
            // reluctant doubling (matching CaDiCaL's stable-mode behavior).
            // This reduces restarts from 93K to ~14K (#8466).
            let ema_fires = if self.cold.glucose_restarts
                && self.conflicts_since_restart >= self.cold.stable_ema_gate
            {
                let margin = RESTART_MARGIN_STABLE;
                self.cold.lbd_ema_fast > margin * self.cold.lbd_ema_slow
            } else {
                false
            };

            if ema_fires {
                self.stats.stable_ema_fires += 1;
            }

            let fires = reluctant_fires || ema_fires;
            if fires {
                let cause = if reluctant_fires {
                    RestartAttribution::StableReluctant
                } else {
                    RestartAttribution::StableEma
                };
                self.stats
                    .set_pending_restart_attribution(cause, self.stable_mode);
            }
            fires
        } else if self.cold.glucose_restarts {
            // Glucose-style EMA restarts (focused mode only — stable mode uses
            // reluctant doubling above). CaDiCaL restart.cpp:104.
            // A/B #1: focused margin defaults to RESTART_MARGIN_FOCUSED (1.10,
            // the calibrated value — lowering it was instance-dependent, see
            // constants.rs). AY_AB_FOCUSED_MARGIN overrides it for A/B sweeps.
            let margin = ab_focused_margin();
            self.stats.focused_ema_checks += 1;
            let ema_condition = self.cold.lbd_ema_fast > margin * self.cold.lbd_ema_slow;
            // CaDiCaL restart.cpp:101: `stats.conflicts <= lim.restart` with
            // `lim.restart = stats.conflicts + restartint` (restartint=2). The `<=`
            // gate means CaDiCaL needs strictly MORE than restartint conflicts past
            // the last restart, i.e., > 2 = at least 3 conflicts. AY previously used
            // `>= 2` which allowed restart after only 2 conflicts — 33% more frequent.
            let conflict_gate = self.conflicts_since_restart > self.cold.focused_restart_gate;
            if ema_condition && !conflict_gate {
                self.stats.focused_ema_blocked_by_conflict_gate += 1;
            }
            let fires = conflict_gate && ema_condition;
            if fires {
                self.stats.focused_ema_fires += 1;
            }
            if fires {
                self.stats.set_pending_restart_attribution(
                    RestartAttribution::FocusedEma,
                    self.stable_mode,
                );
            }
            fires
        } else {
            // Luby restarts as fallback (focused mode)
            let threshold = self.cold.restart_base * u64::from(Self::get_luby(self.cold.luby_idx));
            let fires = self.conflicts_since_restart >= threshold;
            if fires {
                self.stats.set_pending_restart_attribution(
                    RestartAttribution::FocusedLuby,
                    self.stable_mode,
                );
            }
            fires
        }
    }

    /// Update LBD exponential moving averages after learning a clause.
    ///
    /// Uses ADAM-style bias correction (Kingma & Ba, ICLR 2015) matching
    /// CaDiCaL's `ema.cpp`. Without correction, the slow EMA starts near 0
    /// and takes ~100K conflicts to converge, causing the fast/slow ratio
    /// to be artificially high and triggering restarts every 2-3 conflicts.
    /// Correction: `value = biased / (1 - beta^n)` compensates for the
    /// zero-initialized bias.
    /// Update theory conflict ratio EMA (#8452).
    ///
    /// Called on every conflict. `is_theory` is true when the conflict
    /// originated from the theory/extension solver.
    pub(super) fn update_theory_conflict_ratio(&mut self, is_theory: bool) {
        let alpha = 1.0 - THEORY_RATIO_EMA_DECAY;
        let sample = if is_theory { 1.0 } else { 0.0 };
        self.cold.theory_conflict_ratio += alpha * (sample - self.cold.theory_conflict_ratio);
    }

    pub(super) fn update_lbd_ema(&mut self, lbd: u32) {
        self.stats.lbd_sum += u64::from(lbd);
        self.stats.lbd_count += 1;
        self.stats.record_lbd_bucket(lbd);
        let y = f64::from(lbd);
        let alpha_fast = 1.0 - EMA_FAST_DECAY;
        let alpha_slow = 1.0 - EMA_SLOW_DECAY;

        // Update biased fast EMA
        self.cold.lbd_ema_fast_biased += alpha_fast * (y - self.cold.lbd_ema_fast_biased);
        // Update bias correction exponent: exp *= beta
        self.cold.lbd_ema_fast_exp *= EMA_FAST_DECAY;
        // Corrected value: biased / (1 - beta^n)
        let denom_fast = 1.0 - self.cold.lbd_ema_fast_exp;
        self.cold.lbd_ema_fast = if denom_fast > 0.0 {
            self.cold.lbd_ema_fast_biased / denom_fast
        } else {
            self.cold.lbd_ema_fast_biased
        };

        // Update biased slow EMA
        self.cold.lbd_ema_slow_biased += alpha_slow * (y - self.cold.lbd_ema_slow_biased);
        // Update bias correction exponent
        self.cold.lbd_ema_slow_exp *= EMA_SLOW_DECAY;
        let denom_slow = 1.0 - self.cold.lbd_ema_slow_exp;
        self.cold.lbd_ema_slow = if denom_slow > 0.0 {
            self.cold.lbd_ema_slow_biased / denom_slow
        } else {
            self.cold.lbd_ema_slow_biased
        };
    }
    /// Compute the level to backtrack to when restarting, reusing trail decisions
    ///
    /// CaDiCaL's trail reuse optimization: instead of backtracking to level 0,
    /// keep decisions that would be made again anyway (those with higher VSIDS
    /// activity than the next decision variable).
    ///
    /// This saves re-making the same decisions after restart, which is especially
    /// valuable when VSIDS has stabilized.
    pub(super) fn compute_reuse_trail_level(&mut self) -> u32 {
        if self.decision_level == 0 {
            return 0;
        }

        // Find what the next decision variable would be, matching the current mode:
        // - Stable mode: VSIDS heap
        // - Focused mode: VMTF queue
        let Some(next_decision) = self.pick_next_decision_variable() else {
            return self.decision_level; // All assigned, keep everything
        };

        // Find the lowest level where we can reuse the trail
        let mut reuse_level = 0u32;

        for level in 1..=self.decision_level {
            let decision_idx = self.trail_lim[level as usize - 1];
            let decision_lit = self.trail[decision_idx];
            let decision_var = decision_lit.variable();

            if self.branch_priority_is_lower(
                decision_var,
                next_decision,
                self.active_branch_heuristic,
            ) {
                break;
            }
            reuse_level = level;
        }

        // Postcondition: reuse_level must not exceed current decision_level.
        debug_assert!(
            reuse_level <= self.decision_level,
            "BUG: reuse_level ({reuse_level}) > decision_level ({})",
            self.decision_level
        );
        reuse_level
    }

    /// Restart with trail reuse: keep decisions with higher VSIDS activity.
    ///
    /// AE-Kissat-MAB `restart.c:178-208`: MAB epoch completion runs BEFORE trail
    /// reuse computation. If the heuristic arm switched, trail reuse is disabled
    /// (level 0) because the old trail was ordered by a different scoring function.
    pub(super) fn do_restart(&mut self) {
        self.do_restart_impl::<true>();
    }

    /// Restart from the pure SAT main loop.
    ///
    /// This follows the same restart mechanics as theory/extension mode, but
    /// does not consult or mutate theory-heavy restart policy state.
    pub(super) fn do_restart_pure(&mut self) {
        self.do_restart_impl::<false>();
    }

    fn do_restart_impl<const USE_THEORY_RESTARTS: bool>(&mut self) {
        self.trace_restart();
        self.emit_diagnostic_restart();

        // Approximate-BCP filter Phase 2 (#8789): feature-gated pure
        // observer sampled once per restart. The prefilter scans every
        // active clause (O(clauses)), so the restart boundary — not the
        // BCP inner loop — is the highest-frequency spot where the
        // measurement cost is tolerable, while still sampling a diverse
        // set of trail states across the solve. Updates only the
        // `approx_bcp_*` SolverStats counters; a nonzero
        // `approx_bcp_mismatch_detected` indicates a filter soundness bug
        // (2026-07-14 triage: this call was missing entirely, so the
        // Phase-2 observer had never produced data).
        #[cfg(feature = "approx-bcp-filter")]
        {
            let _ = self.run_approx_bcp_prefilter();
        }

        // Complete MAB epoch FIRST; may switch heuristic arm.
        // AE-Kissat-MAB restart.c:188-189.
        let arm_switched = self.complete_branch_heuristic_epoch_if_needed();

        // Trail reuse: skip if arm switched (AE-Kissat-MAB restart.c:192).
        // When the heuristic changes, the decision ordering is different and
        // the old trail decisions are no longer guaranteed to be top-priority.
        let reuse_level = if arm_switched {
            0
        } else {
            self.compute_reuse_trail_level()
        };
        self.backtrack(reuse_level);

        // Stale watch entries from lazy clause deletion are handled by:
        // 1. BCP inline compaction (propagation.rs:357-364) — on-demand
        // 2. flush_watches() before inprocessing (config.rs:144) — batch
        // CaDiCaL never flushes at restart. Removing the per-restart
        // O(total_watches) sweep eliminates ~21% overhead on crn_11_99.
        self.conflicts_since_restart = 0;
        self.cold.luby_idx += 1;
        self.cold.restarts += 1;

        // Kissat-style focused-mode restart limit growth (#8655).
        // Kissat restart.c:39-51: `kissat_update_focused_restart_limit`:
        //   delta = restartint + logn(restarts) - 1
        // where logn(n) = log10(n + 9).
        //
        // After many restarts, the minimum conflict gap between restarts
        // grows logarithmically. At 1000 restarts: gate = 2 + log10(1009) - 1 ~= 4.
        // At 100K restarts: gate = 2 + 5 - 1 = 6.
        //
        // This prevents restart storms on large structured BMC formulas
        // where focused mode may still execute (e.g., during mode alternation
        // for formulas between 100K-500K clauses). Without this growth, the
        // fixed gate of 2 allows restarts every 3 conflicts indefinitely.
        //
        // Only update when in focused mode — stable mode uses reluctant
        // doubling which has its own growth mechanism.
        if !self.stable_mode {
            let restarts = self.cold.restarts;
            if restarts > 0 {
                let logn = ((restarts + 9) as f64).log10();
                // Kissat: delta = restartint + logn(restarts) - 1
                // restartint = RESTART_INTERVAL = 2
                let delta = RESTART_INTERVAL as f64 + logn - 1.0;
                self.cold.focused_restart_gate = self
                    .cold
                    .focused_restart_gate
                    .max(delta.max(RESTART_INTERVAL as f64) as u64);
            }
        }

        // Advance theory Luby index when in theory-heavy mode (#8452).
        // Only increment when the restart was triggered by the theory
        // restart policy. When theory ratio drops back below threshold,
        // reset the index so the next theory mode entry starts fresh.
        if USE_THEORY_RESTARTS
            && self.cold.theory_conflict_ratio > THEORY_CONFLICT_RATIO_THRESHOLD
            && self.cold.ext_conflict_count > 20
        {
            self.cold.theory_luby_idx += 1;
        } else if USE_THEORY_RESTARTS && self.cold.theory_luby_idx > 1 {
            // Exiting theory mode: reset for next entry.
            self.cold.theory_luby_idx = 1;
        }

        // Domain-epoch hardness accounting: a bucket-mode query that keeps
        // restarting graduates to exact heap selection (#8476).
        self.bucket_queue_on_restart();

        // Notify programmatic observer of restart (#8155).
        self.notify_observer_restart();
        // CaDiCaL resets target_assigned only during rephase (rephase.cpp:373-374),
        // NOT on every restart. Resetting here was added for #7003 (6g_6color
        // timeout) but destroys target phase coherence on hard combinatorial
        // instances requiring stable search guidance (FmlaEquivChain, clique).
        // Rephase timing now matches CaDiCaL (arithmetic-increase spacing),
        // so the original workaround is no longer needed.

        // Postcondition: conflicts_since_restart must be 0 after restart.
        debug_assert_eq!(
            self.conflicts_since_restart, 0,
            "BUG: conflicts_since_restart not reset after restart"
        );
    }

    /// Restart-side accounting for the bucket-queue decision mode (#8476).
    ///
    /// Domain-restricted queries start on the O(1) bucket queue, a
    /// bounded-effort approximation of activity order that wins on the short
    /// queries domain mode targets. Every restart taken while the bucket
    /// path is live is cheap evidence that this query is not one of those:
    /// once `BUCKET_QUEUE_RESTART_THRESHOLD` such restarts accumulate within
    /// the current domain epoch, selection is handed to the exact EVSIDS
    /// heap for the remainder of the epoch.
    ///
    /// Called from every restart flavor (`do_restart_impl` for the full and
    /// pure paths, `do_partial_restart` for the assumption path) so that all
    /// restart events feed the same hardness signal. Inert whenever the
    /// bucket path is inactive: restarts of non-domain queries, or of an
    /// epoch that already handed off, neither count nor trigger anything.
    /// Re-activation and counter reset belong to `set_domain`
    /// (`incremental.rs`), never to this site.
    pub(super) fn bucket_queue_on_restart(&mut self) {
        if !self.bucket_queue_active {
            return;
        }
        self.domain_restarts += 1;
        if self.domain_restarts >= BUCKET_QUEUE_RESTART_THRESHOLD {
            self.migrate_to_heap();
        }
    }

    /// Hand decision selection for the current domain epoch from the bucket
    /// queue to the exact EVSIDS heap.
    ///
    /// Obligation at handoff: every currently-unassigned variable of the
    /// caller's decision domain must be reachable through the heap, which is
    /// the active selection structure from this point until the next
    /// `set_domain`. The whole domain is offered to the heap:
    /// `insert_into_heap` is idempotent and skips variables it already
    /// tracks, and variables assigned right now may stay absent — the
    /// ordinary backtrack contract re-heaps them on unassignment once the
    /// bucket flag is off. Residual bucket entries are dropped so the
    /// structure starts clean at the next epoch.
    ///
    /// Purely a selection-structure change: activities, saved phases, the
    /// trail, decision levels, and the clause database are untouched, so
    /// the heap resumes exact ordering over the activities as they stand.
    fn migrate_to_heap(&mut self) {
        // Flag first: from here on, backtracking stops feeding the bucket
        // (backtrack.rs guards on this) and the decision loop takes the
        // heap route in pick_domain_restricted_decision.
        self.bucket_queue_active = false;

        // decision_domain is what the heap-route decision loop filters by;
        // active_domain (its BCP-expanded superset) is the fallback for
        // callers that never populated the original-domain mask. Extra
        // unassigned variables from the superset are harmless: the decision
        // loop filters them out and reinserts them.
        let domain = self
            .decision_domain
            .as_deref()
            .or(self.active_domain.as_deref());
        if let Some(domain) = domain {
            for var_idx in (0..domain.len()).filter(|&i| domain[i]) {
                if self.var_is_assigned(var_idx) || self.var_lifecycle.is_removed(var_idx) {
                    continue;
                }
                self.vsids.insert_into_heap(Variable::new(var_idx as u32));
            }
        }

        self.vsids.bucket_queue_clear();
    }
}
