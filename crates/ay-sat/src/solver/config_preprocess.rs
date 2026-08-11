// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Initial preprocessing pipeline split from `config.rs` for file-size compliance (#5142).

use super::config_preprocess_cleanup::{PreprocessOutcome, PreprocessStageControl};
use super::config_preprocess_policy::{factor_dense_enabled, PreprocessPolicy};
use super::*;

impl Solver {
    /// Run initial preprocessing to reduce the search space
    ///
    /// Quick-path pipeline (matches CaDiCaL internal.cpp:742-792) with an
    /// early symmetry pass inserted before destructive rewrites:
    ///   symmetry → congruence → backbone → sweep → decompose → factor → fastelim (BVE)
    /// Heavy passes (HTR, probing, conditioning, subsumption) are deferred to
    /// inprocessing where they fire in the first round at ~2K conflicts.
    ///
    /// Returns true if UNSAT was detected during preprocessing.
    pub(super) fn preprocess(&mut self) -> bool {
        matches!(
            self.preprocess_interruptible(&|| false),
            PreprocessOutcome::Unsat
        )
    }

    pub(super) fn preprocess_inner<F>(&mut self, should_stop: &F) -> bool
    where
        F: Fn() -> bool + ?Sized,
    {
        // #8477: Runtime disable flags for bisecting preprocessing soundness bugs.
        // These permanently disable techniques for BOTH preprocessing and inprocessing.
        // Must be processed BEFORE the no_preprocess early return so that
        // inprocessing also respects these flags.
        // #8506: Reads cached OnceLock instead of per-call std::env::var() syscalls.
        let sat_flags = ay_core::sat_disable_flags();
        if sat_flags.no_bve {
            self.inproc_ctrl.bve.enabled = false;
        }
        if sat_flags.no_probe {
            self.inproc_ctrl.probe.enabled = false;
        }
        if sat_flags.no_congruence {
            self.inproc_ctrl.congruence.enabled = false;
        }
        if sat_flags.no_decompose {
            self.inproc_ctrl.decompose.enabled = false;
        }
        if sat_flags.no_sweep {
            self.inproc_ctrl.sweep.enabled = false;
        }
        if sat_flags.no_subsume {
            self.inproc_ctrl.subsume.enabled = false;
        }
        if sat_flags.no_vivify {
            self.inproc_ctrl.vivify.enabled = false;
        }
        if sat_flags.no_factor {
            self.inproc_ctrl.factor.enabled = false;
        }
        if sat_flags.no_bce {
            self.inproc_ctrl.bce.enabled = false;
        }
        if sat_flags.no_transred {
            self.inproc_ctrl.transred.enabled = false;
        }
        if sat_flags.no_preprocess {
            return false;
        }
        // Early exits do not reach the normal tail that computes watch
        // validity. Fail safe by requiring callers to rebuild unless the inner
        // pipeline completes and overwrites this field.
        self.cold.preprocess_watches_valid = false;
        let _preprocess_start = ay_core::time::Instant::now();
        let preprocess_budget_secs =
            PreprocessPolicy::budget_secs_for_counts(self.num_vars, self.arena.num_clauses());
        // DEEP sparse-band lever (kill-switched, default ON since 2026-07-10
        // wf_55735963): raise the whole
        // preprocess budget so `preprocess_timed_out()` does not truncate the
        // deep BVE pass. Scoped to num_vars>150K formulas where the shared
        // expensive passes are already skipped, so this extra budget is spent
        // effectively only on BVE. No-op when the deep knob is off.
        // Proof-aware (wf_0c7d84e9): scaled by bve_wall_budget_scale() (4x
        // under DRAT emission, 1x otherwise) so proof step-tracking overhead
        // does not starve the pass — see PROOF_WALL_BUDGET_SCALE.
        let preprocess_budget_secs = if self.bve_sparse_deep_active() {
            preprocess_budget_secs
                .max(BVE_SPARSE_DEEP_PREPROCESS_BUDGET_SECS * self.bve_wall_budget_scale())
        } else {
            preprocess_budget_secs
        };
        // Giant-band AUTO budget (giant-3M loss fix, 2026-07 — see
        // AUTO_GIANT_PREPROCESS_BUDGET_SECS): the 2s Large budget is
        // consumed by the full level-0 GC alone at 8.5M clauses, so the
        // in-band AUTO probe entry was a load-dependent coin flip. Raised
        // to 12s ONLY for AUTO-armed non-proof giants inside the raised
        // 4M/10M band that the dense disarm will not disarm (5ceb95f5
        // run-6 preprocess_ms=10,833 -> SAT@62.0s). No proof-wall scaling:
        // the band is non-proof by construction.
        let preprocess_budget_secs = if self.auto_giant_preprocess_budget_active() {
            preprocess_budget_secs.max(AUTO_GIANT_PREPROCESS_BUDGET_SECS)
        } else {
            preprocess_budget_secs
        };
        self.cold.preprocess_deadline =
            Some(_preprocess_start + std::time::Duration::from_secs(preprocess_budget_secs));

        // Must be at level 0 for preprocessing
        if self.decision_level != 0 {
            return false;
        }

        // NOTE: Preprocessing is NOT blanket-disabled in proof mode. All
        // enabled techniques emit valid DRAT records. Factorization now uses
        // the same DRAT transaction path as inprocessing and performs its own
        // LRAT-only runtime guard inside `factorize()`.
        //
        // CaDiCaL runs all preprocessing with proof logging enabled.

        // Invalidate JIT-compiled formulas before preprocessing (#8359).
        // Preprocessing deletes and modifies clauses, which invalidates the
        // arena offsets embedded in compiled JIT code. Without this, the JIT
        // propagation path (propagate_hybrid → batch_enqueue_from_jit) uses
        // stale clause references from deleted clauses, causing
        // assignment_level() to read empty literal slices → level-0
        // assignments with dead reasons → "stale reason ClauseRef" panic
        // during backtrack. All BV tests fail because bv_compiled_formula
        // is set before solve() which runs preprocessing.

        // Clause deletions are lazy: stale watch entries are compacted in a
        // single linear pass before running level-0 inprocessing.
        let _t_flush0 = ay_core::time::Instant::now();
        self.flush_watches();
        let _t_flush_done = _t_flush0.elapsed();

        let policy = self.compute_preprocess_policy();
        let skip_gate_dependent_passes = policy.skip_gate_dependent_passes;
        let skip_expensive_preprocessing_passes = policy.skip_expensive_preprocessing_passes;
        let skip_dense_formula = policy.skip_dense_formula;
        let skip_congruence = policy.skip_congruence;
        let preprocessing_quick_mode = policy.preprocessing_quick_mode;
        let formula_density = policy.formula_density;

        // Permanently disable techniques that are counterproductive on random
        // k-SAT (#3814). The `enabled` flag persists across inprocessing rounds
        // in the main CDCL loop, so we don't need separate inprocessing guards.
        //
        // - HTR: produces resolvents from uniform ternary clauses that bloat
        //   the clause DB without useful structure.
        // - Conditioning: removes clauses whose absence is equisatisfiable, but
        //   on uniform formulas this disrupts CDCL search heuristics.
        if skip_gate_dependent_passes {
            self.inproc_ctrl.htr.enabled = false;
            self.inproc_ctrl.condition.enabled = false;
        }

        // Proof modes require disabling incompatible techniques (#4397, #4557).
        // The allow/deny policy lives in proof_capability.rs.
        if self.proof_manager.is_some() || self.cold.lrat_enabled {
            let ctrl = self.inproc_ctrl.clone();
            self.inproc_ctrl = ctrl.with_proof_overrides(self.cold.lrat_enabled);
        }

        // Run 1 full preprocessing round. CaDiCaL defaults to 0 full rounds
        // (fastelim only), with 1 round in SAT-COMP configuration (-P1).
        // 3 rounds caused preprocessing to hang on large instances (#6926):
        // all per-technique limits fire 3x, and the fixed-point exit only
        // triggers when zero variables are eliminated (rare on large formulas).
        // Inprocessing re-fires techniques after search progress, so 1 round
        // is sufficient. Ref: CaDiCaL internal.cpp:795-811.
        // Track whether watches are valid after preprocessing. When no
        // clause-modifying pass runs (dense formula skip), or when BVE
        // rebuilds watches and no subsequent pass modifies clause literals
        // in-place, the post-preprocessing watch rebuild in
        // solve_no_assumptions can be skipped. On large instances (4.7M clauses),
        // this avoids a redundant O(clauses) pass that costs ~6 seconds.
        //
        // Start as true: watches from init_solve() are valid. Set to false
        // only when a pass actually invalidates watch structure.
        let mut watches_valid = true;
        let mut bve_rebuilt_watches = false;
        let mut _t1_cong: u128 = 0;
        let mut _t2_bb: u128 = 0;
        let mut _t3_decomp: u128 = 0;
        let mut _t4_factor: u128 = 0;
        let mut _t5_bve: u128 = 0;
        let mut _t6_probe: u128 = 0;

        for _round in 0..1 {
            // Check interrupt at the start of each preprocessing round (#3638).
            //
            // Poll the process memory limit here too. `poll_process_memory_limit`
            // is gated on a CONFLICT cadence and its call sites are the CDCL loop
            // tops, propagation, and IC3 — so nothing enforces the limit during
            // preprocessing, which is exactly where unbounded growth happens.
            // Measured on the SAT-COMP 2026 set: `--memory 6000` was ignored
            // entirely while `post-cbmc-aes-ee-r2` (a 33 MB file) grew steadily
            // past 12 GB, and `lightsout_sat_23` (180 KB) reached 71.7 GB. Same
            // shape as the large-workload / compiler_consumer 300 GB incident that motivated
            // `poll_process_memory_limit_now` for the zero-conflict spin.
            self.poll_process_memory_limit_now();
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }

            // Level-0 garbage collection at the start of each round ensures
            // all techniques operate on clean clauses (no stale false literals).
            // On large formulas (>200K vars) with few fixed variables (<50%),
            // use lightweight GC that only checks for all-false clauses.
            // Full GC on 1M+ clause formulas costs 12s+ due to per-clause
            // watch manipulation. When many variables are fixed (>50%), full
            // GC is needed: clause shortening triggers unit propagation
            // cascades that are essential for UNSAT detection.
            let _t_gc0 = ay_core::time::Instant::now();
            let fixed_ratio = if self.num_vars > 0 {
                self.count_fixed_vars() as f64 / self.num_vars as f64
            } else {
                0.0
            };
            // Huge-arena batch deferral (#l0-gc-batch): the full GC's fixpoint
            // pass rebuilds gc_occ by scanning the ENTIRE arena — on a
            // million-clause incremental MaxSAT part (protein: 2.5M binary
            // hards) that O(arena) rebuild ran on nearly every solve, because
            // OLL hardens a few units between solves and the >=50%-fixed route
            // selects the full pass (measured ~40% of total runtime: memmove +
            // ArenaIter + OccList::add_clause all under collect_level0_garbage).
            // Full GC is DB hygiene, not soundness: the lightweight variant
            // already performs the UNSAT-essential all-false check. So on huge
            // arenas, batch the hygiene: run the full pass only once enough new
            // level-0 units accumulate to amortize the scan. When it does run,
            // its affected-set walks the trail from position 0, so it catches
            // up on the entire deferred window at once.
            const L0_GC_BATCH_MIN_ARENA_WORDS: usize = 4_000_000;
            const L0_GC_BATCH_MIN_NEW_FIXED: i64 = 128;
            // Layout-invariant accounting units (legacy 5-word headers, see
            // `accounting_len`) so the R2 header slimming does not shift this
            // threshold crossing and thereby the GC route / search trajectory.
            let defer_full = self.arena.accounting_len() > L0_GC_BATCH_MIN_ARENA_WORDS
                && self
                    .fixed_count
                    .saturating_sub(self.cold.last_full_l0_gc_fixed)
                    < L0_GC_BATCH_MIN_NEW_FIXED;
            if (skip_congruence && fixed_ratio < 0.50) || defer_full {
                if self.collect_level0_garbage_lightweight() {
                    return true;
                }
            } else {
                let full_ran = self.fixed_count != self.cold.last_collect_fixed;
                if self.collect_level0_garbage() {
                    return true;
                }
                if full_ran {
                    self.cold.last_full_l0_gc_fixed = self.fixed_count;
                }
            }
            let _t_gc_done = _t_gc0.elapsed();
            let _t_bcp0 = ay_core::time::Instant::now();
            if self.propagate_check_unsat() {
                return true;
            }
            let _t_bcp_done = _t_bcp0.elapsed();

            let (symmetry_unsat, symmetry_changed) =
                self.preprocess_symmetry_interruptible(should_stop);
            if symmetry_unsat {
                return true;
            }
            if symmetry_changed && self.propagate_check_unsat() {
                return true;
            }

            let vars_before = self.num_vars - self.count_fixed_vars();

            let _t0 = _preprocess_start;

            // 1. Congruence closure must run before decompose so Tarjan SCC can
            //    consume new equivalence binaries; skipping decompose here can
            //    break reconstruction when BVE later eliminates those variables (#5752).
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            // Route-aware collapse probe (#15, AY_AB_SUBST_AUTO — default ON
            // since 2026-07-10, wf_55735963): the FIRST congruence round
            // doubles as a cheap substitution-heaviness probe. Its
            // equivalence density (equivalences / active vars) separates
            // substitution-heavy industrial (70da r1 ≈ 0.30) from general
            // (≈ 0) cleanly, so the expensive decompose + fixpoint only run
            // when the probe says it will pay off — avoiding the measured
            // general regression (8→7) from unconditional collapse. The flag
            // is armed by VariantConfig::apply_to_solver for the Default
            // DIMACS variant only (kill-switch AY_AB_SUBST_AUTO=0), so Custom
            // congruence profiles keep their historical unconditional path.
            let auto_collapse = self.cold.subst_auto_collapse;
            let mut collapse_worthy = !auto_collapse;
            let _t_cong_start = ay_core::time::Instant::now();
            if self.inproc_ctrl.gate.enabled
                && self.inproc_ctrl.congruence.enabled
                && self.inproc_ctrl.decompose.enabled
                && !skip_gate_dependent_passes
                && !skip_congruence
            {
                let equivs_before = self.inproc.congruence.stats().equivalences_found;
                self.set_diagnostic_pass(DiagnosticPass::Congruence);
                self.congruence();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
                if auto_collapse {
                    let equivs = self
                        .inproc
                        .congruence
                        .stats()
                        .equivalences_found
                        .saturating_sub(equivs_before);
                    let active_vars = self.num_vars.saturating_sub(self.count_fixed_vars()).max(1);
                    let density = equivs as f64 / active_vars as f64;
                    // 0.05 sits well below substitution-heavy (>=0.1) and well
                    // above general (~0); calibrated on sc2025 + 2024 samples.
                    collapse_worthy = density >= 0.05;
                    if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
                        eprintln!(
                            "AB_AUTO: probe_equivs={equivs} active_vars={active_vars} density={density:.4} collapse_worthy={collapse_worthy}"
                        );
                    }
                    if !collapse_worthy {
                        // General instance: bail before decompose/fixpoint;
                        // only the cheap probe round was paid. Disable the
                        // gate-dependent substitution passes for the rest of
                        // this solve so inprocessing does not re-trigger them.
                        self.inproc_ctrl.decompose.enabled = false;
                        self.inproc_ctrl.congruence.enabled = false;
                    }
                }
            }
            let _t_cong_wall = _t_cong_start.elapsed();
            tracing::debug!(
                "[preprocess-breakdown] flush={:.1}ms gc={:.1}ms bcp={:.1}ms cong_wall={:.1}ms",
                _t_flush_done.as_secs_f64() * 1000.0,
                _t_gc_done.as_secs_f64() * 1000.0,
                _t_bcp_done.as_secs_f64() * 1000.0,
                _t_cong_wall.as_secs_f64() * 1000.0,
            );

            _t1_cong = _t0.elapsed().as_millis();

            // 1b. Backbone literal computation.
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            // CaDiCaL runs backbone during preprocessing (internal.cpp:769)
            // after gates+decompose. AY's backbone uses CDCL-based probing which
            // is O(probes * BCP_cost_per_probe). On medium formulas (438K clauses)
            // this costs 4s despite the 5K conflict budget. CaDiCaL's backbone
            // uses lightweight binary-clause propagation. Only run during
            // preprocessing on small formulas (≤10K clauses) where BCP is cheap.
            // Larger formulas defer to inprocessing where BVE has reduced the
            // formula size.
            if self.inproc_ctrl.backbone.enabled
                && !skip_expensive_preprocessing_passes
                && self.arena.num_clauses() <= 10_000
            {
                self.set_diagnostic_pass(DiagnosticPass::Backbone);
                self.backbone();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }
            _t2_bb = _t0.elapsed().as_millis();

            // 1c. SAT sweeping (equivalence merging + unit detection).
            //     CaDiCaL runs sweep during preprocessing (sweep.cpp), finding
            //     equivalent variables via SCC analysis and discovering units.
            //     On crn_11_99_u, sweep finds 45 units — the single largest
            //     contributor to CaDiCaL's fixed-var count.
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            // AY's sweep uses kitten-based COI probing (CaDiCaL sweep.cpp
            // pattern) with random simulation fallback (#6868). On uniform
            // formulas with no binary clauses, COI probing may find nothing,
            // but random simulation discovers candidates by assigning random
            // values, forward-propagating, and grouping variables by signature.
            // The skip_gate_dependent_passes guard avoids the O(clauses)
            // iteration cost when sweep is unlikely to find anything.
            // Sweep gating (#9215, #8448): sweep's kitten sub-solver cost
            // scales with num_vars (COI neighborhood traversal). On shuffling-2
            // (138K vars, 4.7M clauses), sweep solves 1824 vars in Kissat's
            // first pass — the critical technique that enables fast SAT.
            //
            // Small-dense skip (#8448): on small dense formulas (< 10K vars,
            // density > 30), kitten probing is unproductive and dominates wall
            // time. On stable-300 (300 vars, density 58.5), the scaled budget
            // (300K ticks) is fast enough, but Schur_161_5 (805 vars, density
            // ~33) wastes 2-3s. Skip sweep when both conditions hold.
            // Large dense formulas like shuffling-2 (138K vars, 83% binary)
            // benefit from sweep despite high density.
            let skip_sweep_small_dense = self.num_vars < 10_000 && formula_density > 30.0;
            let skip_sweep_preprocessing = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
                || skip_gate_dependent_passes
                || skip_sweep_small_dense;
            if self.inproc_ctrl.sweep.enabled && !skip_sweep_preprocessing {
                self.set_diagnostic_pass(DiagnosticPass::Sweep);
                if self.sweep() {
                    self.clear_diagnostic_pass();
                    return true;
                }
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }

            // 2. Decompose (SCC equivalent literal substitution).
            //    Runs after congruence + backbone + sweep so Tarjan can leverage
            //    new binary implication edges from congruence equivalence binaries
            //    and any new units discovered by backbone/sweep.
            //    Decompose stays disabled in proof modes until proof emission
            //    and final model reconstruction are both safe.
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            // Decompose is gated by density (#8448): the SCC substitution
            // path has a soundness issue on dense shuffled formulas that
            // produces false UNSAT. Keep density guard until fixed.
            if self.inproc_ctrl.decompose.enabled && !skip_congruence && !skip_dense_formula {
                self.set_diagnostic_pass(DiagnosticPass::Decompose);
                self.decompose();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }

            // 2a. Substitution fixpoint experiment (#15 Phase 2, A/B knob
            // AY_AB_SUBST_FIXPOINT=1, default OFF = byte-identical behavior).
            // Kissat reaches its congruence+substitution fixpoint inside ONE
            // probe-time closure (70da0b78: 27217 vars substituted -> UNSAT in
            // 0.11s). AY runs one congruence round per preprocess/inprocessing
            // slot, so each further round costs a full CDCL search interval —
            // on 70da0b78 it spreads 6 diminishing rounds (14913, 2001, 619,
            // 1437, 103, 389 equivalences) across a 30s timeout it never
            // escapes. This loop drives congruence -> decompose to fixpoint
            // immediately, capped at 10 rounds. Each round re-checks
            // interruption; the preprocess deadline is pushed out by the
            // loop's own elapsed time so downstream passes are not starved.
            let want_fixpoint = matches!(
                std::env::var("AY_AB_SUBST_FIXPOINT").ok().as_deref(),
                Some("1")
            ) || (auto_collapse && collapse_worthy);
            if want_fixpoint
                && self.inproc_ctrl.gate.enabled
                && self.inproc_ctrl.congruence.enabled
                && self.inproc_ctrl.decompose.enabled
                && !skip_gate_dependent_passes
                && !skip_congruence
                && !skip_dense_formula
            {
                for _round in 0..10 {
                    if self.preprocessing_should_stop(should_stop) {
                        return false;
                    }
                    let round_start = ay_core::time::Instant::now();
                    let equivs_before = self.inproc.congruence.stats().equivalences_found;
                    let skipped_before = self.inproc.congruence.stats().non_rup_equivalences;
                    self.set_diagnostic_pass(DiagnosticPass::Congruence);
                    let found = self.congruence();
                    self.clear_diagnostic_pass();
                    if self.propagate_check_unsat() {
                        return true;
                    }
                    if !found {
                        break;
                    }
                    // Spin guard: in proof mode the closure can re-derive the
                    // same non-RUP edges every round while emission skips them
                    // all — decompose then substitutes nothing and the loop
                    // makes no progress (observed on 70da0b78 under
                    // AY_AB_DRAT_SUBST: 947 edges re-skipped per round). Break
                    // when the round's ACCEPTED yield is zero.
                    {
                        let s = self.inproc.congruence.stats();
                        let yielded = s.equivalences_found - equivs_before;
                        let skipped = s.non_rup_equivalences - skipped_before;
                        if yielded <= skipped {
                            break;
                        }
                    }
                    self.set_diagnostic_pass(DiagnosticPass::Decompose);
                    self.decompose();
                    self.clear_diagnostic_pass();
                    if self.propagate_check_unsat() {
                        return true;
                    }
                    if let Some(deadline) = self.cold.preprocess_deadline.as_mut() {
                        *deadline += round_start.elapsed();
                    }
                }
            }
            _t3_decomp = _t0.elapsed().as_millis();

            // Post-collapse BVE eligibility re-derivation (AY_AB_BVE_POST_COLLAPSE,
            // default ON since 2026-07-10 wf_55735963; =0 kill-switch). Placed
            // IMMEDIATELY after the congruence+decompose
            // collapse (steps 1/2/2a above — the re-derivation is meaningless
            // any earlier because count_removed()==0 until decompose runs) and
            // BEFORE the next preprocess_timed_out() stage boundary: the
            // collapse on a >200K-var instance typically consumes the whole 2s
            // large-formula budget itself, so without the deadline extension
            // here control flow would early-return at step 2b and never reach
            // the BVE stage at 4d (measured on ebbda8d9: 200K equivs + 403K
            // substitutions, then deadline-abort before BVE).
            //
            // Two ORIGINAL-num_vars gates keep BVE off these instances:
            // skip_expensive_preprocessing_passes (bypassed inside
            // run_preprocess_bve via the unlock) and — the part the cap alone
            // cannot fix — `features.bve = false` on the Default DIMACS route
            // for anything above the 150K sparse-band cap, which leaves
            // `inproc_ctrl.bve.enabled` false and skips the 4d dispatch
            // entirely. Arm BVE here when the re-derived eligibility holds.
            // Fail-closed: the unlock predicate refuses LRAT/incremental/
            // AY_SAT_NO_BVE, and enforce_inprocessing_proof_overrides()
            // re-clamps anything the proof-capability registry forbids (BVE is
            // DRAT-legal). The arming persists into inprocessing, so the
            // interval-scheduled elimination rounds also see the collapsed
            // residual. The deadline extension is knob-scoped and bounded by
            // the BVE wall window (deep-aware); the intermediate stages (2b
            // HTR / 3 probe / 4 factor) remain gated by skip_expensive, so the
            // extension is effectively spent on BVE only.
            if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
                eprintln!(
                    "AB_BVE_POST_COLLAPSE: check num_vars={} active={} removed={} active_clauses={} lrat={} incr={} unlock={}",
                    self.num_vars,
                    self.var_lifecycle.count_active(),
                    self.var_lifecycle.count_removed(),
                    self.arena.active_clause_count(),
                    self.cold.lrat_enabled,
                    self.cold.has_been_incremental,
                    self.bve_post_collapse_unlock_active(),
                );
            }
            if self.bve_post_collapse_unlock_active() {
                self.inproc_ctrl.bve.enabled = true;
                self.enforce_inprocessing_proof_overrides();
                if self.inproc_ctrl.bve.enabled {
                    // Proof-aware (wf_0c7d84e9): see PROOF_WALL_BUDGET_SCALE.
                    let extension_secs = self.bve_wall_budget_scale()
                        * if self.bve_sparse_deep_active() {
                            BVE_SPARSE_DEEP_PREPROCESS_BUDGET_SECS
                        } else {
                            2 * FASTELIM_WALL_CLOCK_LIMIT_SECS
                        };
                    let extended = ay_core::time::Instant::now()
                        + std::time::Duration::from_secs(extension_secs);
                    match self.cold.preprocess_deadline.as_mut() {
                        Some(deadline) if *deadline < extended => *deadline = extended,
                        _ => {}
                    }
                }
                if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
                    eprintln!(
                        "AB_BVE_POST_COLLAPSE: armed bve={} (num_vars={} active={} removed={})",
                        self.inproc_ctrl.bve.enabled,
                        self.num_vars,
                        self.var_lifecycle.count_active(),
                        self.var_lifecycle.count_removed()
                    );
                }
            }

            // Giant raw-BVE unlock (lever 3, AY_AB_BVE_GIANT_RAW; 2026-07-11
            // sparse-prize completion round). Placed HERE — the same
            // post-collapse-stage slot as the block above — because its "no
            // collapse" qualification (count_removed() == 0) is only
            // meaningful after decompose had its chance, and because a
            // no-collapse giant hits the same two ORIGINAL-num_vars gates:
            // `features.bve = false` above the 150K sparse-band cap (leaves
            // inproc_ctrl.bve.enabled false, skipping the 4d dispatch) and
            // skip_expensive_preprocessing_passes (bypassed inside
            // run_preprocess_bve via the unlock). Elimination-shaped giants
            // (9d7caee5: 1.69M vars, 5.96M clauses, density 3.5, probe
            // equivalence density 0) additionally never reach the
            // post-collapse arming — no substitution structure exists — so
            // without this block they have NO preprocess-BVE route at all
            // while kissat solves them via 93% elimination (unsat@66s).
            // Fail-closed and disjoint: try_qualify_bve_giant_raw refuses
            // LRAT/incremental/AY_SAT_NO_BVE and any collapsed instance
            // (those stay on the measured post-collapse path), and
            // enforce_inprocessing_proof_overrides() re-clamps anything the
            // proof-capability registry forbids. The deadline extension
            // mirrors the post-collapse block (deep-aware, proof-scaled) —
            // the arming persists into inprocessing like the other unlocks.
            if self.try_qualify_bve_giant_raw() {
                self.inproc_ctrl.bve.enabled = true;
                self.enforce_inprocessing_proof_overrides();
                if self.inproc_ctrl.bve.enabled {
                    // Proof-aware (wf_0c7d84e9): see PROOF_WALL_BUDGET_SCALE.
                    let extension_secs = self.bve_wall_budget_scale()
                        * if self.bve_sparse_deep_active() {
                            BVE_SPARSE_DEEP_PREPROCESS_BUDGET_SECS
                        } else {
                            2 * FASTELIM_WALL_CLOCK_LIMIT_SECS
                        };
                    let extended = ay_core::time::Instant::now()
                        + std::time::Duration::from_secs(extension_secs);
                    match self.cold.preprocess_deadline.as_mut() {
                        Some(deadline) if *deadline < extended => *deadline = extended,
                        _ => {}
                    }
                }
                if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
                    eprintln!(
                        "AB_BVE_GIANT_RAW: armed bve={} (num_vars={} active={} removed={} active_clauses={})",
                        self.inproc_ctrl.bve.enabled,
                        self.num_vars,
                        self.var_lifecycle.count_active(),
                        self.var_lifecycle.count_removed(),
                        self.arena.active_clause_count(),
                    );
                }
            }

            let _t_htr_start = ay_core::time::Instant::now();

            // 2b. HTR (hyper-ternary resolution).
            //     CaDiCaL pattern (probe.cpp:936-948):
            //       decompose(); if (ternary()) decompose();
            //     HTR resolves ternary clause pairs to derive binary resolvents
            //     that create new implication graph edges for decompose.
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            if self.inproc_ctrl.htr.enabled
                && !skip_expensive_preprocessing_passes
                && !preprocessing_quick_mode
            {
                self.set_diagnostic_pass(DiagnosticPass::HTR);
                let produced_binary = self.htr();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }

                // Re-run decompose if HTR produced binary clauses (new SCC edges).
                if produced_binary && self.inproc_ctrl.decompose.enabled {
                    self.set_diagnostic_pass(DiagnosticPass::Decompose);
                    self.decompose();
                    self.clear_diagnostic_pass();
                    if self.propagate_check_unsat() {
                        return true;
                    }
                }
            }

            let _t_htr_wall = _t_htr_start.elapsed();
            let _t_probe_start = ay_core::time::Instant::now();

            // 3. Probing (failed literal detection).
            //    Runs after decompose so the binary implication graph is simplified,
            //    yielding more effective root-literal probes.
            //    LRAT hints are collected via collect_probe_conflict_lrat_hints
            //    before backtracking, so probing works in both DRAT and LRAT modes.
            //    Deferred from preprocessing quick path — fires in first inprocessing
            //    round at ~2K conflicts (CaDiCaL internal.cpp:695-739).
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            if self.inproc_ctrl.probe.enabled
                && !preprocessing_quick_mode
                && !skip_expensive_preprocessing_passes
            {
                // Ensure level-0 unit proof IDs before probe hint collection.
                // In preprocessing, backbone/decompose may not have run (if disabled),
                // so probe must ensure IDs itself. Fixes #7108.
                // Deferred from expensive preprocessing -- fires in first
                // inprocessing round at ~2K conflicts (#8084).
                if self.run_preprocess_probe_pass(skip_congruence) {
                    return true;
                }
            }

            let _t_probe_wall = _t_probe_start.elapsed();
            let _t_factor_start = ay_core::time::Instant::now();
            let dense_factor_bve_lrat_route = self.dense_factor_bve_lrat_preprocess_route_active();

            // 4. Factorization (extension variable compression).
            //    CaDiCaL runs factoring BEFORE fastelim (internal.cpp:774-778).
            //    On clique formulas, factorization introduces extension variables
            //    that compress binary clause patterns, enabling fastelim to
            //    cascade through extension variables for 70%+ clause reduction.
            //
            //    Skip factorization on small dense formulas (<1000 vars,
            //    density >10 clauses/var). On these formulas, factorization
            //    introduces extension variables that bloat the search space
            //    without enabling useful BVE cascades. Measured on clique_n2_k10
            //    (180 vars, 3160 clauses): factorization adds 257 vars (142%
            //    increase), causing 2x slowdown (17K vs 37K conflicts/sec).
            //    CaDiCaL's factor is effective on larger structured formulas
            //    where extension variables compress repeated patterns, but on
            //    small dense combinatorial formulas the variable overhead
            //    dominates. Threshold of 1000 vars is conservative; density >10
            //    catches clique/Ramsey-type formulas while allowing structured
            //    formulas (e.g. FmlaEquivChain at density ~3) through.
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            // #8466: Removed the small-dense factorization skip (av < 1000
            // && density > 10). CaDiCaL runs factorization on ALL formulas
            // including clique_n2_k10, introducing 292 extension variables that
            // compress the binary clause structure and enable fastelim to
            // eliminate 359/472 vars (76%). Without factorization, AY only
            // eliminates 10/180 vars (6%), leaving 170 active vars vs CaDiCaL's
            // 113. The original skip (added for performance) was measured before
            // the chrono-BT adaptive disable and gc_occ overhead fix; with those
            // in place, the dynamics are different and factorization's clause
            // compression enables a fundamentally smaller search space.
            // Latch pre-factor counts for the opt-in post-factor BVE
            // clause-reopen (AY_AB_BVE_POST_FACTOR, DEFAULT OFF —
            // MEASURED-NEGATIVE; see bve_post_factor_reopens). Captured
            // IMMEDIATELY BEFORE the factor step so the re-derivation after it
            // can measure how far factoring collapsed the active-clause count.
            // Cheap and inert: two O(1) reads, unread by the reopen predicate
            // unless the knob is armed (which additionally requires
            // factored_vars>0 and a large-ratio collapse).
            self.cold.pre_factor_active_clauses = self.arena.active_clause_count();
            self.cold.pre_factor_num_vars = self.num_vars;
            if dense_factor_bve_lrat_route {
                let bve_outcome = self.run_dense_factor_bve_lrat_preprocess_route(
                    skip_gate_dependent_passes,
                    skip_expensive_preprocessing_passes,
                );
                bve_rebuilt_watches = bve_rebuilt_watches || bve_outcome.rebuilt_watches;
                if bve_outcome.found_unsat {
                    return true;
                }
            } else if self.should_preprocess_factor()
                && (!skip_expensive_preprocessing_passes
                    || (factor_dense_enabled()
                        && formula_density >= config_preprocess_policy::factor_dense_min_density()))
            {
                // #14 factor-dense unlock (default ON, AY_AB_FACTOR_DENSE=0
                // disables): dense ternary formulas are the MOST factorable
                // class (BVA's target), but the shared density skip
                // blanket-disabled factor on them. Measured on SAT-COMP
                // main-track 82851650 (4.6k vars, 474k clauses, density 103):
                // skip = timeout at 7.9M conflicts; with factor allowed
                // through = s UNSATISFIABLE at 2529 conflicts (kissat-parity:
                // 2549), 219 factors across 3 passes. Sound regardless of
                // scheduling: factorization is satisfiability-preserving with
                // model reconstruction and full DRAT/LRAT proof plumbing —
                // only cost, never verdict, is at stake. Default flipped on
                // the 32-instance dense A/B (+2 solves, 0 lost, 0 verdict
                // disagreements — see factor_dense_enabled). The residual
                // ~47s Factor::run cost vs kissat's <0.5s is the algorithmic
                // follow-up (incremental PQ factoring), bounded meanwhile by
                // the honestly-accounted effort budget (#14-factor-cost).
                self.set_diagnostic_pass(DiagnosticPass::Factor);
                self.factorize();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }
            let _t_factor_wall = _t_factor_start.elapsed();
            tracing::debug!(
                "[preprocess-phases] htr={:.1}ms probe={:.1}ms factor={:.1}ms",
                _t_htr_wall.as_secs_f64() * 1000.0,
                _t_probe_wall.as_secs_f64() * 1000.0,
                _t_factor_wall.as_secs_f64() * 1000.0,
            );
            _t4_factor = _t0.elapsed().as_millis();

            // Post-factor BVE clause-reopen arming (AY_AB_BVE_POST_FACTOR,
            // DEFAULT OFF — MEASURED-NEGATIVE on its target class; see
            // try_qualify_bve_post_factor / bve_post_factor_reopens). Placed
            // IMMEDIATELY AFTER the factor step (the CLAUSE-axis analogue of
            // the post-collapse arming block above): factoring on the
            // density-264 huge-binary cluster (f6a085f3: 42K vars, 11.1M
            // clauses) collapses active_clauses ~97% (→ ~371K) while GROWING
            // num_vars, so the var-gated post-collapse reopen never fires and
            // both ORIGINAL-clause gates (skip_expensive + features.bve=false
            // above the sparse-band cap) stay latched on the pre-factor counts.
            // Re-derive BVE eligibility on the factored residual: arm
            // inproc_ctrl.bve.enabled (else the 4d dispatch below is skipped)
            // and push the deadline out by the BVE wall window so the
            // just-unlocked pass is not truncated. Fail-closed
            // (LRAT/incremental/AY_SAT_NO_BVE refused in try_qualify) and
            // enforce_inprocessing_proof_overrides() re-clamps anything the
            // proof registry forbids. Knob-scoped: a complete no-op unless
            // AY_AB_BVE_POST_FACTOR=1. HONEST STATUS: the reopen FIRES
            // correctly but AY's BVE eliminates a structural ceiling of ~1,306
            // vs kissat's 104,496 on this class, so f6 stays s UNKNOWN — this
            // is measurement infra, not a solve, and ships opt-in only.
            if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
                eprintln!(
                    "AB_BVE_POST_FACTOR: check enabled={} pre_factor_clauses={} active_clauses={} factored_vars={} lrat={} incr={}",
                    config_preprocess_policy::bve_post_factor_enabled(),
                    self.cold.pre_factor_active_clauses,
                    self.arena.active_clause_count(),
                    self.num_vars.saturating_sub(self.cold.pre_factor_num_vars),
                    self.cold.lrat_enabled,
                    self.cold.has_been_incremental,
                );
            }
            if self.try_qualify_bve_post_factor() {
                self.inproc_ctrl.bve.enabled = true;
                self.enforce_inprocessing_proof_overrides();
                if self.inproc_ctrl.bve.enabled {
                    // Proof-aware (wf_0c7d84e9): see PROOF_WALL_BUDGET_SCALE.
                    let extension_secs = self.bve_wall_budget_scale()
                        * if self.bve_sparse_deep_active() {
                            BVE_SPARSE_DEEP_PREPROCESS_BUDGET_SECS
                        } else {
                            2 * FASTELIM_WALL_CLOCK_LIMIT_SECS
                        };
                    let extended = ay_core::time::Instant::now()
                        + std::time::Duration::from_secs(extension_secs);
                    match self.cold.preprocess_deadline.as_mut() {
                        Some(deadline) if *deadline < extended => *deadline = extended,
                        _ => {}
                    }
                }
                if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
                    eprintln!(
                        "AB_BVE_POST_FACTOR: armed bve={} (num_vars={} pre_factor_vars={} active_clauses={} pre_factor_clauses={})",
                        self.inproc_ctrl.bve.enabled,
                        self.num_vars,
                        self.cold.pre_factor_num_vars,
                        self.arena.active_clause_count(),
                        self.cold.pre_factor_active_clauses,
                    );
                }
            }

            // 4c. Pre-BVE subsumption: CaDiCaL elim.cpp:1043-1044.
            //     Subsumption reduces occurrence counts after factorization,
            //     enabling more profitable fastelim eliminations on structured
            //     formulas. On clique formulas, factorization introduces extension
            //     variables that compress binary clause patterns -- subsumption
            //     removes the resulting redundancy (#7178 Gap A).
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            if !dense_factor_bve_lrat_route
                && !self.circuit_bve_lrat_preprocess_route_active()
                && self.inproc_ctrl.subsume.enabled
                && !skip_expensive_preprocessing_passes
            {
                self.set_diagnostic_pass(DiagnosticPass::Subsume);
                self.subsume();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }

            // 4d-pre. Preprocessing vivification for small dense formulas (#8135).
            //   On clique-like formulas (180 vars, 3160 clauses), vivification
            //   before BVE shortens clauses, reduces occurrence counts, and
            //   enables more effective variable elimination. Kissat achieves 88%
            //   vivification success on clique formulas; running vivification
            //   during preprocessing ensures AY gets the same benefit.
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            {
                let formula_class = FormulaClass::classify(
                    self.num_vars.saturating_sub(self.count_fixed_vars()),
                    self.arena.active_clause_count(),
                );
                if !dense_factor_bve_lrat_route
                    && !self.circuit_bve_lrat_preprocess_route_active()
                    && formula_class == FormulaClass::Small
                    && self.inproc_ctrl.vivify.enabled
                    && !skip_expensive_preprocessing_passes
                {
                    self.set_diagnostic_pass(DiagnosticPass::Vivify);
                    if self.vivify_preprocess() {
                        self.clear_diagnostic_pass();
                        return true;
                    }
                    self.clear_diagnostic_pass();
                    if self.propagate_check_unsat() {
                        return true;
                    }
                    watches_valid = false;
                }
            }

            // 4d-bce (#maxsat-bce-preprocess): BCE before BVE — unlocks
            // eliminations on LP-extracted encodings; only fires when a
            // caller arms inproc_ctrl.bce.enabled (MaxSAT one-shot), so
            // default SAT/SMT paths are bit-identical.
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            if !dense_factor_bve_lrat_route
                && !self.circuit_bve_lrat_preprocess_route_active()
                && self.inproc_ctrl.bce.enabled
                && !skip_expensive_preprocessing_passes
            {
                self.set_diagnostic_pass(DiagnosticPass::BCE);
                self.bce();
                self.clear_diagnostic_pass();
                if self.propagate_check_unsat() {
                    return true;
                }
            }

            // 4d. BVE / fastelim (witness-based reconstruction, CaDiCaL approach).
            //     Preprocessing uses fastelimbound=8 and bypasses conflict-interval
            //     scheduling because num_conflicts=0 would otherwise suppress BVE (#4209).
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            if self.circuit_bve_lrat_preprocess_route_active() {
                let bve_outcome =
                    self.run_circuit_bve_lrat_preprocess_route(skip_expensive_preprocessing_passes);
                bve_rebuilt_watches = bve_rebuilt_watches || bve_outcome.rebuilt_watches;
                if bve_outcome.found_unsat {
                    return true;
                }
            } else if self.inproc_ctrl.bve.enabled && !dense_factor_bve_lrat_route {
                let bve_outcome = self.run_preprocess_bve(
                    skip_gate_dependent_passes,
                    skip_expensive_preprocessing_passes,
                );
                bve_rebuilt_watches = bve_outcome.rebuilt_watches;
                if bve_outcome.found_unsat {
                    return true;
                }
            }
            _t5_bve = _t0.elapsed().as_millis();

            // 4e. Post-BVE probing: CaDiCaL runs probing AFTER fastelim/BVE
            //     during the quick preprocessing path (internal.cpp:788, probe.cpp).
            //     On structured BMC formulas, post-BVE probing finds backbone
            //     variables that collapse the remaining search space. CaDiCaL's
            //     log shows the 'P' line AFTER all 'e' (BVE) lines.
            //     Previously AY deferred probing from quick mode (#6926), but
            //     this skips the post-BVE probing step that CaDiCaL includes.
            //     On stric-bmc-ibm-10, this is the difference between SAT (0.35s)
            //     and Unknown (timeout) when factor+sweep are both enabled (#3366).
            if self.preprocessing_should_stop(should_stop) {
                return false;
            }
            if self.inproc_ctrl.probe.enabled
                && !skip_expensive_preprocessing_passes
                && self.run_preprocess_probe_pass(skip_congruence)
            {
                // Post-BVE probing deferred on large formulas -- fires in first
                // inprocessing round at ~2K conflicts (#8084).
                return true;
            }
            _t6_probe = _t0.elapsed().as_millis();

            let cleanup = self.run_preprocess_cleanup_stage(
                preprocessing_quick_mode,
                skip_expensive_preprocessing_passes,
                skip_dense_formula,
                should_stop,
            );
            if cleanup.invalidated_watches {
                watches_valid = false;
            }
            match cleanup.control {
                PreprocessStageControl::Continue => {}
                PreprocessStageControl::ReturnFalse => return false,
                PreprocessStageControl::Unsat => return true,
            }

            // Check if we reached a fixed point
            let vars_after = self.num_vars - self.count_fixed_vars();
            if vars_after == vars_before {
                break;
            }
        }

        // Preprocessing summary: CaDiCaL-style fixed/eliminated/substituted/factored totals.
        self.emit_preprocess_summary(
            _preprocess_start,
            _t1_cong,
            _t2_bb,
            _t3_decomp,
            _t4_factor,
            _t5_bve,
            _t6_probe,
        );

        let _t7_loop_done = _preprocess_start.elapsed().as_millis();

        // Final GC: remove clauses that still mention eliminated/substituted
        // variables after all preprocessing passes (#7083, #8496).
        // Also called from solve_no_assumptions after preprocess() returns,
        // to handle early-return paths (timeouts/interrupts). The function
        // is idempotent when no new variables have been removed.
        let finalize_deleted = self.finalize_preprocess_clause_cleanup();

        // #8496: Verify no active clause references a removed variable.
        #[cfg(debug_assertions)]
        if self.var_lifecycle.count_removed() > 0 {
            for idx in self.arena.indices() {
                if self.arena.is_dead(idx) || self.arena.is_empty_clause(idx) {
                    continue;
                }
                for lit in self.arena.literals(idx) {
                    assert!(
                        !self.var_lifecycle.is_removed(lit.variable().index()),
                        "BUG (#8496): finalize_preprocess_clause_cleanup missed active clause {idx} \
                         (len={}, learned={}) containing removed variable {} \
                         (is_dead={}, is_empty={}, is_active={})",
                        self.arena.len_of(idx),
                        self.arena.is_learned(idx),
                        lit.variable().index(),
                        self.arena.is_dead(idx),
                        self.arena.is_empty_clause(idx),
                        self.arena.is_active(idx),
                    );
                }
            }
        }

        // Signal to solve_no_assumptions whether watches are still valid.
        // BVE disconnects/reconnects watches as its last step. If no subsequent
        // pass modified clause literals in-place, the caller can skip the
        // redundant O(clauses) watch rebuild.
        // #8496: When finalize deleted any clauses containing eliminated
        // variables, watches are NOT valid — arena.delete() on pending-garbage
        // clauses zeroes lit_len but does NOT remove stale watch entries.
        // The binary-clause BCP path does not check garbage bits, so stale
        // binary watch entries can propagate eliminated variables onto the
        // trail. Force a full watch rebuild in that case.
        let base_valid = watches_valid || bve_rebuilt_watches;
        self.cold.preprocess_watches_valid = base_valid && !finalize_deleted;

        let _t_final = _preprocess_start.elapsed();
        tracing::debug!(
            "[preprocess-final] total={:.1}ms cong={_t1_cong}ms bb={_t2_bb}ms decomp={_t3_decomp}ms factor={_t4_factor}ms bve={_t5_bve}ms probe={_t6_probe}ms gc={:.1}ms",
            _t_final.as_secs_f64() * 1000.0,
            _t_final.as_millis().saturating_sub(_t7_loop_done) as f64,
        );
        false
    }

    /// Run the initial preprocessing pipeline ONCE, synchronously, without
    /// entering a solve (#maxsat-oneshot-preproc). This is the entry a caller
    /// (ay-maxsat's OllEngine) uses to get a single BVE/subsumption pass on
    /// the hard formula before the incremental core-extraction loop begins,
    /// WITHOUT arming per-solve inprocessing (which would rerun it on every
    /// assumption solve — the rehash storm the >500k gate exists to avoid).
    ///
    /// Mirrors the no-assumptions solve prologue (solve/mod.rs:562-624)
    /// exactly: preprocess() → finalize_preprocess_clause_cleanup (the #8496
    /// dead-var clause purge, MANDATORY so watches never reference eliminated
    /// variables) → watch rebuild → root re-propagate → self-disable. Returns
    /// true iff UNSAT was detected. After this returns, subsequent
    /// solve_with_assumptions calls behave as normal incremental solves
    /// (`preprocess_enabled` is now false), and BVE model reconstruction is
    /// handled per-solve on the finalize path — models come back over the
    /// original variable space with eliminated vars restored.
    ///
    /// The caller MUST freeze every variable it needs to survive (e.g. all
    /// soft-clause variables in a MaxSAT setting) BEFORE calling this: BVE
    /// only skips frozen variables, and once eliminated a variable cannot be
    /// referenced by a later `add_clause`.
    ///
    /// No-op (returns false) if preprocessing is disabled, the solver has
    /// already gone incremental, or it is not at decision level 0.
    pub fn preprocess_once(&mut self) -> bool {
        if !self.cold.preprocess_enabled
            || self.cold.has_been_incremental
            || self.decision_level != 0
        {
            return false;
        }
        let preprocess_unsat = self.preprocess();
        let cleanup_unsat = self.finish_initial_preprocessing();
        preprocess_unsat || cleanup_unsat
    }

    /// Helper: count the number of fixed (assigned at level 0) variables.
    /// Uses trail.len() which is O(1) (#3758 Phase 3).
    pub(super) fn count_fixed_vars(&self) -> usize {
        self.trail.len()
    }
}

#[cfg(test)]
#[path = "config_preprocess_tests.rs"]
mod tests;
