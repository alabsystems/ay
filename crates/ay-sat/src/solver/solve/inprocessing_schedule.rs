// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing pass scheduling facade.
//!
//! `run_restart_inprocessing` orchestrates the inprocessing pipeline that runs
//! at decision level 0 after restarts. The pass ordering and interleaving
//! logic follows CaDiCaL's probe.cpp / elim.cpp pipeline with AY-specific
//! tuning.
//!
//! Implementation is split across sibling modules:
//! - `inprocessing_maintenance`: garbage drain and gate checks
//! - `inprocessing_equivalence`: vivify, subsume, probe, congruence, HTR
//! - `inprocessing_elimination`: BVE+subsume+BCE+CCE cascade, factor, standalone BCE/CCE, condition, transred, sweep
//! - `inprocessing_round_end`: invariant checks, telemetry, scheduling

use super::super::*;

impl Solver {
    /// Generic inprocessing budget guard shared by the round guard and the
    /// per-pass (backbone / sweep) guards: `true` once the work window that
    /// started at (`start`, `start_ticks`) has consumed its budget.
    ///
    /// Deterministic mode (`AY_AB_DETERMINISTIC_INPROC=1`) gates on the
    /// machine-independent `search_ticks` delta since the window opened, so
    /// *which* passes fit no longer depends on host load. Wall-clock mode
    /// (default; `AY_AB_DETERMINISTIC_INPROC=0`) is byte-identical to `main` by
    /// construction — the `else` branch is the exact original `elapsed()`
    /// comparison. Only inner scheduling is bounded; the outer `-t <ms>` total
    /// timeout stays wall-clock. Soundness surface is zero: the budget schedules
    /// work, never truth.
    #[inline]
    pub(in crate::solver) fn inproc_over_budget(
        &self,
        start: ay_core::time::Instant,
        start_ticks: u64,
        wall_limit_ms: u64,
        tick_budget: u64,
    ) -> bool {
        if crate::determinism::deterministic_inproc_enabled() {
            self.total_search_ticks().saturating_sub(start_ticks) >= tick_budget
        } else {
            start.elapsed().as_millis() as u64 >= wall_limit_ms
        }
    }

    /// Per-inprocessing-round budget guard (5 round-gate sites): wall-clock
    /// 2000ms in wall mode, `search_ticks` delta vs round entry in deterministic
    /// mode. Thin wrapper over [`Self::inproc_over_budget`] with the round
    /// budget (`AY_XP_INPROC_TICK_BUDGET`-overridable).
    #[inline]
    pub(in crate::solver) fn inproc_round_over_budget(
        &self,
        round_start: ay_core::time::Instant,
        round_start_ticks: u64,
    ) -> bool {
        self.inproc_over_budget(
            round_start,
            round_start_ticks,
            INPROCESSING_ROUND_WALL_LIMIT_MS,
            crate::determinism::round_tick_budget(),
        )
    }

    /// Run inprocessing immediately after a restart.
    ///
    /// Returns `true` if UNSAT was derived at decision level 0.
    #[inline]
    pub(in crate::solver) fn run_restart_inprocessing(&mut self) -> bool {
        // #8477: Runtime disable flag for bisecting inprocessing soundness bugs.
        // #8506: Reads cached OnceLock instead of per-call std::env::var() syscall.
        if ay_core::sat_disable_flags().no_inprocess {
            return false;
        }
        // Check interrupt before running any inprocessing (#3638).
        if self.is_interrupted() {
            return false;
        }

        // ── Lightweight maintenance (runs at level 0 after every restart) ──
        // Drain deferred HBR garbage has a fixpoint guard (O(1) when nothing
        // changed) and must run at every level-0 opportunity for correctness:
        // stale pending-garbage marks from probing BCP block watch list
        // integrity (#3971). L0 GC is deferred past the inprocessing gate
        // below to avoid O(clauses) scans on every level-0 restart.
        if self.decision_level == 0 {
            self.drain_all_pending_garbage();
            if self.propagate_check_unsat() {
                return true;
            }
        }

        // ── Inprocessing pass gate (#7135, #8208) ──────────────────────
        // Use total_conflicts() (lifetime + current solve) so the threshold
        // progresses across IC3/PDR's many tiny incremental solves.
        let total_conflicts = self.total_conflicts();
        if total_conflicts == 0 {
            return false;
        }
        if total_conflicts < self.cold.next_inprobe_conflict {
            return false;
        }

        // ── Reduction gate (#5130) ───────────────────────────────────
        if self.cold.last_inprobe_reduction > 0
            && self.cold.num_reductions == self.cold.last_inprobe_reduction
        {
            return false;
        }

        // ── Level 0 requirement (#4719) ──────────────────────────────
        if self.decision_level != 0 {
            return false;
        }

        self.run_restart_inprocessing_slow()
    }

    /// Execute the broad restart inprocessing pass set after the hot gate fires.
    ///
    /// Kept out of the restart hot path so the cheap per-restart checks do not
    /// inherit the instruction footprint of the full inprocessing pipeline.
    #[cold]
    #[inline(never)]
    fn run_restart_inprocessing_slow(&mut self) -> bool {
        // ── Level-0 garbage collection (deferred past inprocessing gate) ──
        // CaDiCaL runs mark_satisfied_clauses_as_garbage() inside collect()
        // which is called from reduce(), not on every restart. On large
        // formulas (4M+ clauses), the O(clauses) scan of
        // collect_level0_garbage consumed ~19% of search time when called
        // at every level-0 restart opportunity. Deferring it past the
        // inprocessing gate means it only fires when inprocessing passes
        // will actually run.
        if self.collect_level0_garbage() {
            return true;
        }
        if self.propagate_check_unsat() {
            return true;
        }

        // Trail must be fully propagated before inprocessing techniques.
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: unpropagated literals at inprocessing entry (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        // Reset minimal trail rewind tracker (#8095). Individual inprocessing
        // passes update this when they derive new units or delete reason clauses.
        // rebuild_watches() reads it to set qhead precisely.
        self.earliest_affected_trail_pos = None;

        // BVE occ lists are maintained incrementally while the saved state is
        // live (#8096). Cross-round retention is a default-off reuse candidate;
        // when disabled, the round finalizer clears `occ_populated` so these
        // hooks become no-ops after same-round BVE/BCE/dense consumers finish.
        // All clause-mutating techniques notify BVE via per-clause hooks:
        //   - Deletions: note_irredundant_clause_removed_for_bve (subsume, vivify,
        //     BCE, CCE, condition, transred, deduplicate, HTR, factor, SBVA)
        //   - Replacements: note_irredundant_clause_replaced_for_bve (subsume, vivify)
        //   - Additions: note_irredundant_clause_added_for_bve (HTR, factor, SBVA)
        //   - Decompose/sweep: occ_remove_clause/occ_replace_clause in apply_decompose_mutation
        //   - Promotions: note_clause_promoted_to_irredundant (subsume, vivify)
        //   - Congruence binaries: direct occ_add_new_irredundant calls
        //   - HBR binaries: direct occ_add_new_irredundant calls
        //   - collect_level0_garbage: per-clause occ notifications when irredundant
        //     clauses are deleted or strengthened (#8364)
        // Compaction recreates BVE from scratch.

        // ── Per-round overhead tracking (#8099) ──────────────────────────
        // Capture wall-clock start and per-pass timing baseline so we can
        // compute infrastructure overhead = total_round_time - sum(pass_times).
        let round_start = ay_core::time::Instant::now();
        // Deterministic per-round work baseline: cumulative search_ticks
        // (focused + stable) at round entry. When the deterministic budget is
        // active, the per-round pass gates measure the tick delta against this
        // instead of `round_start.elapsed()` (wf_6503d3eb determinism harden).
        let round_start_ticks = self.total_search_ticks();
        let pass_time_baseline: [u64; solver_stats::INPROCESS_TIMING_LABELS.len()] =
            self.stats.inprocessing_time_ns;
        let pass_yield_baseline: [u64; solver_stats::INPROCESS_ACCOUNTING_LABELS.len()] =
            self.stats.inprocessing_pass_yields;

        // ── JIT caching: defer invalidation to structural passes (#8128) ──
        // Instead of blanket-invalidating the compiled formula before ALL
        // inprocessing, we snapshot the current state and lazily invalidate
        // only when a structural pass runs (one that modifies clause literals
        // or structure). Deletion-only passes (BCE, CCE, condition, transred,
        // probe, congruence, backbone, reorder) are handled by guard bits in
        // the compiled code and do not require recompilation.
        let had_compiled_formula = self.has_compiled_formula();

        // ── Pass scheduling section ───────────────────────────────────
        // CaDiCaL probe.cpp:933-952 inprobe ordering:
        //   decompose → ternary → decompose → probe → decompose →
        //   extract_gates → decompose → backbone → sweep → decompose →
        //   vivify → transred → backbone → factor
        // AY currently keeps BVE/subsume/BCE/factor/transred/sweep in the
        // separate elimination pipeline and runs the assumption-based backbone
        // pass once after that block, immediately before vivification.
        let skip_gate_dependent_passes = self.is_uniform_nonbinary_irredundant_formula();
        // Use active (live) clause count for inprocessing gates. arena.num_clauses()
        // is cumulative (includes deleted), causing false skips on formulas like
        // FmlaEquivChain (4.7M parsed → 362K active after preprocessing, but
        // num_clauses() still reports ~4.7M). CaDiCaL gates on stats.current.irredundant
        // + stats.current.redundant which excludes deleted clauses.
        let active_clauses = self.arena.active_clause_count();
        // Density-based guard for large dense formulas (#8136).
        // On shuffling-2 (138K vars, 4.7M clauses, density 33.8), inprocessing
        // passes find almost nothing useful but consume 4+ seconds:
        //   decompose: 1.1s for 444 substitutions (0.009% of clauses)
        //   backbone:  2.3s for 0 backbone literals
        //   vivify:    0.6s for 169 strengthenings (0.004% of clauses)
        // Kissat solves with zero preprocessing/inprocessing. The density guard
        // uses the same thresholds as preprocessing (#8136) to skip these passes
        // on formulas where the ratio of work-done to time-spent is negligible.
        //
        // Use irredundant_count (not active_clause_count) for density (#8466):
        // after BVE eliminates most variables on small dense formulas like
        // clique_n2_k10 (180 vars → ~4 active), accumulated learned clauses
        // inflate the active_clause_count to ~8K, producing a spurious density
        // of ~2000 that blocks ALL inprocessing. The structural formula density
        // (irredundant clauses / structural active vars) correctly reflects the
        // formula's inherent complexity, not transient learned clause accumulation.
        //
        // Use structural active vars (num_vars - eliminated/substituted) instead
        // of num_vars - trail.len() (#8466). The trail-based estimate becomes
        // tiny (e.g., 5) when BVE creates extension variables that are immediately
        // fixed at level 0. With 2672 irredundant clauses / 5 = density 534,
        // all expensive inprocessing (factor, backbone, probe) gets blocked.
        // Structural active vars counts variables still in the formula, regardless
        // of assignment. On clique_n2_k10: 180 vars - 78 eliminated = 102
        // structural, density = 2672/102 = 26.2 — correctly below BVE_HIGH_DENSITY_SKIP.
        let irredundant_clauses = self.arena.irredundant_count();
        let structural_active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let formula_density = if structural_active_vars > 0 {
            irredundant_clauses as f64 / structural_active_vars as f64
        } else {
            0.0
        };
        let skip_dense_inprocessing = (irredundant_clauses > PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD
            && formula_density > PREPROCESS_BVE_SKIP_DENSITY)
            || formula_density > BVE_HIGH_DENSITY_SKIP;
        // Dense-skip elimination lift (kill-switch AY_AB_DENSE_SKIP_LIFT=0):
        // raised clause arm (2M -> 3M) for the elimination-side gates
        // (factor/HTR/probe/backbone + subsume); skip_congruence_inproc
        // below keeps the ORIGINAL dense predicate (the #8448
        // dense-decompose soundness guard is untouched). See
        // skip_dense_formula_elim for the d421913d measurement.
        let skip_dense_inprocessing_elim =
            config_preprocess_policy::PreprocessPolicy::skip_dense_formula_elim(
                irredundant_clauses,
                formula_density,
            );
        let skip_expensive_equivalence_passes = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || active_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES
            || skip_dense_inprocessing_elim;
        // Subsumption pays an O(clauses) occurrence-list setup cost. Large
        // sparse Main-track formulas such as spg_200_316 can also pay a large
        // transient memory cost just to build subsumption candidates, so keep
        // the hard var/active-clause gates and cool skipped/no-progress rounds
        // down with the large idle interval.
        let skip_subsume_inproc = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || active_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES
            || skip_dense_inprocessing_elim;
        // Congruence + decompose share a clause threshold (CONGRUENCE_MAX_CLAUSES = 3M).
        let skip_congruence_inproc = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || active_clauses > CONGRUENCE_MAX_CLAUSES
            || skip_dense_inprocessing;
        // Giant-formula bail for the two decompose RE-RUN sites below (HTR
        // produced_binary + probe_found_failed) — 2026-07-11 dense-band
        // regression fix, guard 2. Those sites bypass skip_congruence_inproc,
        // so DEFAULT-ON AUTO-armed decompose leaked O(total_literals) re-runs
        // onto >8M-clause giants that never ran the preprocess probe
        // (measured: 2,760ms / 4 runs on 0ec8c5e9's 21M-clause arena, a lost
        // 46s-margin SAT). Clause cap ONLY (AUTO_DECOMPOSE_RERUN_MAX_CLAUSES
        // = 8M, decoupled from the probe caps by the giant-3M fix so the
        // non-proof 10M probe raise does not widen this drag bound),
        // NOT skip_congruence_inproc (its 200K-var arm would hit the df813fe7
        // flip) and NOT a global armed-but-unprobed disarm (measured to lose
        // the 6f354fbe flip) — below-cap instances keep today's behavior
        // bit-for-bit. See auto_capped_giant_skips_decompose_rerun.
        let auto_giant_decompose_rerun_bail =
            config_preprocess_policy::auto_capped_giant_skips_decompose_rerun(
                self.cold.subst_auto_capped,
                active_clauses,
            );
        // CaDiCaL probe.cpp:936: clean duplicate binaries at inprobe start.
        // Techniques that produce binary clauses (decompose, probe HBR,
        // congruence, factor) can create duplicates between inprocessing rounds.
        // Skip on large dense formulas (#8084): deduplication iterates all
        // 2*num_vars literal indices with per-literal HashMap allocations.
        // On shuffling-2 (138K vars), this is 276K iterations with hash ops.
        // When decompose/congruence are skipped (skip_congruence_inproc), no
        // new binary clauses are produced, so deduplication finds nothing.
        if self.inproc_ctrl.decompose.enabled
            && !skip_congruence_inproc
            && self.deduplicate_binary_clauses()
        {
            return true;
        }

        // Capture clause count and BCP telemetry baselines for per-round diagnostic.
        let clauses_before = self.num_clauses();
        let bcp_blocker_before = self.stats.bcp_blocker_fastpath_hits;
        let bcp_binary_before = self.stats.bcp_binary_path_hits;
        let jumped_reasons_before = self.stats.jumped_reasons;
        let bcp_scan_before = self.stats.bcp_replacement_scan_steps;
        let preproc_lits_before = self.stats.preprocess_level0_literals_removed;
        let preproc_sat_before = self.stats.preprocess_level0_satisfied_deleted;

        // Track actually-executed passes for diagnostic telemetry (#4781).
        // Pre-allocate for typical max passes to avoid reallocations (#8084).
        let mut passes_run: Vec<&'static str> = Vec::with_capacity(16);
        // The scheduler has one shared backbone control for the cheap binary
        // path and the expensive bounded-CDCL path. Treat the whole round as
        // productive if either path finds units, so an empty bounded-CDCL probe
        // does not back off future binary backbone opportunities.
        let mut backbone_productive_this_round = false;
        let mut backbone_binary_ran_this_round = false;
        // #9084: only the backbone row itself may anchor the yield-rescue
        // cooldown. Decompose-only rescue rounds can occur while backbone is
        // still cooling down; letting those rounds write `current + cooldown`
        // would slide the shared backbone deadline indefinitely.
        let mut backbone_cooldown_eligible_this_round = false;

        // Kissat reorder.c: clause-weighted variable reorder.
        // Non-destructive (no clause modifications), runs before clause-modifying
        // passes. In focused mode, rebuilds VMTF queue by importance. In stable
        // mode, folds clause weights into EVSIDS scores. O(vars +
        // irredundant_clauses). Uses growing backoff like other inprocessing passes.
        // Skip on large dense formulas (#8084): on shuffling-2 (4.7M clauses),
        // the O(irredundant_clauses) weight scan adds measurable overhead with
        // negligible benefit when the formula is too large for reorder to matter.
        if self.should_reorder() && !skip_dense_inprocessing {
            self.run_timed_diagnostic_inprocessing_pass(
                DiagnosticPass::Reorder,
                Self::reorder_variables,
            );
            passes_run.push("reorder");
            self.inproc_ctrl.reorder.reschedule_growing(
                self.num_conflicts,
                REORDER_INTERVAL,
                3,
                2,
                REORDER_MAX_INTERVAL,
            );
        } else if self.should_reorder() && skip_dense_inprocessing {
            self.inproc_ctrl.reorder.reschedule_growing(
                self.num_conflicts,
                REORDER_INTERVAL,
                3,
                2,
                REORDER_MAX_INTERVAL,
            );
        }
        // BISECT: validate after reorder
        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        // CaDiCaL probe.cpp:920-921: decompose at inprobe start.
        // Normalizes the binary implication graph (SCC + variable substitution)
        // before any analysis. Gated by should_decompose() so the growing
        // backoff schedule (#7480 D3) controls frequency: unproductive calls
        // grow the interval 1.5×, productive calls reset to base.
        // On large residuals (>3M clauses), decompose's clause substitution
        // pass is O(total_literals) which is expensive (#7135).
        let should_decompose = self.should_decompose();
        if should_decompose {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Decompose);
        }
        if should_decompose && !skip_congruence_inproc {
            self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Decompose, Self::decompose);
            passes_run.push("decompose");
            if self.propagate_check_unsat() {
                return true;
            }
        }
        // BISECT: validate after decompose-1
        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        // HTR (hyper-ternary resolution): resolve ternary clause pairs to derive
        // binary and ternary resolvents. CaDiCaL runs ternary() BEFORE probe()
        // (probe.cpp:938-939) so that HTR-derived binary clauses enrich the
        // implication graph for failed literal probing and SCC decomposition.
        // HTR's rebuild() scan is O(clauses) — same order as decompose's SCC
        // traversal and congruence's gate scan. Uses the congruence threshold
        // (5M) rather than the expensive-pass threshold (3M) so HTR runs on
        // formulas like FmlaEquivChain (4.7M clauses) where HTR-derived
        // binaries are critical for probe and decompose effectiveness (#7279).
        let should_htr = self.should_htr();
        if should_htr {
            self.stats.record_inprocessing_attempt(DiagnosticPass::HTR);
        }
        if should_htr
            && !skip_congruence_inproc
            && self.cold.htr_consecutive_empty < HTR_STALL_LIMIT
        {
            self.jit_invalidate_for_structural_pass(); // HTR: structural (#8128)
            let resolvents_before = {
                let s = self.htr_stats();
                s.ternary_resolvents + s.binary_resolvents
            };
            let produced_binary =
                self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::HTR, Self::htr);
            passes_run.push("htr");
            let resolvents_after = {
                let s = self.htr_stats();
                s.ternary_resolvents + s.binary_resolvents
            };
            if resolvents_after > resolvents_before {
                self.cold.htr_consecutive_empty = 0;
            } else {
                // HTR produced 0 resolvents this round (#8448).
                // On EDP3 (91K vars, 680K clauses), 3 HTR rounds cost 554ms
                // with 0 resolvents. Permanently disable after BACKBONE_STALL_LIMIT
                // consecutive empty rounds.
                self.cold.htr_consecutive_empty += 1;
            }
            if self.propagate_check_unsat() {
                return true;
            }

            // CaDiCaL probe.cpp:939: re-runs decompose when ternary produces
            // binary resolvents (new implication graph edges may reveal new SCCs).
            // Gated by should_decompose() to respect growing backoff (#7480 D3).
            // Giant bail (dense-band fix, defense-in-depth here: the enclosing
            // HTR block already requires !skip_congruence_inproc, which a >8M
            // giant can never pass — the bail documents the re-run discipline).
            let should_decompose = self.should_decompose();
            if should_decompose {
                self.stats
                    .record_inprocessing_attempt(DiagnosticPass::Decompose);
            }
            if produced_binary && should_decompose && !auto_giant_decompose_rerun_bail {
                self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
                self.run_timed_diagnostic_inprocessing_pass(
                    DiagnosticPass::Decompose,
                    Self::decompose,
                );
                passes_run.push("decompose");
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        } else if should_htr
            && (skip_congruence_inproc || self.cold.htr_consecutive_empty >= HTR_STALL_LIMIT)
        {
            self.inproc_ctrl
                .htr
                .reschedule(self.num_conflicts, HTR_INTERVAL);
        }
        // BISECT: validate after htr
        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        if self.is_interrupted() {
            return false;
        }

        // Standalone subsumption: gated by large/dense expensive-pass policy.
        // On shuffling-2 (138K vars, 4.7M clauses, density 33.8), standalone
        // subsumption spends 11.7s for a 0.02% subsumption rate. The density
        // guard skips this pass on large dense formulas where the O(clauses)
        // setup cost dominates with negligible benefit.
        let should_subsume = self.should_subsume();
        if should_subsume {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Subsume);
        }
        if should_subsume && !skip_subsume_inproc {
            self.jit_invalidate_for_structural_pass(); // subsume: structural (#8128)
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Subsume, Self::subsume);
            passes_run.push("subsume");
            self.cold.subsume_ran_since_bve = true; // #8502: signal pre-BVE guard
                                                    // Subsumption can strengthen clauses into units. These units are
                                                    // not watched, so we must propagate here.
            if self.propagate_check_unsat() {
                return true;
            }
        } else if should_subsume && skip_subsume_inproc {
            // Skipped due to large/dense formula shape: use growing backoff so we don't
            // re-check on each inprocessing round (#9215).
            self.inproc_ctrl.subsume.reschedule_growing(
                self.num_conflicts,
                SUBSUME_INTERVAL,
                4,
                1,
                SUBSUME_LARGE_MAX_IDLE_INTERVAL,
            );
        }

        // BISECT: targeted validation after subsume
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after subsume");

        if self.is_interrupted() {
            return false;
        }

        let should_probe = self.should_probe();
        if should_probe {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Probe);
        }
        if should_probe {
            let failed_before = self.inproc.prober.stats().failed;
            // Probing returns true only on proven UNSAT (level-0 conflict).
            // Use explicit timing to capture probe() duration for overhead
            // calculation (#8099).
            let probe_unsat = self.run_probe_inprocessing_pass();
            if probe_unsat {
                return true;
            }
            passes_run.push("probe");
            // Drain deferred HBR subsumption deletions created during probing (#4761).
            // Probing BCP marks subsumed clauses as pending_garbage, and the lazy
            // watch removal during subsequent search_propagate leaves those clauses
            // without watches. Drain them now before further inprocessing.
            self.drain_all_pending_garbage();
            let probe_found_failed = self.inproc.prober.stats().failed > failed_before;
            if probe_found_failed {
                // Post-probe: probing_mode already cleared — search variant.
                // Re-propagate any units derived from failed literals.
                if let Some(conflict_ref) = self.search_propagate() {
                    self.record_level0_conflict_chain(conflict_ref);
                    return true;
                }
            }

            // CaDiCaL re-runs decompose after probing (probe.cpp:940-941).
            // Failed literal units produce new binary implications for SCC.
            // Gated by should_decompose() to respect growing backoff (#7480 D3).
            // Giant bail (dense-band fix): THIS is the site that bypassed
            // skip_congruence_inproc and paid the measured 2,760ms of
            // O(total_literals) decompose re-runs on 0ec8c5e9's 21M-clause
            // arena when DEFAULT-ON AUTO armed decompose without the probe
            // ever running (>8M-clause instances skip the preprocess probe
            // block, whose not-worthy bail is AUTO's only disarm). Below the
            // 8M cap (all 7 sparse flips) behavior is unchanged.
            let should_decompose = self.should_decompose();
            if should_decompose {
                self.stats
                    .record_inprocessing_attempt(DiagnosticPass::Decompose);
            }
            if probe_found_failed && should_decompose && !auto_giant_decompose_rerun_bail {
                self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
                self.run_timed_diagnostic_inprocessing_pass(
                    DiagnosticPass::Decompose,
                    Self::decompose,
                );
                passes_run.push("decompose");
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }
        // BISECT: targeted validation after probe
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after probe");

        // Intree probing: BFS tree-structured probe (CMS intree.cpp, #8169).
        // Runs after sequential probing for complementary coverage:
        // sequential probing covers root literals individually, intree covers
        // the binary implication tree structure more efficiently.
        // Gated by the same probe schedule — both fire in the same round.
        // Skip on large dense formulas (#8084): intree's O(vars) root-finding
        // scan + O(watch_lists) BFS adds overhead without proportional benefit
        // when the formula is too dense for probing to find useful failed lits.
        //
        // LRAT mode: intree_probe() collects LRAT hints at decision_level==1
        // via collect_probe_conflict_lrat_hints (same as regular probing).
        // Deeper levels use TrustedTransform fallback. Re-enabled per #8382.
        if self.inproc_ctrl.probe.enabled {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Probe);
        }
        if self.inproc_ctrl.probe.enabled && !skip_dense_inprocessing {
            if self.run_intree_inprocessing_pass() {
                return true;
            }
            passes_run.push("intree");
            // Drain deferred HBR subsumption deletions from intree probing (#8186).
            // intree_probe() uses probe_propagate() (PROBE mode BCP) which can
            // trigger HBR subsumption, marking clauses as pending garbage. Same
            // pattern as the drain after regular probe() above.
            self.drain_all_pending_garbage();
            if self.propagate_check_unsat() {
                return true;
            }
        }

        // Congruence closure: detect equivalent variables via gate structure.
        // Runs before decompose so that gate equivalences feed into SCC.
        // CaDiCaL: `if (extract_gates(true)) decompose();` — congruence only
        // adds binary equivalence clauses; decompose handles all clause rewriting.
        // Guard: congruence REQUIRES decompose to consume its equivalences.
        // Without decompose, congruence binary clauses remain unsubstituted
        // and BVE may eliminate variables with active equivalence binaries,
        // causing reconstruction to produce invalid models (#5752, #5937).
        // Regression timeline: b5f8a5234 removed this guard → FlatZinc accap
        // returned false UNSAT; 3e7738b95 restored it.
        let mut congruence_found_equivalences = false;
        let should_congruence = self.should_congruence();
        if should_congruence {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Congruence);
        }
        if self.inproc_ctrl.gate.enabled
            && should_congruence
            && self.inproc_ctrl.decompose.enabled
            && !skip_gate_dependent_passes
            && !skip_congruence_inproc
        {
            // congruence: deletion-only (only adds binary clauses, no structural modification)
            congruence_found_equivalences = self.run_timed_diagnostic_inprocessing_pass(
                DiagnosticPass::Congruence,
                Self::congruence,
            );
            passes_run.push("congruence");
            if self.propagate_check_unsat() {
                return true;
            }
            // (#8450) CaDiCaL-style delay for unproductive congruence:
            // CaDiCaL uses congruence_delay.bump_delay() which increments
            // a skip counter — it NEVER permanently disables congruence.
            // Previously (#8361) AY permanently disabled congruence after
            // one unproductive call. This was too aggressive: on hard
            // industrial formulas, congruence equivalences may emerge only
            // after BVE/vivify simplify the clause structure. The growing
            // backoff in congruence() already handles unproductive rounds
            // (2x exponential backoff up to CONGRUENCE_MAX_INTERVAL=64K).
            // No permanent disable needed.
        } else if should_congruence
            && (skip_gate_dependent_passes
                || skip_congruence_inproc
                || !self.inproc_ctrl.decompose.enabled
                || !self.inproc_ctrl.gate.enabled)
        {
            // Skipped: use growing backoff so we don't re-check quickly (#7135).
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                2,
                1,
                CONGRUENCE_MAX_INTERVAL,
            );
        }

        // Decompose: SCC-based equivalent literal substitution.
        // CaDiCaL pattern (internal.cpp:767): `if (extract_gates(true)) decompose();`
        // When congruence found equivalences AND decompose is enabled, decompose
        // runs to rewrite all clauses using the binary equivalences. Without this,
        // reason-protected clauses retain pre-substitution literals (#5237).
        // Decompose stays disabled in proof modes until proof emission and
        // final model reconstruction are both safe.
        let should_decompose = self.should_decompose();
        if should_decompose || (congruence_found_equivalences && self.inproc_ctrl.decompose.enabled)
        {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Decompose);
        }
        if !skip_congruence_inproc
            && (should_decompose
                || (congruence_found_equivalences && self.inproc_ctrl.decompose.enabled))
        {
            self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Decompose, Self::decompose);
            passes_run.push("decompose");
            if self.propagate_check_unsat() {
                return true;
            }
        }

        // BISECT: targeted validation after congruence + decompose-2
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after congruence+decompose-2");

        // The Fmla LRAT decompose admission route is proof-only and dry-run only.
        // Run it after HTR, probe, intree, and congruence have had a chance to
        // add implication edges or level-0 consequences. On FmlaEquivChain the
        // early post-HTR slot produced no SCC substitutions; this later slot
        // preserves the fail-closed clamp while testing the richer implication
        // graph before the rest of the round mutates clause structure further.
        self.run_fmla_decompose_lrat_preflight_route(&mut passes_run);

        if self.is_interrupted() {
            return false;
        }

        // Binary-clause backbone detection (1st call).
        // CaDiCaL probe.cpp:945: `binary_clauses_backbone()` after extract_gates+decompose.
        // Lightweight binary-only propagation — no OTFS/JIT/chrono suppression needed.
        let should_backbone = self.should_backbone();
        if should_backbone {
            backbone_cooldown_eligible_this_round = true;
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Backbone);
        }
        if should_backbone
            && !skip_expensive_equivalence_passes
            && self.cold.backbone_phases < BACKBONE_MAX_ROUNDS
        {
            let backbone_yield_before = self.inprocessing_yield_signal(DiagnosticPass::Backbone);
            backbone_binary_ran_this_round = true;
            let backbone_binary_found = self.run_timed_diagnostic_inprocessing_pass(
                DiagnosticPass::Backbone,
                Self::backbone_binary,
            );
            if self.inprocessing_yield_signal(DiagnosticPass::Backbone) > backbone_yield_before {
                backbone_productive_this_round = true;
            }
            if backbone_binary_found {
                passes_run.push("backbone_binary");
                if self.has_empty_clause {
                    return true;
                }
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }

        // Elimination back-half: BVE interleaved with subsumption/BCE/CCE
        // (CaDiCaL elim.cpp:1093-1098 cascade), factor, standalone BCE/CCE,
        // condition, transred, sweep + decompose, compact.
        if self.run_elimination_passes(
            &mut passes_run,
            skip_gate_dependent_passes,
            skip_expensive_equivalence_passes,
            skip_subsume_inproc,
            round_start,
            round_start_ticks,
        ) {
            return true;
        }
        // BISECT: targeted validation after elimination
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after elimination");

        // Backbone computation: identify literals fixed in every model.
        // Initial implementation uses bounded assumption-based probing, so run
        // it after the elimination block has simplified the formula and before
        // vivification strengthens clauses against the updated root assignment.
        // CaDiCaL enforces a round limit: `backbonemaxrounds = 1000` (options.hpp:30).
        // Skip backbone entirely once the phase count exceeds this limit.
        //
        // Wall-clock guard (#8448): skip backbone if this inprocessing round
        // has already consumed the wall-clock budget. Backbone bounded-CDCL
        // is the most expensive single technique (up to 200ms per call).
        let skip_wall_clock = self.inproc_round_over_budget(round_start, round_start_ticks);
        let should_backbone = self.should_backbone();
        let bounded_backbone_allowed = !self.bounded_backbone_zero_decompose_backoff_enabled
            || self.num_conflicts >= self.cold.next_bounded_backbone_conflict;
        if should_backbone {
            backbone_cooldown_eligible_this_round = true;
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Backbone);
        }
        if should_backbone
            && bounded_backbone_allowed
            && !skip_expensive_equivalence_passes
            && self.cold.backbone_phases < BACKBONE_MAX_ROUNDS
            && !skip_wall_clock
            && self.cold.backbone_consecutive_empty < BACKBONE_STALL_LIMIT
        {
            let backbone_yield_before = self.inprocessing_yield_signal(DiagnosticPass::Backbone);
            let backbone_time_before = self.stats.inprocessing_time_ns
                [solver_stats::inprocessing_timing_index(DiagnosticPass::Backbone).unwrap()];
            let decompose_index =
                solver_stats::inprocessing_timing_index(DiagnosticPass::Decompose).unwrap();
            let bb_found = self
                .run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Backbone, Self::backbone);
            let backbone_time_after = self.stats.inprocessing_time_ns
                [solver_stats::inprocessing_timing_index(DiagnosticPass::Backbone).unwrap()];
            let bounded_backbone_ms =
                backbone_time_after.saturating_sub(backbone_time_before) / 1_000_000;
            let bounded_backbone_yield_delta = self
                .inprocessing_yield_signal(DiagnosticPass::Backbone)
                .saturating_sub(backbone_yield_before);
            self.stats.bounded_backbone_runs = self.stats.bounded_backbone_runs.saturating_add(1);
            self.stats.bounded_backbone_ms = self
                .stats
                .bounded_backbone_ms
                .saturating_add(bounded_backbone_ms);
            if bb_found || bounded_backbone_yield_delta > 0 {
                self.stats.bounded_backbone_yields =
                    self.stats.bounded_backbone_yields.saturating_add(1);
            }
            let bounded_path_productive = bb_found || bounded_backbone_yield_delta > 0;
            backbone_productive_this_round |= bounded_path_productive;
            passes_run.push("backbone");
            let round_decompose_yields = self.stats.inprocessing_pass_yields[decompose_index]
                .saturating_sub(pass_yield_baseline[decompose_index]);
            let bounded_units = bounded_backbone_yield_delta.max(u64::from(bb_found));
            let bounded_ms_per_unit = bounded_backbone_ms / bounded_units.max(1);
            if self.bounded_backbone_zero_decompose_backoff_enabled
                && round_decompose_yields == 0
                && bounded_ms_per_unit >= BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_MIN_MS_PER_UNIT
            {
                let bounded_next = self.num_conflicts.saturating_add(BACKBONE_INTERVAL);
                if self.cold.next_bounded_backbone_conflict < bounded_next {
                    self.cold.next_bounded_backbone_conflict = bounded_next;
                }
                self.stats.bounded_backbone_backoff_triggers = self
                    .stats
                    .bounded_backbone_backoff_triggers
                    .saturating_add(1);
            }
            if backbone_productive_this_round {
                // Productive: reset stall counter and base interval. Binary
                // backbone productivity in this round counts here because the
                // binary and bounded paths currently share one control row.
                self.cold.backbone_consecutive_empty = 0;
                self.inproc_ctrl
                    .backbone
                    .reschedule(self.num_conflicts, BACKBONE_INTERVAL);
                if bb_found {
                    if self.has_empty_clause {
                        return true;
                    }
                    if self.propagate_check_unsat() {
                        return true;
                    }
                }
            } else {
                // Unproductive: increment stall counter and grow backoff.
                // (#8448) Re-added stall limit after #8450 removed it:
                // growing backoff alone is insufficient because backbone
                // rounds still fire (just less frequently) and each round
                // costs 200-300ms on medium formulas. On mp1-klieber (30K
                // vars), 810ms is wasted on backbone with 0 units found.
                // After BACKBONE_STALL_LIMIT (2) consecutive empty rounds,
                // backbone is permanently disabled for the instance.
                self.cold.backbone_consecutive_empty += 1;
                self.inproc_ctrl.backbone.reschedule_growing(
                    self.num_conflicts,
                    BACKBONE_INTERVAL,
                    3,
                    2,
                    BACKBONE_MAX_INTERVAL,
                );
            }
        } else if should_backbone && backbone_productive_this_round {
            self.cold.backbone_consecutive_empty = 0;
            self.inproc_ctrl
                .backbone
                .reschedule(self.num_conflicts, BACKBONE_INTERVAL);
        } else if should_backbone && skip_expensive_equivalence_passes {
            self.inproc_ctrl.backbone.reschedule_growing(
                self.num_conflicts,
                BACKBONE_INTERVAL,
                3,
                2,
                BACKBONE_MAX_INTERVAL,
            );
        }

        // BISECT: targeted validation after backbone
        #[cfg(debug_assertions)]
        self.bisect_validate_watches("after backbone");

        // CaDiCaL probe.cpp:949: vivify runs after sweep (resets watches).
        // Vivify strengthens clauses by re-propagating their literals.
        // Running after sweep means sweep equivalences are substituted first,
        // giving vivify a cleaner formula to work with.
        // Vivification exempt from density guard (#8360, #8362): it only
        // strengthens/shortens clauses, never inflates. On small dense formulas,
        // vivification is the critical technique that REDUCES density. Kissat
        // has no density guard for vivification.
        //
        // Wall-clock guard (#8448): skip vivify if this inprocessing round
        // has already consumed the wall-clock budget. On ecarev-110 (741K
        // clauses), vivify takes 1437ms per round -- with decompose (1104ms)
        // and BVE (1342ms) already consuming 2.4s, vivify pushes the round
        // to 3.9s. Skipping it when over-budget saves ~1.4s per round.
        let vivify_wall_budget_exceeded =
            self.inproc_round_over_budget(round_start, round_start_ticks);
        let should_vivify = self.should_vivify();
        if should_vivify {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Vivify);
        }
        if should_vivify && !vivify_wall_budget_exceeded {
            self.jit_invalidate_for_structural_pass(); // vivify: structural (#8128)
            let vivify_yield_before = self.inprocessing_yield_signal(DiagnosticPass::Vivify);
            if self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Vivify, Self::vivify) {
                return true;
            }
            let vivify_made_progress =
                self.inprocessing_yield_signal(DiagnosticPass::Vivify) > vivify_yield_before;
            passes_run.push("vivify");

            // Post-vivification subsumption (#7393, #8134, #8135): vivification
            // marks strengthened/deleted clause variables dirty. A follow-up
            // subsumption pass can exploit shorter clauses from vivification
            // to subsume other clauses. CaDiCaL achieves this via mark_added
            // in vivify_strengthen and new_clause_as, then the next subsume
            // round picks up the dirty variables.
            //
            // On small dense formulas (e.g. clique_n2_k10: 180 vars, 3160 cls),
            // post-vivify subsumption is especially critical: vivification
            // shortens many clauses in each round, and immediate subsumption
            // removes clauses that the shorter vivified clauses now subsume.
            // On FmlaEquivChain, this cascade creates a 1.91x speedup.
            let post_vivify_subsume_wall_budget_exceeded =
                self.inproc_round_over_budget(round_start, round_start_ticks);
            let post_vivify_subsume_due = !self.use_large_sparse_subsume_idle_cooldown()
                || vivify_made_progress
                || self.should_subsume();
            if self.inproc_ctrl.subsume.enabled
                && !skip_subsume_inproc
                && !post_vivify_subsume_wall_budget_exceeded
                && post_vivify_subsume_due
            {
                self.stats
                    .record_inprocessing_attempt(DiagnosticPass::Subsume);
                self.jit_invalidate_for_structural_pass(); // subsume: structural (#8128)
                self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Subsume, Self::subsume);
                passes_run.push("subsume");
                self.cold.subsume_ran_since_bve = true; // #8502: signal pre-BVE guard
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }

        // Binary-clause backbone detection (2nd call).
        // CaDiCaL probe.cpp:951: `binary_clauses_backbone()` after vivify+transred.
        // Vivification may shorten clauses to binary, creating new backbone
        // propagation opportunities. This second pass catches those. Use the
        // round-local "binary ran" bit as an admission ticket so a same-round
        // bounded-CDCL empty backoff cannot suppress the cheap post-vivify
        // binary pass after the first binary pass already passed the gate.
        // The admission ticket is runtime-gated so A/B runs can restore the
        // legacy post-vivify gate of `should_backbone` only.
        let should_backbone = self.should_backbone();
        let should_backbone_binary = should_backbone
            || (self.backbone_post_vivify_binary_admission_enabled()
                && backbone_binary_ran_this_round);
        if should_backbone_binary {
            if should_backbone {
                backbone_cooldown_eligible_this_round = true;
            }
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Backbone);
        }
        if should_backbone_binary
            && !skip_expensive_equivalence_passes
            && self.cold.backbone_phases < BACKBONE_MAX_ROUNDS
        {
            let backbone_yield_before = self.inprocessing_yield_signal(DiagnosticPass::Backbone);
            let backbone_binary_found = self.run_timed_diagnostic_inprocessing_pass(
                DiagnosticPass::Backbone,
                Self::backbone_binary,
            );
            if self.inprocessing_yield_signal(DiagnosticPass::Backbone) > backbone_yield_before {
                self.cold.backbone_consecutive_empty = 0;
                self.inproc_ctrl
                    .backbone
                    .reschedule(self.num_conflicts, BACKBONE_INTERVAL);
            }
            if backbone_binary_found {
                passes_run.push("backbone_binary");
                if self.has_empty_clause {
                    return true;
                }
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }

        // Postcondition: inprocessing must leave the solver at level 0
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: run_restart_inprocessing exiting at decision level {}",
            self.decision_level,
        );
        // Trail must be fully propagated after inprocessing
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: unpropagated literals after inprocessing (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        #[cfg(debug_assertions)]
        self.validate_watch_invariants();

        // Reverse watch validation (#8401): check that every watch entry
        // points to a clause whose watched positions match. Forward
        // validation (above) checks clause->watch; this checks watch->clause.
        #[cfg(debug_assertions)]
        self.validate_watches_reverse("inprocessing exit");

        // #5012 Family A: reason clause protection invariant.
        // Every trail reason must reference a live clause containing the variable.
        // CaDiCaL equivalent: elim.cpp:440 post-condition.
        #[cfg(debug_assertions)]
        self.validate_reason_clause_integrity();

        // #5012 Family B: proof system coherence invariant.
        // Forward checker and solver clause DB must agree on live set.
        // CaDiCaL equivalent: checker.cpp aggregate consistency checks.
        #[cfg(debug_assertions)]
        self.validate_proof_coherence();

        // #5012 Family C: reconstruction stack coherence invariant.
        // Every witness literal must appear in its clause.
        // CaDiCaL equivalent: external.cpp:208-230 validity check.
        #[cfg(debug_assertions)]
        self.validate_reconstruction_stack();

        // Always-on release-mode soundness guards (#4994):

        // Fix 1: Proof I/O error check. ProofOutput::has_io_error() exists in
        // release builds (bool field on DRAT/LRAT writer). Catches truncated or
        // corrupted proofs from disk-full or broken-pipe mid-solve. O(1) cost.
        if let Some(ref manager) = self.proof_manager {
            assert!(
                !manager.has_inprocessing_boundary_error(),
                "BUG: proof I/O error detected at inprocessing boundary"
            );
        }

        // Fix 2: Pending-garbage drain check. pending_garbage_count is a u32
        // on Solver (not cfg(debug_assertions)). Non-zero at inprocessing exit
        // means BCP will encounter stale clauses — a reliability bug. O(1) cost.
        assert_eq!(
            self.pending_garbage_count, 0,
            "BUG [Family A]: {} pending-garbage clauses at inprocessing exit",
            self.pending_garbage_count,
        );

        // ── Per-round overhead computation (#8099) ────────────────────────
        // Infrastructure overhead = total round wall time - sum of individual
        // pass times recorded by run_timed_diagnostic_inprocessing_pass.
        let round_elapsed_ns = round_start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        let pass_time_delta_ns: u64 = self
            .stats
            .inprocessing_time_ns
            .iter()
            .zip(pass_time_baseline.iter())
            .map(|(now, before)| now.saturating_sub(*before))
            .sum();
        let overhead_ns = round_elapsed_ns.saturating_sub(pass_time_delta_ns);
        self.cold.last_inprocessing_overhead_ms = overhead_ns as f64 / 1_000_000.0;

        // Update per-round stats (#8099).
        self.stats.inprocessing_rounds += 1;
        let clauses_after = self.num_clauses();
        let round_simplifications = clauses_before.saturating_sub(clauses_after) as u64
            + self
                .stats
                .preprocess_level0_literals_removed
                .saturating_sub(preproc_lits_before)
            + self
                .stats
                .preprocess_level0_satisfied_deleted
                .saturating_sub(preproc_sat_before);
        self.stats.inprocessing_simplifications = self
            .stats
            .inprocessing_simplifications
            .saturating_add(round_simplifications);
        let round_pass_yields: u64 = self
            .stats
            .inprocessing_pass_yields
            .iter()
            .zip(pass_yield_baseline.iter())
            .map(|(now, before)| now.saturating_sub(*before))
            .sum();
        let backbone_or_decompose_yield = self.inprocessing_yield_productivity_rescue_enabled
            && [DiagnosticPass::Backbone, DiagnosticPass::Decompose]
                .into_iter()
                .any(|pass| {
                    solver_stats::inprocessing_timing_index(pass).is_some_and(|index| {
                        self.stats.inprocessing_pass_yields[index] > pass_yield_baseline[index]
                    })
                });
        let (lrat_clamped_bve_due, lrat_clamped_factor_due) =
            self.lrat_proof_clamped_elimination_due();
        if lrat_clamped_bve_due {
            self.stats.inprocessing_lrat_clamped_bve_due_rounds = self
                .stats
                .inprocessing_lrat_clamped_bve_due_rounds
                .saturating_add(1);
        }
        if lrat_clamped_factor_due {
            self.stats.inprocessing_lrat_clamped_factor_due_rounds = self
                .stats
                .inprocessing_lrat_clamped_factor_due_rounds
                .saturating_add(1);
        }
        // Pass-local yields such as LRAT-safe probe units still leave the
        // destructive BVE/factor opportunity proof-clamped. Rescue only the
        // probe cadence on zero-simplification rounds; never reopen BVE/factor.
        let lrat_probe_rescue_due = self.lrat_proof_clamp_probe_rescue_enabled
            && self.inproc_ctrl.probe.enabled
            && (lrat_clamped_bve_due || lrat_clamped_factor_due)
            && round_simplifications == 0;
        if lrat_probe_rescue_due {
            self.stats.inprocessing_lrat_probe_rescue_rounds = self
                .stats
                .inprocessing_lrat_probe_rescue_rounds
                .saturating_add(1);
        }

        // ── Diminishing-returns tracking (#8134) ─────────────────────────
        // Track per-round productivity. A round is "low productivity" if its
        // simplification count is less than 1% of active clauses. Consecutive
        // low-productivity rounds trigger wider inprocessing intervals.
        self.cold.last_round_simplifications = round_simplifications;
        let productivity_threshold = (active_clauses as u64) / 100; // 1%
        let yield_rescued_low_productivity_round =
            backbone_or_decompose_yield && round_simplifications <= productivity_threshold;
        let lrat_probe_rescued_low_productivity_round =
            lrat_probe_rescue_due && round_simplifications <= productivity_threshold;
        if round_simplifications <= productivity_threshold
            && !backbone_or_decompose_yield
            && !lrat_probe_rescued_low_productivity_round
        {
            self.cold.consecutive_low_productivity_rounds = self
                .cold
                .consecutive_low_productivity_rounds
                .saturating_add(1);
        } else {
            // Productive round: reset the counter.
            self.cold.consecutive_low_productivity_rounds = 0;
        }

        tracing::debug!(
            num_clauses = clauses_after,
            num_vars = self.num_vars,
            trail_len = self.trail.len(),
            overhead_ms = format_args!("{:.2}", self.cold.last_inprocessing_overhead_ms),
            round = self.stats.inprocessing_rounds,
            simplifications = round_simplifications,
            low_prod_streak = self.cold.consecutive_low_productivity_rounds,
            "inprocessing: round complete"
        );

        // Emit per-round diagnostic summary (#4674, #4781).
        // Uses passes_run (actually executed) instead of collect_enabled_passes().
        let telemetry = crate::diagnostic_trace::InprocessingRoundTelemetry {
            bcp_blocker_fastpath_hits: self
                .stats
                .bcp_blocker_fastpath_hits
                .saturating_sub(bcp_blocker_before),
            bcp_binary_path_hits: self
                .stats
                .bcp_binary_path_hits
                .saturating_sub(bcp_binary_before),
            jumped_reasons: self
                .stats
                .jumped_reasons
                .saturating_sub(jumped_reasons_before),
            bcp_replacement_scan_steps: self
                .stats
                .bcp_replacement_scan_steps
                .saturating_sub(bcp_scan_before),
            preprocess_level0_literals_removed: self
                .stats
                .preprocess_level0_literals_removed
                .saturating_sub(preproc_lits_before),
            preprocess_level0_satisfied_deleted: self
                .stats
                .preprocess_level0_satisfied_deleted
                .saturating_sub(preproc_sat_before),
        };
        self.emit_diagnostic_inprocessing_round(
            clauses_before,
            clauses_after,
            &passes_run,
            &telemetry,
        );

        // CaDiCaL probe.cpp:987: last.inprobe.reductions = stats.reductions
        self.cold.last_inprobe_reduction = self.cold.num_reductions;

        // CaDiCaL probe.cpp:979-981: update inprobe conflict limit.
        // delta = 10 * inprobeint * log10(phases + 9)
        // With INPROBE_INTERVAL=100: phase 0 → delta=954, phase 91 → delta=2000.
        // Reduced from 25x to 10x (#8466): Kissat uses probeint=100 with
        // effort-based scaling, probing ~2.5x more frequently than AY's
        // previous 25x multiplier. 10x brings AY closer to Kissat's probe
        // frequency, improving FmlaEquivChain, stable, and battleship solves.
        // Logarithmic growth still widens the inprobe interval as search
        // progresses, reducing per-round overhead on large residuals (#7135).
        //
        // On large residuals (>3M clauses), the O(clauses) setup cost of even
        // lightweight passes (watch sorting, candidate building, occurrence
        // lists) dominates per-round time. Scale the interval by
        // log10(clauses/1M) to reduce round frequency proportionally (#7135).
        self.cold.inprobe_phases += 1;
        let log_factor = ((self.cold.inprobe_phases + 9) as f64).log10();
        // A/B knob (campaign): AY_INPROBE_MULT scales the inprocessing interval
        // (lower = more frequent inprocessing). Default 10.0 (current behavior),
        // cached per process.
        let inprobe_mult = {
            use std::sync::OnceLock;
            static M: OnceLock<f64> = OnceLock::new();
            *M.get_or_init(|| {
                std::env::var("AY_INPROBE_MULT")
                    .ok()
                    .and_then(|s| s.parse::<f64>().ok())
                    .filter(|m| *m > 0.0 && m.is_finite())
                    .unwrap_or(10.0)
            })
        };
        let base_delta = (inprobe_mult * INPROBE_INTERVAL as f64 * log_factor) as u64;
        // Scale interval on large formulas using sqrt of (clauses / 1M).
        // Linear scaling (from #7135) was too aggressive: 4.7M clauses → 4.7x,
        // throttling beneficial subsumption/BVE on FmlaEquivChain (#7279).
        // sqrt scaling: 3M → 1.7x, 5M → 2.2x, 10M → 3.2x. This still
        // compensates for O(clauses) setup cost while allowing more frequent
        // inprocessing than the linear version.
        let active_count = self.arena.active_clause_count();
        let clause_scale = if active_count > PREPROCESS_EXPENSIVE_MAX_CLAUSES {
            (active_count as f64 / 1_000_000.0).sqrt().max(1.0)
        } else {
            1.0
        };
        // Diminishing-returns scaling (#8134, #8361): when consecutive
        // low-productivity rounds accumulate, widen the interval exponentially.
        // Each streak round adds a 3.0x multiplier (#8361, raised from 2.0x).
        // Streak 0: 1.0x, 1: 3.0x, 2: 9.0x, 3: 27.0x, 4: 81.0x.
        // With 3.0x backoff, unproductive rounds are skipped sooner, reducing
        // total inprocessing rounds from ~7 to ~4-5 on medium instances.
        // A productive round resets the streak to 0.
        let productivity_scale = if lrat_probe_rescue_due {
            1.0
        } else if self.cold.consecutive_low_productivity_rounds > 0 {
            3.0_f64.powi(self.cold.consecutive_low_productivity_rounds as i32)
        } else {
            1.0
        };
        let lrat_zero_yield_scale = if lrat_probe_rescue_due {
            1.0
        } else if self.cold.lrat_enabled
            && self.proof_manager.is_some()
            && round_simplifications == 0
            && round_pass_yields == 0
            && !passes_run.is_empty()
        {
            LRAT_ZERO_YIELD_INPROBE_COOLDOWN_SCALE
        } else {
            1.0
        };
        let delta =
            (base_delta as f64 * clause_scale * productivity_scale * lrat_zero_yield_scale) as u64;
        let delta = delta.max(INPROBE_INTERVAL);
        let delta = if lrat_probe_rescue_due {
            delta.min(LRAT_PROOF_CLAMP_PROBE_RESCUE_INTERVAL)
        } else {
            delta
        };
        self.cold.next_inprobe_conflict = self.total_conflicts().saturating_add(delta);
        if lrat_probe_rescue_due {
            self.inproc_ctrl.probe.reschedule(self.num_conflicts, delta);
        }
        if self.inprocessing_yield_rescue_backbone_cooldown_enabled
            && yield_rescued_low_productivity_round
            && backbone_cooldown_eligible_this_round
            && self.inproc_ctrl.backbone.enabled
        {
            let cooldown_next = self
                .num_conflicts
                .saturating_add(YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL);
            if self.inproc_ctrl.backbone.next_conflict < cooldown_next {
                self.inproc_ctrl
                    .backbone
                    .reschedule(self.num_conflicts, YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL);
                self.stats
                    .inprocessing_yield_rescue_backbone_cooldown_rounds = self
                    .stats
                    .inprocessing_yield_rescue_backbone_cooldown_rounds
                    .saturating_add(1);
            }
        }

        // CaDiCaL reduce.cpp:250: use dynamic irredundant count for reduce
        // interval scaling. O(1) via incremental counter (#7476).
        self.num_original_clauses = self.arena.irredundant_count();
        debug_assert_eq!(
            self.num_original_clauses,
            self.arena
                .active_indices()
                .filter(|&idx| !self.arena.is_learned(idx))
                .count(),
            "BUG: irredundant_count drift (#7476)"
        );

        // Notify programmatic observer of each inprocessing technique that ran (#8155).
        if self.has_observer() && !passes_run.is_empty() {
            for &pass_name in &passes_run {
                if let Some(technique) =
                    crate::observer::InprocessingTechnique::from_pass_name(pass_name)
                {
                    self.notify_observer_inprocessing(technique, round_simplifications);
                }
            }
        }

        // Invalidate the uniform formula cache after any inprocessing round
        // that ran passes (#7905). Passes like BVE, subsumption, vivification,
        // decompose, and factorization can add/delete/strengthen irredundant
        // clauses, changing the uniform formula property.
        if !passes_run.is_empty() {
            self.invalidate_uniform_formula_cache();
        }

        // ── JIT recompilation: conditional rebuild after inprocessing (#8128, #8134, #8202) ──
        //
        // Deferral optimization (#8134): During initial rapid inprocessing
        // (first 2 BVE phases), if the next round is imminent (delta < 500
        // conflicts), skip recompilation because the next round will likely
        // re-invalidate JIT.  On FmlaEquivChain this saves ~400ms by avoiding
        // 10+ unnecessary 35-50ms recompilations.  After that, always
        // recompile so JIT survives sustained search.
        {
            let needs_recompile = had_compiled_formula && !self.has_compiled_formula();
            let next_round_imminent = delta < 500;

            if needs_recompile && next_round_imminent && self.cold.bve_phases < 2 {
                // Defer during initial rapid inprocessing.
                self.stats.jit_recompilations_skipped += 1;
                tracing::debug!(
                    next_delta = delta,
                    bve_phases = self.cold.bve_phases,
                    "jit: deferred recompilation (initial rapid inprocessing)"
                );
            } else if !passes_run.is_empty() {
                // Delegate to the shared recompilation helper (#8202).
                // Handles: deletion-only skip, delta/full recompile, watch
                // detachment, jit_qhead sync, and the safety-net reattach.
                self.jit_recompile_after_inprocessing(had_compiled_formula);
            }

            // BCP JIT watch reattachment safety net removed (#8517).
        }

        false
    }
}
