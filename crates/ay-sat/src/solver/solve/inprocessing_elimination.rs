// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing elimination back-half:
//! BVE interleaved with subsumption/BCE/CCE, factor, standalone BCE/CCE,
//! condition, transred, sweep, compact.

use super::super::*;

const POST_FACTOR_CIRCUIT_BVE_MAX_VARS: usize = 8_192;
const POST_FACTOR_CIRCUIT_BVE_MAX_IRRED_CLAUSES: usize = 100_000;
const POST_FACTOR_CIRCUIT_BVE_MIN_AND_XOR_GATES: u64 = 128;

impl Solver {
    /// Run the elimination back half of inprocessing.
    ///
    /// Returns `true` if UNSAT was derived. Appends pass names to `passes_run`.
    pub(in crate::solver) fn run_elimination_passes(
        &mut self,
        passes_run: &mut Vec<&'static str>,
        skip_gate_dependent_passes: bool,
        skip_expensive_equivalence_passes: bool,
        skip_subsume_inproc: bool,
        round_start: ay_core::time::Instant,
        round_start_ticks: u64,
    ) -> bool {
        if self.use_official_main_lrat_elimination_fast_path() {
            return self.run_official_main_lrat_elimination_passes(
                passes_run,
                skip_expensive_equivalence_passes,
            );
        }

        // Post-collapse BVE eligibility re-derivation (--sat-no-bve-post-collapse,
        // default ON since 2026-07-10 wf_55735963; =0 kill-switch): on the
        // huge substitution-heavy instances the
        // congruence/decompose collapse frequently completes during
        // INPROCESSING rounds — the 2s large-formula preprocess deadline
        // aborts preprocess() right after the congruence probe, before its
        // own decompose step, so the preprocess-time arming hook never sees
        // the collapsed state (measured on ebbda8d9: 199,888 probe equivs in
        // preprocess, 403,016 substitutions landing later). Re-derive here at
        // the elimination-phase entry, which runs AFTER the schedule's
        // equivalence front half, so the first round after the collapse arms
        // BVE. Fail-closed exactly like the preprocess hook: the unlock
        // predicate refuses LRAT/incremental/AY_SAT_NO_BVE and the proof
        // overrides are re-enforced after arming. Inert when the knob is off
        // (cheap OnceLock env check first) or the collapse merged nothing.
        if !self.inproc_ctrl.bve.enabled && self.bve_post_collapse_unlock_active() {
            self.inproc_ctrl.bve.enabled = true;
            self.enforce_inprocessing_proof_overrides();
            if ay_core::misc_cli_flags().ab_subst_stats {
                eprintln!(
                    "AB_BVE_POST_COLLAPSE: armed bve={} in inprocessing (num_vars={} active={} removed={})",
                    self.inproc_ctrl.bve.enabled,
                    self.num_vars,
                    self.var_lifecycle.count_active(),
                    self.var_lifecycle.count_removed()
                );
            }
        }

        // ── Interleaved elimination phase (CaDiCaL elim.cpp:1050-1109) ──
        //
        // CaDiCaL runs BVE as a multi-round phase interleaved with subsumption
        // and BCE between rounds. The cascade effect is critical: BVE produces
        // resolvents → subsumption simplifies/removes them → creates new BVE
        // candidates → repeat. Without interleaving, each technique reaches
        // only a local fixpoint within its own round.
        // Density-based BVE skip for very large dense formulas (#8136).
        let active_cls_for_bve = self.arena.active_clause_count();
        let active_vars_for_bve = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let bve_density = if active_vars_for_bve > 0 {
            active_cls_for_bve as f64 / active_vars_for_bve as f64
        } else {
            0.0
        };
        // Dense-skip elimination lift (kill-switch AY_AB_DENSE_SKIP_LIFT=0):
        // raised clause arm (2M -> 3M) for the BVE dense skip only;
        // decompose/congruence gates keep the original predicate (see
        // skip_dense_formula_elim for the d421913d measurement).
        let skip_bve_dense = config_preprocess_policy::PreprocessPolicy::skip_dense_formula_elim(
            active_cls_for_bve,
            bve_density,
        );
        // Proportional BVE+transred time guard (#8078): skip BVE and transred
        // when their cumulative time exceeds 15% of total search time.
        // CaDiCaL bounds inprocessing via tick-proportional effort; AY's occ
        // list rebuild cost is not metered by ticks. On FmlaEquivChain, BVE
        // consumed 41% of search time (net +1673 clauses) and transred removed
        // 36 binary clauses causing 53% more conflicts. This guard caps
        // BVE+transred overhead while allowing beneficial passes (vivify,
        // subsumption, congruence, probe) to continue.
        let skip_inproc_proportional = self.bve_transred_proportional_guard_exceeded();
        let mut bce_ran_in_elim_phase = false;
        let mut cce_ran_in_elim_phase = false;
        // Wall-clock guard (#8448): skip BVE if this inprocessing round has
        // already consumed the wall-clock budget. BVE is the most expensive
        // elimination technique (occ list rebuild + resolution) and can
        // consume 1-3s on medium formulas like mp1-klieber.
        let bve_wall_budget_exceeded =
            self.inproc_round_over_budget(round_start, round_start_ticks);
        let should_bve = self.should_bve();
        if should_bve
            && !skip_gate_dependent_passes
            && !skip_bve_dense
            && !skip_inproc_proportional
            && !bve_wall_budget_exceeded
        {
            // CaDiCaL elim.cpp:1043-1044: force a subsumption pass before
            // the first BVE round IF no subsumption has run since the last BVE
            // phase. BVE effectiveness depends on a simplified formula —
            // subsumption removes redundant clauses and strengthens others,
            // reducing the occurrence lists that BVE must consider. The
            // conditional guard (#8502) avoids redundant subsumption when the
            // front-half inprocessing schedule already ran subsumption this round.
            if self.inproc_ctrl.subsume.enabled
                && !skip_subsume_inproc
                && !self.cold.subsume_ran_since_bve
                && (!self.use_large_sparse_subsume_idle_cooldown() || self.should_subsume())
            {
                self.stats
                    .record_inprocessing_attempt(DiagnosticPass::Subsume);
                self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Subsume, Self::subsume);
                passes_run.push("subsume");
                if self.has_empty_clause {
                    return true;
                }
            }
            // Reset the flag: BVE is about to run, so the next BVE round
            // should force subsumption again unless subsumption runs in between.
            self.cold.subsume_ran_since_bve = false;

            self.jit_invalidate_for_structural_pass(); // BVE: structural (#8128)
            let clauses_before_elim_phase = self.arena.irredundant_count();

            // CaDiCaL elim.cpp:1046: disconnect watches for the entire
            // elimination phase. BVE uses occurrence lists, subsume_round()
            // uses one-watch occ-lists, BCE uses occurrence lists. None need
            // the 2WL watch graph. Reconnecting once at the end (instead of
            // per-subsumption-round) saves O(clauses) work per interleave
            // iteration — a major win on large formulas like FmlaEquivChain.
            //
            // Watches are NOT cleared (#8093): incremental reconnection after
            // BVE preserves pre-existing watch entries and only attaches watches
            // for new resolvents. Stale binary entries are purged; stale
            // long-clause entries are lazily handled by BCP.
            //
            // The baseline tracks the arena offset from which new (unwatched)
            // clauses begin. It starts at the current arena length and is
            // advanced when instantiate() does a temporary full rebuild (which
            // attaches watches for all active clauses up to that point).
            let mut arena_baseline = self.arena.len(); // #8093: new clauses start here
            self.cold.instantiate_rebuilt_watches = false; // #8093: reset flag
            self.watches_disconnected = true;
            self.cold.disconnected_deletions = 0; // #8093: reset for purge-skip optimization
                                                  // Instantiate gate (lever 2, AY_AB_BVE_INST_GATE — see
                                                  // bve_inst_gate_enabled): stamp a new elimination phase. The
                                                  // interleave loop below calls bve() up to ELIM_INTERLEAVE_ROUNDS
                                                  // times; under the gate only one instantiate per phase runs,
                                                  // bounded by the inprocessing BVE wall.
            self.cold.bve_elim_phase_seq = self.cold.bve_elim_phase_seq.wrapping_add(1);

            let mut elim_derived_unsat = false;
            // (#8448) Wall-clock guard for the inprocessing BVE cascade.
            // On medium formulas like FmlaEquivChain (54K vars, 438K clauses),
            // 3 rounds of BVE+subsumption+BCE+CCE cascade consume 3+s. Cap the
            // cascade at 2s to preserve search time budget. CaDiCaL bounds
            // inprocessing via tick-proportional effort; AY's occ list rebuild
            // cost is not tick-metered, so a wall-clock fallback is needed.
            let elim_wall_start = ay_core::time::Instant::now();
            for elim_round in 0..ELIM_INTERLEAVE_ROUNDS {
                // BVE can derive UNSAT directly (empty resolvent).
                if self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BVE, Self::bve) {
                    elim_derived_unsat = true;
                    break;
                }
                passes_run.push("bve");

                // #8093: If instantiate() ran inside this BVE round, it did a
                // full rebuild_watches() covering all active clauses. Advance
                // the baseline so reconnect_bve_watches only attaches watches
                // for clauses added in subsequent rounds.
                if self.cold.instantiate_rebuilt_watches {
                    arena_baseline = self.arena.len();
                    self.cold.instantiate_rebuilt_watches = false;
                }

                // CaDiCaL defers post-BVE propagation to after the loop
                // (elim.cpp:1134-1138). BVE units are enqueued via enqueue()
                // which sets vals[], so subsequent BVE/subsumption rounds
                // correctly see the unit's truth value. Full BCP propagation
                // (which requires watches) runs once after reconnection.
                if self.has_empty_clause {
                    elim_derived_unsat = true;
                    break;
                }

                if self.is_interrupted() {
                    break;
                }

                // (#8448) Wall-clock guard: stop the BVE cascade after 2s.
                // The first round captures the primary benefit; subsequent
                // rounds have diminishing returns but fixed overhead cost.
                if elim_wall_start.elapsed().as_secs() >= 2 {
                    break;
                }

                // Between BVE rounds: try subsumption and BCE to create new
                // elimination candidates (CaDiCaL elim.cpp:1084-1098).
                // Exit the interleaving loop if neither produces new candidates.
                let marked_before = self.cold.bve_marked;
                let fixed_before = self.fixed_count;

                // Inter-round subsumption: subsume_round() operates without
                // watch management (CaDiCaL subsume_round() pattern). Watches
                // are already disconnected above; reconnection is deferred to
                // after the loop. Propagation is also deferred — subsumption
                // units are on the trail (vals set) and BVE sees them.
                if self.inproc_ctrl.subsume.enabled
                    && !skip_subsume_inproc
                    && (!self.use_large_sparse_subsume_idle_cooldown() || self.should_subsume())
                {
                    self.stats
                        .record_inprocessing_attempt(DiagnosticPass::Subsume);
                    self.run_timed_diagnostic_inprocessing_pass(
                        DiagnosticPass::Subsume,
                        Self::subsume,
                    );
                    passes_run.push("subsume");
                    if self.has_empty_clause {
                        elim_derived_unsat = true;
                        break;
                    }
                }

                // Inter-round BCE: blocked clause removal opens new BVE
                // opportunities (CaDiCaL block() in the interleaved loop).
                if self.inproc_ctrl.bce.enabled && !self.cold.has_been_incremental {
                    self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BCE, Self::bce);
                    passes_run.push("bce");
                    bce_ran_in_elim_phase = true;
                }

                // Inter-round CCE: covered clause elimination after BCE.
                // CaDiCaL elim.cpp:1093-1098 cascade: subsume_round() -> block() -> cover().
                // CCE strictly subsumes BCE and can find additional covered-tautological
                // clauses that BCE misses. Running CCE inside the BVE cascade allows
                // its clause deletions to feed back into BVE candidate generation.
                if self.inproc_ctrl.cce.enabled && !self.cold.has_been_incremental {
                    self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::CCE, Self::cce);
                    passes_run.push("cce");
                    cce_ran_in_elim_phase = true;
                }

                // Dense propagation between interleave rounds (#8088):
                // BVE occ lists are still live. Use occ-list-based propagation
                // to discover units and conflicts from newly-derived clauses
                // without rebuilding the 2WL watch graph. This catches conflicts
                // earlier than the deferred 2WL BCP after the loop ends, and
                // propagates units so subsequent BVE rounds see a cleaner formula.
                // Kissat dense.c:99-110 (`kissat_enter_dense_mode`).
                if self.inproc.bve.is_occ_populated()
                    && self.qhead < self.trail.len()
                    && self.propagate_dense_check_unsat()
                {
                    elim_derived_unsat = true;
                    break;
                }

                // Check if subsumption, BCE, or CCE produced new BVE candidates.
                // CaDiCaL's feedback signal: subsume_round() returns true
                // when old_marked < stats.mark.elim.
                let new_candidates =
                    self.cold.bve_marked != marked_before || self.fixed_count != fixed_before;

                if !new_candidates || elim_round + 1 >= ELIM_INTERLEAVE_ROUNDS {
                    break;
                }

                // Reset BVE fixpoint guards so the next bve() call re-fires.
                // The subsumption between rounds incremented bve_marked; we
                // want bve() to see that and process the new candidates.
                self.cold.last_bve_fixed = self.fixed_count;
                self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
            }

            // Dense propagation before watch rebuild (#8088):
            // BVE occ lists are still live. Run one final dense propagation
            // pass to discover all remaining units and conflicts before the
            // expensive O(clauses) watch rebuild. This avoids rebuilding
            // watches only to immediately find a conflict via 2WL BCP.
            // Kissat dense.c:199-235 (`kissat_resume_sparse_mode`).
            if !elim_derived_unsat
                && self.inproc.bve.is_occ_populated()
                && self.qhead < self.trail.len()
                && self.propagate_dense_check_unsat()
            {
                elim_derived_unsat = true;
            }

            // BVE occ lists remain live after the BVE interleave loop (#8096).
            // Subsequent passes (factor, BCE, CCE, vivify, subsume) maintain
            // occ lists incrementally via per-clause notification hooks.

            // Soundness fix (#8397): clear stale reason references left by
            // subsumption/BCE/CCE passes that ran inside the BVE interleave
            // loop with watches_disconnected=true. When watches are disconnected,
            // delete_clause_checked(ClearLevel0) clears level-0 reasons for
            // literals IN the deleted clause, but skips the non-level-0 stale
            // reason scan (mutate_delete.rs:297-298). bve() calls
            // clear_stale_reasons() internally, but the subsume/BCE/CCE passes
            // between BVE rounds do not. After the last BVE round, those stale
            // references persist into CDCL solving, causing conflict analysis to
            // follow dead clause references (debug: backtrack.rs:220 panic;
            // release: spurious SAT → FINALIZE_SAT_FAIL).
            self.clear_stale_reasons();

            // Flush learned clauses containing eliminated variables (#8482).
            // BVE only deletes irredundant clauses. Learned clauses with
            // eliminated variables survive and get watched on reconnection,
            // which can cause BCP to assign eliminated variables.
            self.flush_learned_with_eliminated_vars();

            // CaDiCaL elim.cpp:1125-1128: reconnect watches once after
            // the entire elimination phase. Incremental reconnection (#8093):
            // instead of O(all_clauses) rebuild, purge stale binary entries
            // and attach watches only for new resolvents (>= arena_baseline).
            // BVE adds/deletes clauses in bulk; full re-propagation needed (#8095).
            self.mark_trail_affected(0);
            self.watches_disconnected = false;
            self.reconnect_bve_watches(arena_baseline);

            // BISECT: validate watches immediately after reconnect_bve_watches
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after reconnect_bve_watches");

            // Deferred propagation: catch units derived by BVE and subsumption
            // during the interleave loop (CaDiCaL elim.cpp:1134-1138).
            if elim_derived_unsat {
                return true;
            }
            if self.propagate_check_unsat() {
                return true;
            }

            // BISECT: validate watches after post-BVE propagation
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after post-bve-propagation");

            // Record the stricter re-entry threshold for BVE (#7178).
            self.update_bve_growth_guard(clauses_before_elim_phase);
            // CaDiCaL elim.cpp:1026: stats.elimphases++ once per elim() call.
            // bve_body() already increments bve_phases on each bve() call.
            // The extra increment here was causing 3x interval growth inflation
            // (2 sub-rounds × 1 body + 1 here = 3 per inprocessing round).
            // Removed: bve_body() handles phase counting correctly (#8135).
        } else if should_bve {
            // BVE skipped: keep fixpoint/schedule state in sync so BVE can
            // re-fire when the formula classification changes (#7135).
            //
            // Dense and wall-budget skips are budget decisions, not BVE
            // fixpoints. Leave last_bve_* untouched so already-visible
            // fixed-count/mark deltas still trigger a future due BVE pass.
            if (skip_gate_dependent_passes || skip_inproc_proportional)
                && !skip_bve_dense
                && !bve_wall_budget_exceeded
            {
                self.cold.last_bve_fixed = self.fixed_count;
                self.cold.last_bve_marked = self.cold.bve_marked;
            }
            self.inproc_ctrl
                .bve
                .reschedule(self.num_conflicts, BVE_INTERVAL_BASE);
        }

        // Factorization: introduce extension variables to compress clause structure.
        // CaDiCaL runs factoring after BVE (factor.cpp:928).
        // Guard: factorize builds O(clauses) occurrence lists BEFORE applying the
        // effort limit. On large residuals (>3M clauses), this costs 10+ seconds.
        // Matches preprocessing guard (config_preprocess.rs:340).
        let factor_count_before = self.cold.factor_factored_total;
        // #14 factor-dense unlock (default ON, density-banded): mirror the
        // preprocessing site — see `factor_dense_enabled` /
        // `FACTOR_DENSE_MIN_DENSITY` (config_preprocess_policy.rs) for the
        // A/B rationale (gains at density>=100, losses at ~60). Factor is
        // self-contained here (builds its own occ lists; no data dependency
        // on the other density-gated passes), so letting only factor through
        // is safe. `bve_density` (computed above) is this round's live
        // clause/var density — the same quantity the preprocess site gates on.
        let factor_dense = config_preprocess_policy::factor_dense_enabled()
            && bve_density >= config_preprocess_policy::factor_dense_min_density();
        // Record why a scheduled factor pass did not run (one evaluation, reused
        // by both arms below) so `--stats` can attribute a factor-less run to a
        // schedule gate rather than to the pass finding nothing.
        let factor_skip = self.factor_skip_reason();
        if let Some(reason) = factor_skip {
            self.cold.factor_skip_counts[reason.index()] += 1;
        }
        if factor_skip.is_none() && (!skip_expensive_equivalence_passes || factor_dense) {
            self.jit_invalidate_for_structural_pass(); // factor: structural (#8128)
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Factor, Self::factorize);
            passes_run.push("factor");
            // BISECT: validate watches after factor
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after factor");
            self.reschedule_bve_after_productive_circuit_factor(factor_count_before);
            if self.propagate_check_unsat() {
                return true;
            }
        } else if factor_skip.is_none() && skip_expensive_equivalence_passes {
            self.inproc_ctrl
                .factor
                .reschedule(self.num_conflicts, FACTOR_INTERVAL);
        }

        // CaDiCaL factor.cpp:966: factor may create duplicate divider clauses.
        // Guard with skip_expensive_equivalence_passes (#8084): when factor is
        // skipped, no new divider clauses are produced. The O(2*num_vars) scan
        // with per-literal HashMap allocations is wasted on large formulas.
        if self.inproc_ctrl.decompose.enabled
            && !skip_expensive_equivalence_passes
            && self.deduplicate_binary_clauses()
        {
            return true;
        }

        // SBVA: Structured Bounded Variable Addition (Manthey 2023).
        // Runs after factorization and deduplication. SBVA identifies groups
        // of clauses sharing large common literal subsets and compresses them
        // using fresh extension variables. Complementary to factor: factor
        // handles single-literal differences, SBVA handles multi-literal
        // shared subsets.
        if self.should_sbva() && !skip_expensive_equivalence_passes {
            self.jit_invalidate_for_structural_pass();
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Sbva, Self::sbva);
            passes_run.push("sbva");
            // BISECT: validate watches after sbva
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after sbva");
            if self.propagate_check_unsat() {
                return true;
            }
        } else if self.should_sbva() && skip_expensive_equivalence_passes {
            self.inproc_ctrl
                .sbva
                .reschedule(self.num_conflicts, SBVA_INTERVAL);
        }

        // Standalone BCE: only if it wasn't already run in the interleaved
        // elimination phase above. This ensures BCE fires on its own schedule
        // even when BVE doesn't fire.
        // Gate: BCE builds occurrence lists O(clauses) before the effort limit.
        // On large residuals (>3M clauses), this setup cost dominates (#7135).
        let should_bce = self.should_bce();
        if should_bce
            && !bce_ran_in_elim_phase
            && !self.cold.has_been_incremental
            && !skip_expensive_equivalence_passes
        {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BCE, Self::bce);
            passes_run.push("bce");
            // BISECT: validate watches after standalone bce
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after standalone-bce");
        } else if should_bce
            && !bce_ran_in_elim_phase
            && (self.cold.has_been_incremental || skip_expensive_equivalence_passes)
        {
            self.inproc_ctrl
                .bce
                .reschedule(self.num_conflicts, BCE_INTERVAL);
        }

        // Covered clause elimination (ACCE): strictly subsumes BCE.
        // CaDiCaL: cover() after block() in the elimination pipeline.
        // Same reconstruction as BCE. Disable via `--disable cce`.
        // Only runs standalone if it wasn't already run in the interleaved
        // elimination phase above (same pattern as standalone BCE).
        // Guard: CCE builds occurrence lists O(clauses) before the effort limit,
        // same as BCE. Skip on large residuals (#8084).
        let should_cce = self.should_cce();
        if should_cce
            && !cce_ran_in_elim_phase
            && !self.cold.has_been_incremental
            && !skip_expensive_equivalence_passes
        {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::CCE, Self::cce);
            passes_run.push("cce");
            // BISECT: validate watches after standalone cce
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after standalone-cce");
        } else if should_cce
            && !cce_ran_in_elim_phase
            && (self.cold.has_been_incremental || skip_expensive_equivalence_passes)
        {
            self.inproc_ctrl
                .cce
                .reschedule(self.num_conflicts, CCE_INTERVAL);
        }

        // No later pass in this restart-inprocessing round consumes BVE's
        // occurrence lists directly. Unless the default-off saved-state reuse
        // candidate is enabled, drop the live marker here so condition,
        // transred, sweep, vivify, and later reduce_db mutations do not pay
        // occurrence maintenance that cannot be reused.
        self.inproc.bve.finish_occ_saved_state_round();

        // Conditioning (GBCE) after BCE: globally blocked clause elimination.
        // Reference: CaDiCaL condition.cpp; Kiesl, Heule, Biere -- ATVA 2019.
        // Guard: conditioning builds a total assignment over all vars and iterates
        // all clauses. On large residuals, this is O(clauses) before the check.
        // Matches preprocessing guard (config_preprocess.rs:416).
        if self.should_condition() && !skip_expensive_equivalence_passes {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Condition, Self::condition);
            passes_run.push("condition");
            // BISECT: validate watches after condition
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after condition");
        } else if self.should_condition() && skip_expensive_equivalence_passes {
            self.inproc_ctrl
                .condition
                .reschedule(self.num_conflicts, CONDITION_INTERVAL);
        }

        // Transred removes transitive binary clauses via BFS on the binary
        // implication graph. The BFS cost is O(binary_clauses). On large dense
        // formulas (>3M clauses), the setup + BFS overhead is disproportionate
        // to the few transitive edges found (#8084).
        let should_transred = self.should_transred();
        if should_transred {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::TransRed);
        }
        if should_transred && !skip_expensive_equivalence_passes && !skip_inproc_proportional {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::TransRed, Self::transred);
            passes_run.push("transred");
            // BISECT: validate watches after transred
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after transred");
            // Post-transred: no probing/vivify -- search variant.
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return true;
            }
        } else if should_transred && (skip_expensive_equivalence_passes || skip_inproc_proportional)
        {
            self.inproc_ctrl
                .transred
                .reschedule(self.num_conflicts, TRANSRED_INTERVAL);
        }

        // Sweep gating (#9215): sweep's kitten sub-solver cost scales with
        // num_vars (COI neighborhood traversal), NOT num_clauses. On shuffling-2
        // (138K vars, 4.7M clauses), sweep solves 1824 vars in Kissat's first
        // inprocessing round — the critical technique that enables fast SAT.
        // Gate by variable count only (PREPROCESS_EXPENSIVE_MAX_VARS = 200K),
        // not by clause count or density. CaDiCaL runs sweep unconditionally
        // with tick-based effort limits.
        //
        // Post-collapse re-derivation (--sat-no-bve-post-collapse=1, default
        // OFF): this gate keys on the ORIGINAL num_vars, which is never
        // re-derived after congruence+decompose substitute away a large
        // fraction of the variables. When the post-collapse unlock holds
        // (re-derived ACTIVE count under the cap — the same predicate that
        // re-opens preprocess BVE), let the elimination-phase sweep run on
        // the collapsed residual too. Cost stays bounded by the
        // sweep_wall_budget_exceeded round guard below; the unlock is inert
        // when the knob is off or the collapse merged nothing.
        let skip_sweep = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            && !self.bve_post_collapse_unlock_active();
        // Wall-clock guard (#8448): skip sweep if this inprocessing round
        // has already consumed the budget. Sweep's kitten sub-solver can
        // consume 300-1400ms per round on medium formulas.
        let sweep_wall_budget_exceeded =
            self.inproc_round_over_budget(round_start, round_start_ticks);
        if self.should_sweep() && !skip_sweep && !sweep_wall_budget_exceeded {
            self.jit_invalidate_for_structural_pass(); // sweep: structural (#8128)
                                                       // SAT sweeping detects equivalences via SCC on implication graph.
            if self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Sweep, Self::sweep) {
                return true;
            }
            passes_run.push("sweep");
            // BISECT: validate watches after sweep
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after sweep");
            // Post-sweep: no probing/vivify -- search variant.
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return true;
            }

            // CaDiCaL re-runs decompose after sweep (probe.cpp:947-948).
            // Sweep equivalences produce new binary clauses for SCC.
            if self.inproc_ctrl.decompose.enabled {
                self.jit_invalidate_for_structural_pass(); // decompose: structural (#8128)
                self.run_timed_diagnostic_inprocessing_pass(
                    DiagnosticPass::Decompose,
                    Self::decompose,
                );
                passes_run.push("decompose");
                // BISECT: validate watches after decompose
                #[cfg(debug_assertions)]
                self.bisect_validate_watches("after decompose-in-sweep");
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        } else if self.should_sweep() && skip_sweep {
            self.inproc_ctrl
                .sweep
                .reschedule(self.num_conflicts, SWEEP_INTERVAL);
        }

        // Variable compaction: remap active variables to a contiguous range
        // after BVE/substitution creates holes in variable-indexed arrays.
        // Guards: level 0, non-incremental, no proof output, sufficient inactives.
        if self.compacting() {
            self.compact();
            passes_run.push("compact");
            // BISECT: validate watches after compact
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after compact");
        }

        false
    }

    /// Official Main/default/LRAT reaches the elimination tail with BVE,
    /// factor, SBVA, and sweep clamped off for proof safety. Keep the remaining
    /// LRAT-safe scheduled passes, but skip the disabled-pass density,
    /// wall-clock, cascade, and watch-disconnect setup.
    fn run_official_main_lrat_elimination_passes(
        &mut self,
        passes_run: &mut Vec<&'static str>,
        skip_expensive_equivalence_passes: bool,
    ) -> bool {
        debug_assert!(self.use_official_main_lrat_elimination_fast_path());

        if self.run_bve_lrat_scout_elimination_route(passes_run, skip_expensive_equivalence_passes)
        {
            return true;
        }

        if self.inproc_ctrl.decompose.enabled
            && !skip_expensive_equivalence_passes
            && self.deduplicate_binary_clauses()
        {
            return true;
        }

        let should_bce = self.should_bce();
        if should_bce && !self.cold.has_been_incremental && !skip_expensive_equivalence_passes {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BCE, Self::bce);
            passes_run.push("bce");
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after standalone-bce");
        } else if should_bce
            && (self.cold.has_been_incremental || skip_expensive_equivalence_passes)
        {
            self.inproc_ctrl
                .bce
                .reschedule(self.num_conflicts, BCE_INTERVAL);
        }

        let should_cce = self.should_cce();
        if should_cce && !self.cold.has_been_incremental && !skip_expensive_equivalence_passes {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::CCE, Self::cce);
            passes_run.push("cce");
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after standalone-cce");
        } else if should_cce
            && (self.cold.has_been_incremental || skip_expensive_equivalence_passes)
        {
            self.inproc_ctrl
                .cce
                .reschedule(self.num_conflicts, CCE_INTERVAL);
        }

        if self.should_condition() && !skip_expensive_equivalence_passes {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Condition, Self::condition);
            passes_run.push("condition");
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after condition");
        } else if self.should_condition() && skip_expensive_equivalence_passes {
            self.inproc_ctrl
                .condition
                .reschedule(self.num_conflicts, CONDITION_INTERVAL);
        }

        let should_transred = self.should_transred();
        if should_transred {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::TransRed);
        }
        let skip_inproc_proportional =
            should_transred && self.bve_transred_proportional_guard_exceeded();
        if should_transred && !skip_expensive_equivalence_passes && !skip_inproc_proportional {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::TransRed, Self::transred);
            passes_run.push("transred");
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after transred");
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return true;
            }
        } else if should_transred && (skip_expensive_equivalence_passes || skip_inproc_proportional)
        {
            self.inproc_ctrl
                .transred
                .reschedule(self.num_conflicts, TRANSRED_INTERVAL);
        }

        if self.compacting() {
            self.compact();
            passes_run.push("compact");
            #[cfg(debug_assertions)]
            self.bisect_validate_watches("after compact");
        }

        false
    }

    fn bve_lrat_scout_elimination_route_active(&self) -> bool {
        let sat_flags = ay_core::sat_disable_flags();
        self.cold.bve_lrat_scout_route_enabled
            && self.cold.lrat_enabled
            && self.proof_manager.is_some()
            && self.sat_comp_main_conflict_pruning_enabled()
            && !self.cold.has_been_incremental
            && !self.cold.elimfast_disabled
            && !sat_flags.no_inprocess
            && !sat_flags.no_bve
    }

    fn run_bve_lrat_scout_elimination_route(
        &mut self,
        passes_run: &mut Vec<&'static str>,
        skip_expensive_equivalence_passes: bool,
    ) -> bool {
        if !self.bve_lrat_scout_elimination_route_active()
            || skip_expensive_equivalence_passes
            || self.is_interrupted()
        {
            return false;
        }

        let inproc_ctrl_before_route = self.inproc_ctrl.clone();
        let bve_limit_before_route = self.cold.bve_limit;
        let instantiate_rebuilt_watches_before_route = self.cold.instantiate_rebuilt_watches;
        let bve_growth_bound_before_route = self.inproc.bve.growth_bound();
        let bve_fastelim_mode_before_route = self.inproc.bve.is_fastelim_mode();
        let bve_quick_elim_mode_before_route = self.inproc.bve.is_quick_elim_mode();

        self.inproc_ctrl.bve.enabled = true;
        self.inproc_ctrl.factor.enabled = false;
        self.inproc_ctrl.sbva.enabled = false;
        self.inproc_ctrl.sweep.enabled = false;
        self.inproc_ctrl.gate.enabled = false;
        self.cold.bve_limit = Some(1);
        self.cold.instantiate_rebuilt_watches = false;
        self.watches.clear();
        self.watches_disconnected = true;
        self.cold.disconnected_deletions = 0;
        self.inproc.bve.set_growth_bound(16);
        self.inproc.bve.set_quick_elim_mode(false);
        self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
        // Instantiate gate (lever 2, AY_AB_BVE_INST_GATE): stamp a new
        // elimination phase for this single-shot BVE route.
        self.cold.bve_elim_phase_seq = self.cold.bve_elim_phase_seq.wrapping_add(1);

        let mut bve_unsat =
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BVE, Self::bve);
        passes_run.push("bve");

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

        bve_unsat || self.propagate_check_unsat()
    }

    fn use_official_main_lrat_elimination_fast_path(&self) -> bool {
        self.cold.lrat_enabled
            && self.sat_comp_main_conflict_pruning_enabled()
            && !self.inproc_ctrl.bve.enabled
            && !self.inproc_ctrl.factor.enabled
            && !self.inproc_ctrl.sbva.enabled
            && !self.inproc_ctrl.sweep.enabled
    }

    fn bve_transred_proportional_guard_exceeded(&self) -> bool {
        // Indices follow INPROCESS_TIMING_LABELS: 6 = BVE, 12 = transred.
        let bve_transred_ns =
            self.stats.inprocessing_time_ns[6] + self.stats.inprocessing_time_ns[12];
        let search_elapsed_ns = self
            .cold
            .solve_start_time
            .map(|t| t.elapsed().as_nanos() as u64)
            .unwrap_or(0);
        search_elapsed_ns > 2_000_000_000 && bve_transred_ns * 100 / search_elapsed_ns.max(1) > 15
    }

    fn reschedule_bve_after_productive_circuit_factor(&mut self, factor_count_before: u64) {
        let gate_stats = self.inproc.gate_extractor.stats().clone();
        self.reschedule_bve_after_productive_circuit_factor_with_stats(
            factor_count_before,
            &gate_stats,
        );
    }

    fn reschedule_bve_after_productive_circuit_factor_with_stats(
        &mut self,
        factor_count_before: u64,
        gate_stats: &GateStats,
    ) {
        if !self
            .should_reschedule_bve_after_productive_circuit_factor(factor_count_before, gate_stats)
        {
            return;
        }

        self.cold.last_bve_fixed = self.fixed_count;
        self.cold.last_bve_marked = self.cold.bve_marked.wrapping_sub(1);
        self.inproc_ctrl.bve.next_conflict = self.num_conflicts;
    }

    fn should_reschedule_bve_after_productive_circuit_factor(
        &self,
        factor_count_before: u64,
        gate_stats: &GateStats,
    ) -> bool {
        if self.proof_manager.is_some() || self.cold.lrat_enabled {
            return false;
        }
        if !self.inproc_ctrl.bve.enabled || self.cold.has_been_incremental {
            return false;
        }
        if self.cold.factor_factored_total <= factor_count_before {
            return false;
        }
        if self.num_vars > POST_FACTOR_CIRCUIT_BVE_MAX_VARS
            || self.arena.irredundant_count() > POST_FACTOR_CIRCUIT_BVE_MAX_IRRED_CLAUSES
        {
            return false;
        }

        gate_stats.and_gates.saturating_add(gate_stats.xor_gates)
            >= POST_FACTOR_CIRCUIT_BVE_MIN_AND_XOR_GATES
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ProofOutput, SolverVariant, VariantInput, VariantRouteProfile, VariantStartupPolicy,
    };

    fn official_main_lrat_solver() -> Solver {
        let input = VariantInput::new(16, 32, true, true)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let config = SolverVariant::Default.config(input);
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 0);
        let mut solver = Solver::with_proof_output(16, proof);
        config.apply_to_solver(&mut solver);
        solver
    }

    fn due_bve_elimination_solver(num_vars: usize) -> Solver {
        let mut solver = Solver::new(num_vars);
        solver.disable_all_inprocessing();
        solver.set_bve_enabled(true);
        solver.num_conflicts = 123;
        solver.inproc_ctrl.bve.next_conflict = 0;
        solver.cold.last_bve_fixed = -17;
        solver.cold.last_bve_marked = solver.cold.bve_marked.wrapping_add(1);
        solver
    }

    fn due_bce_cce_solver() -> Solver {
        let mut solver = Solver::new(4);
        solver.disable_all_inprocessing();
        solver.set_bce_enabled(true);
        solver.set_cce_enabled(true);
        solver.num_conflicts = 321;
        solver.inproc_ctrl.bce.next_conflict = 0;
        solver.inproc_ctrl.cce.next_conflict = 0;
        solver
    }

    fn official_main_lrat_due_bce_cce_solver() -> Solver {
        let mut solver = official_main_lrat_solver();
        solver.disable_all_inprocessing();
        solver.set_bce_enabled(true);
        solver.set_cce_enabled(true);
        solver.num_conflicts = 451;
        solver.inproc_ctrl.bce.next_conflict = 0;
        solver.inproc_ctrl.cce.next_conflict = 0;
        assert!(solver.use_official_main_lrat_elimination_fast_path());
        solver
    }

    fn add_small_bve_surface(solver: &mut Solver) {
        solver.add_clause_db(
            &[
                Literal::positive(Variable(0)),
                Literal::positive(Variable(1)),
            ],
            false,
        );
        solver.add_clause_db(
            &[
                Literal::negative(Variable(0)),
                Literal::positive(Variable(2)),
            ],
            false,
        );
    }

    fn add_small_lrat_bve_surface(solver: &mut Solver) {
        assert!(solver.add_clause(vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ]));
        assert!(solver.add_clause(vec![
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ]));
        solver.freeze(Variable(1));
        solver.freeze(Variable(2));
    }

    #[test]
    fn productive_no_proof_circuit_factor_reschedules_bve() {
        let mut solver = due_bve_elimination_solver(16);
        solver.num_conflicts = 42;
        solver.inproc_ctrl.bve.next_conflict = 1_000_000;
        solver.cold.bve_marked = 7;
        solver.cold.last_bve_marked = solver.cold.bve_marked;
        solver.cold.last_bve_fixed = solver.fixed_count;
        solver.cold.factor_factored_total = 11;
        let gate_stats = GateStats {
            and_gates: POST_FACTOR_CIRCUIT_BVE_MIN_AND_XOR_GATES,
            ..Default::default()
        };

        assert!(
            solver.should_reschedule_bve_after_productive_circuit_factor(10, &gate_stats),
            "productive small circuit factorization should reopen BVE scheduling"
        );
        solver.reschedule_bve_after_productive_circuit_factor_with_stats(10, &gate_stats);

        assert_eq!(solver.inproc_ctrl.bve.next_conflict, solver.num_conflicts);
        assert_eq!(solver.cold.last_bve_fixed, solver.fixed_count);
        assert_eq!(
            solver.cold.last_bve_marked,
            solver.cold.bve_marked.wrapping_sub(1)
        );
    }

    #[test]
    fn post_factor_bve_reschedule_requires_circuit_gates_and_no_lrat() {
        let mut solver = due_bve_elimination_solver(16);
        solver.cold.factor_factored_total = 2;
        let no_gates = GateStats::default();

        assert!(
            !solver.should_reschedule_bve_after_productive_circuit_factor(1, &no_gates),
            "non-circuit factorization should keep normal BVE backoff"
        );

        let circuit_gates = GateStats {
            xor_gates: POST_FACTOR_CIRCUIT_BVE_MIN_AND_XOR_GATES,
            ..Default::default()
        };
        solver.cold.lrat_enabled = true;
        assert!(
            !solver.should_reschedule_bve_after_productive_circuit_factor(1, &circuit_gates),
            "LRAT/proof mode must keep factor-to-BVE reopening closed"
        );
    }

    #[test]
    fn bve_occ_saved_state_default_off_drops_after_last_same_round_consumer() {
        let mut solver = due_bve_elimination_solver(3);
        add_small_bve_surface(&mut solver);

        let mut passes_run = Vec::new();
        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(passes_run.contains(&"bve"));
        assert!(
            !solver.inproc.bve.is_occ_populated(),
            "default-off saved-state candidate should drop after same-round consumers"
        );
        assert_eq!(solver.inproc.bve.stats().occ_saved_state_round_end_drops, 1);
        assert_eq!(
            solver.inproc.bve.stats().occ_saved_state_round_end_retains,
            0
        );
    }

    #[test]
    fn bve_occ_saved_state_reuse_candidate_retains_after_inprocessing_round() {
        let mut solver = due_bve_elimination_solver(3);
        solver.set_bve_occ_saved_state_reuse_enabled(true);
        add_small_bve_surface(&mut solver);

        let mut passes_run = Vec::new();
        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(passes_run.contains(&"bve"));
        assert!(
            solver.inproc.bve.is_occ_populated(),
            "opt-in saved-state candidate should retain occurrence state"
        );
        assert_eq!(solver.inproc.bve.stats().occ_saved_state_round_end_drops, 0);
        assert_eq!(
            solver.inproc.bve.stats().occ_saved_state_round_end_retains,
            1
        );
    }

    #[test]
    fn bve_dense_skip_reschedules_without_recording_fixpoint() {
        let mut solver = due_bve_elimination_solver(2);
        let dense_clause_count = (BVE_HIGH_DENSITY_SKIP as usize * 2) + 1;
        for _ in 0..dense_clause_count {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(0)),
                    Literal::positive(Variable(1)),
                ],
                false,
            );
        }
        solver.cold.last_bve_fixed = -17;
        solver.cold.last_bve_marked = solver.cold.bve_marked.wrapping_add(1);
        let fixed_before = solver.cold.last_bve_fixed;
        let marked_before = solver.cold.last_bve_marked;

        let mut passes_run = Vec::new();
        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(passes_run.is_empty());
        assert_eq!(
            solver.inproc_ctrl.bve.next_conflict,
            solver.num_conflicts + BVE_INTERVAL_BASE
        );
        assert_eq!(solver.cold.last_bve_fixed, fixed_before);
        assert_eq!(solver.cold.last_bve_marked, marked_before);
    }

    #[test]
    fn bve_wall_budget_skip_reschedules_without_recording_fixpoint() {
        let mut solver = due_bve_elimination_solver(4);
        let fixed_before = solver.cold.last_bve_fixed;
        let marked_before = solver.cold.last_bve_marked;
        let round_start = ay_core::time::Instant::now()
            .checked_sub(std::time::Duration::from_millis(
                INPROCESSING_ROUND_WALL_LIMIT_MS + 1,
            ))
            .unwrap();

        let mut passes_run = Vec::new();
        let unsat =
            solver.run_elimination_passes(&mut passes_run, false, false, false, round_start, 0);

        assert!(!unsat);
        assert!(passes_run.is_empty());
        assert_eq!(
            solver.inproc_ctrl.bve.next_conflict,
            solver.num_conflicts + BVE_INTERVAL_BASE
        );
        assert_eq!(solver.cold.last_bve_fixed, fixed_before);
        assert_eq!(solver.cold.last_bve_marked, marked_before);
    }

    #[test]
    fn bve_interleave_subsumption_obeys_large_formula_skip_gate() {
        let mut baseline = due_bve_elimination_solver(3);
        baseline.set_subsume_enabled(true);
        let mut baseline_passes = Vec::new();
        let baseline_unsat = baseline.run_elimination_passes(
            &mut baseline_passes,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );
        assert!(!baseline_unsat);
        assert!(
            baseline_passes.contains(&"subsume"),
            "pre-BVE subsumption should run when the skip gate is open"
        );

        let mut skipped = due_bve_elimination_solver(3);
        skipped.set_subsume_enabled(true);
        let mut skipped_passes = Vec::new();
        let skipped_unsat = skipped.run_elimination_passes(
            &mut skipped_passes,
            false,
            false,
            true,
            ay_core::time::Instant::now(),
            0,
        );
        assert!(!skipped_unsat);
        assert!(
            !skipped_passes.contains(&"subsume"),
            "BVE must not force subsumption when the large-formula gate is closed"
        );
        let (_, accounting) = skipped
            .inprocessing_pass_accounting()
            .into_iter()
            .find(|(label, _)| *label == "inproc_subsume_ms")
            .expect("subsumption accounting should be present");
        assert_eq!(accounting.attempts, 0);
        assert_eq!(accounting.runs, 0);
    }

    #[test]
    fn bce_cce_expensive_skip_reschedules_due_passes() {
        let mut solver = due_bce_cce_solver();
        let mut passes_run = Vec::new();

        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            true,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(passes_run.is_empty());
        assert_eq!(
            solver.inproc_ctrl.bce.next_conflict,
            solver.num_conflicts + BCE_INTERVAL
        );
        assert_eq!(
            solver.inproc_ctrl.cce.next_conflict,
            solver.num_conflicts + CCE_INTERVAL
        );
    }

    #[test]
    fn bce_cce_incremental_skip_reschedules_due_passes() {
        let mut solver = due_bce_cce_solver();
        solver.cold.has_been_incremental = true;
        let mut passes_run = Vec::new();

        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(passes_run.is_empty());
        assert_eq!(
            solver.inproc_ctrl.bce.next_conflict,
            solver.num_conflicts + BCE_INTERVAL
        );
        assert_eq!(
            solver.inproc_ctrl.cce.next_conflict,
            solver.num_conflicts + CCE_INTERVAL
        );
    }

    #[test]
    fn official_main_lrat_bce_cce_expensive_skip_reschedules_due_passes() {
        let mut solver = official_main_lrat_due_bce_cce_solver();
        let mut passes_run = Vec::new();

        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            true,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(passes_run.is_empty());
        assert_eq!(
            solver.inproc_ctrl.bce.next_conflict,
            solver.num_conflicts + BCE_INTERVAL
        );
        assert_eq!(
            solver.inproc_ctrl.cce.next_conflict,
            solver.num_conflicts + CCE_INTERVAL
        );
    }

    #[test]
    fn official_main_lrat_bce_cce_incremental_skip_reschedules_due_passes() {
        let mut solver = official_main_lrat_due_bce_cce_solver();
        solver.cold.has_been_incremental = true;
        let mut passes_run = Vec::new();

        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(passes_run.is_empty());
        assert_eq!(
            solver.inproc_ctrl.bce.next_conflict,
            solver.num_conflicts + BCE_INTERVAL
        );
        assert_eq!(
            solver.inproc_ctrl.cce.next_conflict,
            solver.num_conflicts + CCE_INTERVAL
        );
    }

    #[test]
    fn official_main_lrat_fast_path_rejects_internal_destructive_transforms() {
        let mut solver = official_main_lrat_solver();

        assert!(solver.use_official_main_lrat_elimination_fast_path());

        solver.inproc_ctrl.bve.enabled = true;
        assert!(!solver.use_official_main_lrat_elimination_fast_path());
        solver.inproc_ctrl.bve.enabled = false;

        solver.inproc_ctrl.factor.enabled = true;
        assert!(!solver.use_official_main_lrat_elimination_fast_path());
        solver.inproc_ctrl.factor.enabled = false;

        solver.inproc_ctrl.sbva.enabled = true;
        assert!(!solver.use_official_main_lrat_elimination_fast_path());
        solver.inproc_ctrl.sbva.enabled = false;

        solver.inproc_ctrl.sweep.enabled = true;
        assert!(!solver.use_official_main_lrat_elimination_fast_path());
    }

    #[test]
    fn official_main_lrat_public_setters_remain_fail_closed() {
        let mut solver = official_main_lrat_solver();

        assert!(solver.use_official_main_lrat_elimination_fast_path());
        assert!(
            !solver.bve_lrat_scout_route_enabled(),
            "Main/LRAT BVE scout route must be default-off"
        );

        solver.set_bve_enabled(true);
        assert!(!solver.is_bve_enabled(), "LRAT must fail closed for BVE");
        assert!(solver.use_official_main_lrat_elimination_fast_path());

        solver.set_factor_enabled(true);
        assert!(
            !solver.is_factor_enabled(),
            "LRAT must fail closed for factor"
        );
        assert!(solver.use_official_main_lrat_elimination_fast_path());

        solver.set_sbva_enabled(true);
        assert!(!solver.is_sbva_enabled(), "LRAT must fail closed for SBVA");
        assert!(solver.use_official_main_lrat_elimination_fast_path());

        solver.set_sweep_enabled(true);
        assert!(
            !solver.is_sweep_enabled(),
            "LRAT must fail closed for sweep"
        );
        assert!(solver.use_official_main_lrat_elimination_fast_path());
    }

    #[test]
    fn official_main_lrat_default_does_not_run_bve_scout() {
        let mut solver = official_main_lrat_solver();
        solver.disable_all_inprocessing();
        add_small_lrat_bve_surface(&mut solver);

        let mut passes_run = Vec::new();
        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert!(
            !passes_run.contains(&"bve"),
            "default official Main/LRAT route must keep BVE clamped"
        );
        assert_eq!(solver.bve_stats().vars_eliminated, 0);
        assert_eq!(solver.bve_stats().lrat_preflight_rejected, 0);
        assert!(!solver.is_bve_enabled());
        assert!(!solver.is_factor_enabled());
        assert!(!solver.is_sweep_enabled());
    }

    #[test]
    fn official_main_lrat_bve_scout_routes_only_bve_preflight() {
        let mut solver = official_main_lrat_solver();
        solver.disable_all_inprocessing();
        add_small_lrat_bve_surface(&mut solver);
        let clause_indices: Vec<usize> = solver.arena.indices().collect();
        solver.cold.clause_ids[clause_indices[0]] = 0;
        let active_before = solver.arena.active_clause_count();
        solver.inproc_ctrl.sbva.next_conflict = 123;
        solver.inproc_ctrl.gate.next_conflict = 456;
        let inproc_ctrl_before = format!("{:?}", solver.inproc_ctrl);

        assert!(!solver.is_sbva_enabled());
        assert!(!solver.is_gate_enabled());
        assert!(!solver.inproc_ctrl.sbva.enabled);
        assert!(!solver.inproc_ctrl.gate.enabled);
        solver.set_bve_lrat_scout_route_enabled(true);
        let mut passes_run = Vec::new();
        let unsat = solver.run_elimination_passes(
            &mut passes_run,
            false,
            false,
            false,
            ay_core::time::Instant::now(),
            0,
        );

        assert!(!unsat);
        assert_eq!(passes_run, vec!["bve"]);
        assert_eq!(
            solver.bve_stats().lrat_preflight_rejected,
            1,
            "BVE scout must reject through the LRAT transaction preflight before mutation"
        );
        assert_eq!(solver.bve_stats().vars_eliminated, 0);
        assert_eq!(solver.arena.active_clause_count(), active_before);
        assert!(
            !solver.var_lifecycle.is_removed(0),
            "failed preflight must not eliminate the candidate variable"
        );
        assert!(
            !solver.is_bve_enabled(),
            "route must restore the public Main/LRAT BVE clamp"
        );
        assert!(!solver.is_factor_enabled());
        assert!(!solver.is_sweep_enabled());
        assert!(
            !solver.is_sbva_enabled(),
            "route must restore the public Main/LRAT SBVA clamp"
        );
        assert!(
            !solver.is_gate_enabled(),
            "route must restore the public Main/LRAT gate clamp"
        );
        assert!(!solver.inproc_ctrl.sbva.enabled);
        assert!(!solver.inproc_ctrl.gate.enabled);
        assert_eq!(solver.inproc_ctrl.sbva.next_conflict, 123);
        assert_eq!(solver.inproc_ctrl.gate.next_conflict, 456);
        assert_eq!(format!("{:?}", solver.inproc_ctrl), inproc_ctrl_before);
    }

    #[test]
    fn non_official_lrat_does_not_use_fast_path() {
        let config = SolverVariant::Default.config(VariantInput::new(16, 32, true, true));
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 0);
        let mut solver = Solver::with_proof_output(16, proof);
        config.apply_to_solver(&mut solver);

        assert!(!solver.use_official_main_lrat_elimination_fast_path());
    }

    #[test]
    fn route_flag_without_lrat_does_not_use_fast_path() {
        let mut solver = Solver::new(16);
        solver.set_sat_comp_main_conflict_pruning(true);
        solver.set_bve_enabled(false);
        solver.set_factor_enabled(false);
        solver.set_sbva_enabled(false);
        solver.set_sweep_enabled(false);

        assert!(!solver.use_official_main_lrat_elimination_fast_path());
    }
}
