// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failed literal probing and hyper-binary resolution.

use super::super::*;

impl Solver {
    /// Run failed literal probing (wrapper: always reschedules).
    ///
    /// Returns `true` only if UNSAT is proven (level-0 conflict after learning
    /// a derived unit). Returns `false` otherwise.
    pub(in crate::solver) fn probe(&mut self) -> bool {
        let result = self.probe_body();
        self.inproc_ctrl
            .probe
            .reschedule(self.num_conflicts, PROBE_INTERVAL);
        result
    }

    /// Probe body — early returns are safe; wrapper handles rescheduling.
    ///
    /// For each candidate probe literal, temporarily assign it and propagate.
    /// If a conflict is found, the literal is "failed" and its negation must be true.
    ///
    /// This must be called at decision level 0 (after a restart) for correctness.
    fn probe_body(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // Validate watches before probing to detect pre-existing corruption
        // from OTFS or other in-place clause modifications.
        #[cfg(debug_assertions)]
        self.validate_watches_reverse("before probe_body");

        // Ensure all level-0 BCP-propagated variables have unit proof IDs
        // before collecting LRAT hints. Without this, collect_probe_conflict_lrat_hints
        // falls back to multi-literal reason clause IDs, which the LRAT checker
        // rejects (NonUnit: 2+ unfalsified literals). Same guard as backbone.rs:48,
        // condition.rs:45, decompose.rs:195. Fixes #7108.
        self.ensure_level0_unit_proof_ids();

        // CaDiCaL probe.cpp:816-817: if leftover probes exist from the
        // previous round (cut short by tick limit), flush and re-filter them.
        // Only regenerate from scratch when the candidate list is empty.
        if self.inproc.prober.has_probes() {
            self.inproc
                .prober
                .flush_probes(&self.arena, &self.vals, self.fixed_count);
        }

        // Reset propfixed BEFORE the loop (CaDiCaL probe.cpp:819-824).
        // This must happen after flush (which uses old propfixed to filter)
        // but before generate/loop (so all candidates are re-probable).
        // "We reset propfixed since there was at least another conflict thus
        // a new learned clause, which might produce new propagations."
        self.inproc.prober.reset_propfixed();

        if !self.inproc.prober.has_probes() {
            self.inproc
                .prober
                .generate_probes(&self.arena, &self.vals, self.fixed_count);
        }
        self.inproc.prober.record_round();

        // Compute tick-proportional effort budget.
        // CaDiCaL probe.cpp:796-832: effort = (search_ticks_delta) * probeeffort / 1000
        // probeeffort=8 (0.8% of search ticks), min 10K ticks.
        // Budget and consumption both in tick units (#3758).
        //
        // Large-formula scaling (#8655): BMC formulas at depth 50+ produce
        // dense binary implication graphs. Scale probe effort for formulas
        // above the large-formula threshold.
        const PROBE_EFFORT_PERMILLE: u64 = 8; // CaDiCaL options.hpp:164
        const PROBE_MIN_EFFORT: u64 = 10_000;
        // AY_XP_PROBE_PERMILLE / AY_XP_PROBE_MIN (default-OFF measured-infra,
        // see xp_probe_vivify.rs): when unset these fall through to the shipping
        // constants, so the default budget is byte-for-byte unchanged.
        let effective_probe_effort = probe_permille().unwrap_or(
            if self.num_original_clauses > LARGE_FORMULA_REDUCE_CAP_THRESHOLD {
                PROBE_LARGE_FORMULA_EFFORT_PERMILLE
            } else {
                PROBE_EFFORT_PERMILLE
            },
        );
        let min_effort = probe_min_effort().unwrap_or(PROBE_MIN_EFFORT);
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.inproc.prober.last_search_ticks());
        let effort = (ticks_delta * effective_probe_effort / 1000).max(min_effort);
        let tick_limit = self.cold.probe_ticks.saturating_add(effort);

        // Probe each candidate
        while let Some(probe_lit) = self.inproc.prober.next_probe() {
            // Tick-proportional effort limit (#3758).
            // CaDiCaL probeeffort=8: 0.8% of search tick delta, measured in ticks.
            //
            // Interrupt check: the tick budget bounds work, not wall time — on
            // competition-scale inputs (e.g. the 49 MB spg_200_316 CNF, whose
            // large-formula budget is 25‰ of search ticks) one probe pass can
            // run for minutes, far past a caller's solve_interruptible timeout,
            // because the inprocessing dispatcher only checks the flag BETWEEN
            // passes. Probing is a pure optimization, so bailing out is always
            // sound; one relaxed atomic load per candidate is negligible next
            // to the full BCP each probe performs.
            if self.cold.probe_ticks >= tick_limit || self.is_interrupted() {
                break;
            }

            // Skip if already assigned or removed by inprocessing
            let probe_var = probe_lit.variable().index();
            if self.var_is_assigned(probe_var) || self.var_lifecycle.is_removed(probe_var) {
                continue;
            }

            self.inproc.prober.record_probed();

            // Precondition: probe literal must be unassigned
            debug_assert!(
                !self.var_is_assigned(probe_var),
                "BUG: probe deciding already-assigned literal {probe_lit:?}",
            );
            // Make probe as decision at level 1
            self.decide(probe_lit);

            // Clear probe_parent for decision literal (#3419).
            // CaDiCaL probe.cpp:338: probe_assign(lit, 0) — parent = 0 for decision.
            self.probe_parent[probe_var] = None;

            // Enter probing mode for level-1 parent tracking and HBR plumbing.
            // CaDiCaL probe.cpp:405,485 tracks probe parents for probing
            // regardless of whether HBR binary clauses are emitted.
            self.probing_mode = true;

            // Propagate (with HBR if enabled)
            let conflict_ref = self.probe_propagate();

            // Exit probing mode
            self.probing_mode = false;

            #[cfg(debug_assertions)]
            self.validate_watches_reverse(&format!(
                "after probe_propagate probe_lit={}",
                probe_lit.to_dimacs()
            ));

            if let Some(conflict_ref) = conflict_ref {
                // Found conflict - this is a failed literal
                self.inproc.prober.record_failed();

                // CaDiCaL-style failed-literal UIP: use dominator extraction.
                // Parent-chain processing is normally needed only when both HBR
                // and LRAT are disabled. The LRAT parent-chain path is a
                // default-off experiment because it must prove each stronger
                // unit from a checker-visible dominated trail suffix.
                let lrat_parent_chain_enabled =
                    self.cold.lrat_enabled && self.lrat_probe_parent_chain_enabled;
                let need_parent_chain =
                    (!self.hbr_enabled && !self.cold.lrat_enabled) || lrat_parent_chain_enabled;
                let dom_result = if need_parent_chain {
                    failed_literal_dominator(
                        self.arena.literals(conflict_ref.0 as usize),
                        probe_lit,
                        &self.trail,
                        &self.var_data,
                        &self.probe_parent,
                        &self.arena,
                    )
                } else {
                    crate::probe::failed_literal_dominator_forced_only(
                        self.arena.literals(conflict_ref.0 as usize),
                        probe_lit,
                        &self.trail,
                        &self.var_data,
                        &self.probe_parent,
                        &self.arena,
                    )
                };
                let crate::probe::FailedLiteralDominatorResult {
                    forced: dom_forced,
                    parent_chain: dom_parent_chain,
                    failure: dom_failure,
                } = dom_result;
                let parent_chain = if need_parent_chain && dom_forced.is_some() {
                    dom_parent_chain
                } else {
                    Vec::new()
                };
                // Fall back to legacy trail-walk UIP only for legitimate
                // dominator failures (NoDominator, ParentChainCycle).
                // MissingMetadata is a probe_parent contract violation —
                // debug_assert fires in failed_literal_dominator; still fall
                // back in release for safety, but log the contract break.
                let forced = dom_forced.or_else(|| {
                    if dom_failure == Some(crate::probe::DominatorFailure::MissingMetadata) {
                        debug_assert!(
                            false,
                            "BUG: probe_parent metadata missing — dominator path returned MissingMetadata for probe {probe_lit:?}",
                        );
                    }
                    find_failed_literal_uip(
                        self.arena.literals(conflict_ref.0 as usize),
                        &self.trail,
                        &self.var_data,
                        &self.arena,
                        self.inproc.prober.uip_seen_mut(),
                    )
                    .forced
                });
                let mut lrat_parent_hints = None;
                let mut lrat_parent_chain_units: Vec<(Literal, Vec<u64>)> = Vec::new();
                if lrat_parent_chain_enabled {
                    if let Some(unit) = forced {
                        lrat_parent_hints = self
                            .collect_probe_parent_chain_lrat_hints(conflict_ref, unit.negated())
                            .map(|hints| (unit, hints));
                    }
                    if lrat_parent_hints.is_some() {
                        for parent in &parent_chain {
                            if parent.variable().index() >= self.num_vars {
                                continue;
                            }
                            let parent_unit = parent.negated();
                            if Some(parent_unit) == forced {
                                continue;
                            }
                            if let Some(hints) =
                                self.collect_probe_parent_chain_lrat_hints(conflict_ref, *parent)
                            {
                                lrat_parent_chain_units.push((parent_unit, hints));
                            }
                        }
                    }
                }

                // LRAT's default path proves only the failed decision literal
                // (`probe_lit => conflict`). Stronger dominator/parent units
                // are used only when the default-off parent-chain collector
                // found a checker-visible suffix proof; otherwise we fall back
                // to the weaker existing unit.
                let forced = if self.cold.lrat_enabled {
                    lrat_parent_hints
                        .as_ref()
                        .map(|(unit, _)| *unit)
                        .or_else(|| Some(probe_lit.negated()))
                } else {
                    forced
                };
                // Collect LRAT hints BEFORE backtracking so level-1 trail
                // entries and their reason clauses are still accessible.
                // Mirrors the preprocessing probe pattern (config.rs:281).
                let lrat_hints = if let Some((_, hints)) = lrat_parent_hints {
                    hints
                } else {
                    self.collect_probe_conflict_lrat_hints(conflict_ref, probe_lit, forced)
                };

                // Backtrack to level 0
                self.backtrack(0);
                debug_assert_eq!(
                    self.decision_level, 0,
                    "BUG: probe backtrack did not reach level 0"
                );

                if let Some(unit_lit) = forced {
                    // (#8478) Validate forced literal is in-bounds before learning.
                    // The dominator walk in failed_literal_uip_from_dominator can
                    // produce OOB literals when reason clauses reference pre-compaction
                    // or eliminated variable indices. Skip the unit rather than panic
                    // in add_clause_db.
                    if unit_lit.variable().index() >= self.num_vars {
                        // OOB forced literal — skip learning, continue probing.
                        // The probe round is still sound: we simply miss this
                        // failed literal's implication.
                        self.inproc.prober.mark_probed(probe_lit, self.fixed_count);
                        continue;
                    }
                    // LRAT soundness gate: a probe conflict whose hint chain came
                    // back empty has no checker-visible certificate. Learning the
                    // unit anyway emits a hidden TrustedTransform (empty-hint LRAT
                    // units are downgraded in enqueue_derived_unit), which is
                    // stripped from the proof file and leaves later
                    // search-learned clauses resolving through this level-0
                    // assignment with a missing antecedent (RUP failure). The
                    // derived unit is a sound optimization, not required for
                    // UNSAT, so skip it when uncertifiable. (Same fix as
                    // intree.rs / transred.rs.)
                    if self.cold.lrat_enabled && lrat_hints.is_empty() {
                        self.inproc.prober.mark_probed(probe_lit, self.fixed_count);
                        continue;
                    }
                    // Learn the unit clause (proof emit + clause DB + enqueue + propagate).
                    if self.learn_derived_unit(unit_lit, &lrat_hints) {
                        // Conflict at level 0 - UNSAT
                        return true;
                    }

                    // After learning a probe-derived unit, BCP at level 0 may
                    // add new trail entries without unit_proof_ids (#7108).
                    if self.cold.lrat_enabled {
                        self.ensure_level0_unit_proof_ids();
                    }

                    // Process failed-literal parent chain (CaDiCaL probe.cpp:565-585):
                    // already-true parent => clash; unassigned => force negation.
                    //
                    // CaDiCaL asserts !opts.probehbr at lines 571,576: Phase 4
                    // is mutually exclusive with HBR. When HBR is enabled, BCP
                    // already handles parent-chain implications via binary clauses.
                    // Gate on !lrat_enabled because we lack probehbr_chains cache
                    // for LRAT proof hints (CaDiCaL lines 572,577: get_probehbr_lrat).
                    if !self.hbr_enabled && !self.cold.lrat_enabled {
                        for parent in parent_chain {
                            // (#8478) Skip OOB parent literals from dominator walk.
                            if parent.variable().index() >= self.num_vars {
                                continue;
                            }
                            let parent_val = self.lit_val(parent);
                            match parent_val {
                                // Clashing parent implies immediate contradiction.
                                1 => {
                                    self.mark_empty_clause();
                                    return true;
                                }
                                // Parent unassigned: derive and propagate unit `¬parent`.
                                0 => {
                                    let parent_unit = parent.negated();
                                    if self.learn_derived_unit(parent_unit, &[]) {
                                        return true;
                                    }
                                }
                                // Already false: nothing to do.
                                _ => {}
                            }
                        }
                    } else if lrat_parent_chain_enabled {
                        for (parent_unit, hints) in lrat_parent_chain_units {
                            let parent = parent_unit.negated();
                            let parent_val = self.lit_val(parent);
                            match parent_val {
                                1 => {
                                    self.mark_empty_clause();
                                    return true;
                                }
                                0 if self.learn_derived_unit(parent_unit, &hints) => {
                                    return true;
                                }
                                _ => {}
                            }
                        }
                    }
                }
            } else {
                // No conflict - backtrack and continue
                self.backtrack(0);
                debug_assert_eq!(
                    self.decision_level, 0,
                    "BUG: probe backtrack (no-conflict) did not reach level 0"
                );
            }

            // Validate watches after each probe iteration to detect corruption immediately.
            #[cfg(debug_assertions)]
            self.validate_watches_reverse(&format!(
                "after probe iter probe_lit={}",
                probe_lit.to_dimacs()
            ));

            // Mark this literal as probed at current fixed point
            self.inproc.prober.mark_probed(probe_lit, self.fixed_count);
        }

        // Record ticks for next effort computation and tick-threshold scheduling (#8148).
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        self.inproc.prober.set_last_search_ticks(ticks_now);
        self.cold.last_probe_ticks = ticks_now;

        // Post-condition: probe must always leave the solver at level 0.
        // If this fails, the solver's clause database state is inconsistent
        // and subsequent inprocessing or search will be unsound.
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: probe() did not restore decision level to 0"
        );

        // No UNSAT detected. Failed literals (if any) are tracked in
        // prober.stats().failed and their derived units are already propagated.
        false
    }
}
