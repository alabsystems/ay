// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared conflict-analysis skeleton used by all CDCL loops.
//!
//! Extracted from solve/mod.rs for maintainability (#5142).
//! Extended with `on_learned` hook for assumption core extraction (#4791 Wave 3).

use super::super::*;
use crate::solver_log::solver_log;

impl Solver {
    /// Shared conflict-analysis skeleton used by all CDCL loops.
    ///
    /// This is Wave 1 of loop unification: keep per-loop control flow where it
    /// differs, but centralize analyze -> chrono backtrack -> learn -> enqueue.
    pub(in crate::solver) fn analyze_and_backtrack<F>(
        &mut self,
        conflict_ref: ClauseRef,
        context: &'static str,
        before_backtrack: F,
    ) where
        F: FnMut(&mut Self, u32),
    {
        self.analyze_and_backtrack_inner(conflict_ref, context, before_backtrack, |_, _, _| {})
    }

    /// Extended conflict-analysis skeleton with a post-analysis hook.
    ///
    /// The `on_learned` callback is invoked after conflict analysis but before
    /// backtrack, receiving the learned clause and actual backtrack level. This
    /// is used by assumption-based solving (#4791 Wave 3) to extract the failed
    /// assumption core from the learned clause while variable levels are still
    /// valid (pre-backtrack).
    pub(in crate::solver) fn analyze_and_backtrack_with_core_hook<F, G>(
        &mut self,
        conflict_ref: ClauseRef,
        context: &'static str,
        before_backtrack: F,
        on_learned: G,
    ) where
        F: FnMut(&mut Self, u32),
        G: FnMut(&Self, &[Literal], u32),
    {
        self.analyze_and_backtrack_inner(conflict_ref, context, before_backtrack, on_learned)
    }

    /// Core conflict-analysis skeleton shared by all CDCL loops.
    ///
    /// Handles: chrono BT forced path, conflict-level backtrack, level-0 UNSAT,
    /// 1UIP analysis, OTFS Branch B, learned clause creation, eager subsumption,
    /// VSIDS decay, and reduce_db scheduling.
    fn analyze_and_backtrack_inner<F, G>(
        &mut self,
        conflict_ref: ClauseRef,
        context: &'static str,
        mut before_backtrack: F,
        mut on_learned: G,
    ) where
        F: FnMut(&mut Self, u32),
        G: FnMut(&Self, &[Literal], u32),
    {
        let prune_conflict_experiments = self.should_prune_conflict_analysis_experiments();

        // A global unit clause is a root fact regardless of where its
        // conflicting assignment was made. This path is especially important
        // for unit theory axioms queued by add_theory_lemma: callers may ignore
        // the returned ClauseRef, and the clause has no watches that could
        // rediscover it after a fallback backtrack. Handle it before the
        // chrono/non-chrono split so both modes install the unit at level 0
        // (#1696).
        if self.arena.len_of(conflict_ref.index()) == 1 {
            before_backtrack(self, 0);
            self.backtrack(0);
            if !self.install_theory_unit_at_root(conflict_ref) {
                self.record_level0_conflict_chain(conflict_ref);
                return;
            }
            self.stats.forced_backtracks += 1;
            return;
        }

        // CaDiCaL analyze.cpp:962-1018: when chronological backtracking is
        // enabled, find the actual conflict level (max level in conflict clause)
        // and backtrack to it before analysis. This ensures decision_level
        // equals the true conflict level so 1UIP analysis counts current-level
        // literals correctly. Without this, assignment_level() corrections make
        // some conflict-clause literals appear below decision_level.
        if self.chrono_enabled {
            let (conflict_level, forced) = self.find_conflict_level(conflict_ref);

            // CaDiCaL analyze.cpp:977-1004: "forced" path — single literal at
            // the highest level. Use conflict clause as driving clause directly,
            // skip 1UIP analysis entirely (SAT'18 paper Alg.1 lines 4-6).
            if let Some(forced_lit) = forced {
                if conflict_level > 0 {
                    let bt_level = conflict_level - 1;
                    before_backtrack(self, bt_level);
                    self.backtrack(bt_level);
                    if bt_level == 0
                        && !self
                            .var_lifecycle
                            .is_inactive(forced_lit.variable().index())
                    {
                        self.fixed_count += 1;
                        self.var_lifecycle.mark_fixed(forced_lit.variable().index());
                        self.l0_gc_dirty[forced_lit.variable().index()] = true;
                    }
                    // After backtrack, forced_lit is unassigned while all other
                    // conflict clause literals remain false. The clause becomes
                    // unit, propagating forced_lit = true (CaDiCaL analyze.cpp:998).
                    // CaDiCaL forced path (analyze.cpp:988-1004): no bump_clause,
                    // no vsids.decay(), no reduce_db. The conflict was not analyzed,
                    // so bumping/decay provides no useful search guidance.
                    self.enqueue(forced_lit, Some(conflict_ref));
                    self.stats.forced_backtracks += 1;
                    return;
                }
            }

            // Backtrack to conflict_level so decision_level == conflict_level
            // for correct 1UIP analysis (CaDiCaL analyze.cpp:1017).
            if conflict_level < self.decision_level {
                before_backtrack(self, conflict_level);
                self.backtrack(conflict_level);
            }

            // CaDiCaL analyze.cpp:1022-1028: after backtracking to
            // conflict_level, if we're now at level 0, learn the empty
            // clause (UNSAT) and return. analyze_conflict requires
            // decision_level > 0. With assignment_level corrections, all
            // conflict clause literals can be at level 0 even when the
            // conflict was detected at a higher decision_level (#6993).
            if self.decision_level == 0 {
                self.record_level0_conflict_chain(conflict_ref);
                return;
            }
        }

        // Trail exhaustion guard (#8479): analyze_conflict returns None when
        // the backward trail scan fails to find a current-level seen literal.
        // Backtrack to level 0 and continue — no incorrect clause is learned.
        let Some(result) = self.analyze_conflict(conflict_ref) else {
            before_backtrack(self, 0);
            self.backtrack(0);
            if self.active_branch_heuristic == BranchHeuristic::Evsids {
                self.vsids.decay();
            } else if self.active_branch_heuristic == BranchHeuristic::Chb {
                self.vsids.decay_evsids_dormant();
            }
            return;
        };

        debug_assert!(
            !result.learned_clause.is_empty(),
            "BUG: analyze_conflict returned empty learned clause ({context})"
        );
        debug_assert!(
            result.backtrack_level < self.decision_level,
            "BUG: backtrack_level ({}) >= decision_level ({}) ({context})",
            result.backtrack_level,
            self.decision_level,
        );
        // LBD is computed pre-minimize (CaDiCaL analyze.cpp:1193 before shrink).
        // Post-minimize, the clause can be shorter than LBD because minimization
        // removes redundant literals without recomputing the level count. This is
        // correct CaDiCaL behavior — the pre-minimize LBD check in
        // conflict_analysis.rs:615 is the authoritative invariant.

        let actual_backtrack_level = self.compute_chrono_backtrack_level(result.backtrack_level);

        if self.cold.trace_ext_conflict {
            eprintln!(
                "[ANALYZE] dl={} bt_level={} actual_bt={} learned_clause={:?} lbd={}",
                self.decision_level,
                result.backtrack_level,
                actual_backtrack_level,
                result
                    .learned_clause
                    .iter()
                    .map(|l| (l.variable().index(), l.is_positive()))
                    .collect::<Vec<_>>(),
                result.lbd,
            );
            for lit in &result.learned_clause {
                let var = lit.variable();
                let level = self.var_data[var.index()].level;
                let val = self.var_value_from_vals(var.index());
                eprintln!(
                    "[ANALYZE]   var={} pos={} level={} val={:?}",
                    var.index(),
                    lit.is_positive(),
                    level,
                    val
                );
            }
        }

        // Post-analysis hook: let callers inspect the learned clause and backtrack
        // level before the clause is consumed. Variable levels are still valid
        // (pre-backtrack). Used by assumption-based solving to extract the failed
        // assumption core (#4791 Wave 3).
        on_learned(&*self, &result.learned_clause, actual_backtrack_level);
        self.export_portfolio_shared_clause(&result.learned_clause, result.lbd);

        // Notify programmatic observer of the learned clause (#8155).
        if !prune_conflict_experiments {
            self.notify_observer_learn(result.learned_clause.len() as u32, result.lbd);
        }

        // Update trail-length EMA before backtracking (trail is still at full
        // length). This feeds the restart-blocking heuristic (Audemard & Simon
        // SAT 2012). CaDiCaL updates this in analyze.cpp before backtrack.
        self.update_trail_ema();

        before_backtrack(self, actual_backtrack_level);
        self.backtrack(actual_backtrack_level);

        // Extract UIP before consuming the learned clause (avoid clone)
        let uip = result.learned_clause[0];

        // Track new level-0 unit: CaDiCaL increments stats.all.fixed for
        // every variable fixed at level 0, not just during probe/sweep.
        // This ensures collect_level0_garbage() fires after CDCL unit learning,
        // cleaning stale false/true literals before the next inprocessing round.
        if actual_backtrack_level == 0 && !self.var_lifecycle.is_inactive(uip.variable().index()) {
            self.fixed_count += 1;
            // CaDiCaL: mark_fixed() in flags.cpp:5-32. Fixed variables are
            // permanently assigned and can never be reactivated or eliminated.
            self.var_lifecycle.mark_fixed(uip.variable().index());
            self.l0_gc_dirty[uip.variable().index()] = true;
        }
        debug_assert!(
            !self.var_is_assigned(uip.variable().index()),
            "BUG: UIP {uip:?} still assigned after backtrack to level {actual_backtrack_level} ({context})",
        );

        // OTFS Branch B: use existing strengthened clause as driving
        // clause instead of creating a new learned clause.
        let driving_off = if let Some(driving_ref) = result.otfs_driving_clause {
            self.update_lbd_ema(result.lbd);
            self.enqueue(uip, Some(driving_ref));
            self.conflict.return_learned_buf(result.learned_clause);
            self.conflict.return_chain_buf(result.resolution_chain);
            solver_log!(
                self,
                "OTFS Branch B: backtrack to level {} drive {} assert {}",
                actual_backtrack_level,
                driving_ref.0,
                uip.to_dimacs()
            );
            Some(driving_ref.0 as usize)
        } else {
            // DIP-ERCL (#8440): attempt to split the learned clause using
            // Dual Implication Points. When successful, two shorter clauses
            // plus Tseitin definition clauses replace the single 1UIP clause.
            // The post-DIP clause is asserting and drives propagation.
            let dip_result = if prune_conflict_experiments {
                None
            } else {
                self.try_dip_ercl(&result.learned_clause)
            };

            if let Some(ercl) = dip_result {
                self.set_diagnostic_pass(DiagnosticPass::Learning);
                let (_pre_ref, post_ref, _ext_var) = self.apply_dip_ercl(ercl);
                self.clear_diagnostic_pass();
                self.update_lbd_ema(result.lbd);
                self.enqueue(uip, Some(post_ref));
                self.conflict.return_learned_buf(result.learned_clause);
                self.conflict.return_chain_buf(result.resolution_chain);
                solver_log!(
                    self,
                    "DIP-ERCL: backtrack to level {} post-DIP clause {} assert {}",
                    actual_backtrack_level,
                    post_ref.0,
                    uip.to_dimacs()
                );
                Some(post_ref.0 as usize)
            } else {
                self.set_diagnostic_pass(DiagnosticPass::Learning);
                let learned_ref = self.add_conflict_learned_clause(
                    result.learned_clause,
                    result.lbd,
                    result.resolution_chain,
                );
                self.clear_diagnostic_pass();
                self.update_lbd_ema(result.lbd);
                self.enqueue(uip, Some(learned_ref));
                solver_log!(
                    self,
                    "backtrack to level {} learn clause {} assert {}",
                    actual_backtrack_level,
                    learned_ref.0,
                    uip.to_dimacs()
                );
                Some(learned_ref.0 as usize)
            }
        };

        // CaDiCaL analyze.cpp:1285-1286: eager subsumption of recently learned
        // clauses using the driving (newly learned or OTFS-strengthened) clause.
        if !prune_conflict_experiments {
            if let Some(off) = driving_off {
                self.eager_subsume(off);
            }
        }

        // TLA trace: after analyze+backtrack+learn, back to propagating
        if !prune_conflict_experiments {
            self.tla_trace_step(
                CdclTraceState::Propagating,
                Some(CdclTraceAction::AnalyzeAndLearn),
            );
        }

        // CaDiCaL analyze.cpp:196-197: score increment growth gated by
        // stable mode. In focused mode EVSIDS scores aren't bumped, so
        // growing the increment is pure waste and inflates it for the
        // next stable phase.
        if self.active_branch_heuristic == BranchHeuristic::Evsids {
            self.vsids.decay();
        } else if self.active_branch_heuristic == BranchHeuristic::Chb {
            self.vsids.decay_evsids_dormant();
        }
        if self.should_reduce_db() {
            self.reduce_db();
        }

        // DIP-ERCL extension variable garbage collection (#8440).
        if !prune_conflict_experiments {
            self.dip_gc_if_needed();
        }
    }

    /// IC3-optimized conflict analysis + backtrack + learn (#8569).
    ///
    /// Stripped-down version of `analyze_and_backtrack_inner` that skips
    /// features unnecessary for IC3 workloads:
    /// - Chronological backtracking (IC3 uses non-chrono BT)
    /// - OTFS Branch B (on-the-fly strengthening)
    /// - DIP-ERCL (dual implication point extension)
    /// - Eager subsumption of learned clauses
    /// - Trail-length EMA updates (IC3 uses Luby restarts)
    /// - TLA trace events
    /// - Observer notifications
    /// - Diagnostic pass tracking
    ///
    /// Keeps: 1UIP analysis, NCB backtrack, learned clause creation, VSIDS decay.
    ///
    /// The `on_learned` callback receives the learned clause and backtrack level
    /// for UNSAT core extraction (same as the generic version).
    pub(in crate::solver) fn analyze_and_backtrack_ic3<G>(
        &mut self,
        conflict_ref: ClauseRef,
        mut on_learned: G,
    ) where
        G: FnMut(&Self, &[Literal], u32),
    {
        let ic3 = self.cold.ic3_mode;

        // IC3-optimized conflict analysis (#8569 Gap 5): use the stripped
        // 1UIP analysis that skips OTFS, tick accounting, clause bumping,
        // streaming core, JIT processing, and ghost guards. This reduces
        // per-conflict overhead by ~50% for IC3's typical tiny conflicts.
        let Some(result) = self.analyze_conflict_ic3(conflict_ref) else {
            // Trail exhaustion guard (#8479).
            if ic3 {
                self.backtrack_ic3(0);
            } else {
                self.backtrack(0);
            }
            self.vsids.decay();
            return;
        };

        debug_assert!(!result.learned_clause.is_empty());
        debug_assert!(result.backtrack_level < self.decision_level);

        // IC3 learned clause verification (#8661): in debug builds, verify
        // that the learned clause is structurally valid before backtracking.
        // This catches domain-BCP-induced soundness bugs where the conflict
        // analysis produces invalid clauses due to incomplete propagation.
        #[cfg(debug_assertions)]
        self.verify_ic3_learned_clause(&result.learned_clause, conflict_ref);

        // Non-chronological backtrack (no chrono-BT computation).
        let bt_level = result.backtrack_level;

        // Post-analysis hook for UNSAT core extraction.
        on_learned(&*self, &result.learned_clause, bt_level);

        // IC3-optimized backtrack (#8569): skips phase saving, target/best
        // phase updates, LSCB lambda checks, and vmtf_on_unassign.
        // Falls back to standard backtrack when ic3_mode is not set (tests).
        if ic3 {
            self.backtrack_ic3(bt_level);
        } else {
            self.backtrack(bt_level);
        }

        let uip = result.learned_clause[0];

        // Track level-0 unit.
        if bt_level == 0 && !self.var_lifecycle.is_inactive(uip.variable().index()) {
            self.fixed_count += 1;
            self.var_lifecycle.mark_fixed(uip.variable().index());
            self.l0_gc_dirty[uip.variable().index()] = true;
        }

        debug_assert!(
            !self.var_is_assigned(uip.variable().index()),
            "BUG: IC3 UIP {uip:?} still assigned after backtrack to level {bt_level}",
        );

        // Skip OTFS and DIP-ERCL — always create the standard learned clause.
        let learned_ref = self.add_conflict_learned_clause(
            result.learned_clause,
            result.lbd,
            result.resolution_chain,
        );
        // IC3-optimized enqueue (#8569): skip phase saving, ChrBT level
        // computation, stale literal guards, and tracing. The UIP is always
        // a long-clause reason (the learned clause just created).
        // Falls back to standard enqueue when ic3_mode is not set (tests).
        if ic3 {
            self.enqueue_bcp_ic3(uip, learned_ref);
        } else {
            self.enqueue(uip, Some(learned_ref));
        }

        // VSIDS decay.
        self.vsids.decay();
    }
}
