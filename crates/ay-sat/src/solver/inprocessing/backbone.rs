// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backbone literal detection via binary-clause and bounded CDCL probing.
//!
//! Two complementary approaches (CaDiCaL backbone.cpp):
//!
//! 1. **Binary-clause backbone** (`backbone_binary`): For each variable, probe
//!    both polarities using binary-only propagation (`backbone_propagate2`).
//!    On conflict, extract a backbone unit via 1UIP resolution on the binary
//!    implication graph (`backbone_analyze`). Lightweight — called twice per
//!    inprobe round (CaDiCaL probe.cpp:945,951).
//!
//! 2. **Bounded CDCL backbone** (`backbone`): For each variable, run a bounded
//!    CDCL search (up to 32 conflicts) under each polarity assumption. More
//!    expensive but catches backbone literals that require long-clause
//!    propagation to reveal.

use super::super::*;
use crate::proof_manager::ProofAddKind;

/// Maximum conflicts per variable probe during bounded CDCL backbone detection.
/// Reduced from 32 to 16 (#8361): most backbone literals are found within
/// 5-10 conflicts. The binary-clause backbone (`backbone_binary`) avoids this
/// overhead entirely by using lightweight binary-only propagation.
const BACKBONE_PROBE_CONFLICT_LIMIT: u64 = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BackboneProbeResult {
    Sat,
    Unsat,
    Unknown,
}

impl Solver {
    /// Run backbone detection by bounded assumption probing.
    ///
    /// Each probe reuses the solver's regular BCP, conflict analysis, clause
    /// learning, and branching heuristics, but stops after a small number of
    /// conflicts. If a probe forces the opposite polarity at level 0, that
    /// opposite literal is a backbone literal.
    pub(in crate::solver) fn backbone(&mut self) -> bool {
        debug_assert_eq!(self.qhead, self.trail.len());
        if !self.require_level_zero() || self.has_empty_clause {
            return false;
        }

        // Flush stale ConflictAnalyzer seen flags before backbone probing (#8498).
        // Same rationale as backbone_binary: bounded CDCL probes interleave
        // conflict analyses that call clear(), and stale seen_to_clear entries
        // from prior CDCL search can cause seen_true_count mismatches.
        self.conflict.clear(&mut self.var_data);

        // Record tick watermark for CaDiCaL-style tick-threshold scheduling (#8090).
        self.cold.last_backbone_ticks = self.search_ticks[0] + self.search_ticks[1];

        // Increment backbone phase counter for round limit enforcement.
        // CaDiCaL: `++stats.backbone.phases` (backbone.cpp:533).
        self.cold.backbone_phases += 1;

        let saved_suppress_phase_saving = self.suppress_phase_saving;
        self.suppress_phase_saving = true;

        // Suppress reduce_db during backbone probing (#7929): backbone units
        // emitted to the DRAT proof must be RUP-derivable using clauses
        // currently in the proof. If reduce_db runs mid-probe and deletes
        // learned clauses that the unit's RUP chain depends on, the external
        // DRAT checker rejects the step. Deferring reduction until after all
        // backbone units are materialized preserves proof validity.
        let saved_suppress_reduce_db = self.suppress_reduce_db;
        self.suppress_reduce_db = true;

        // Disable chronological backtracking during backbone probing (#8135).
        // Backbone bounded-CDCL probes run short searches (32 conflicts) from
        // specific assumptions. Chrono-BT level correction in analyze_and_backtrack
        // can leave the trail in a state where no seen literal exists at the
        // adjusted decision level, causing analyze_conflict to crash (index
        // underflow scanning backward through the trail). Disabling chrono-BT
        // during probing ensures standard non-chronological backtracking, which
        // maintains the invariant that the trail always contains the expected
        // literals at each decision level.
        let saved_chrono_enabled = self.chrono_enabled;
        self.chrono_enabled = false;

        // OTFS is safe during backbone probing (#8439): the pivot's reason
        // pointer is now preserved after strengthening, so subsequent conflict
        // analyses in the bounded search resolve correctly. No suppression needed.

        // Disable JIT watch-scan BCP and JIT conflict processor during backbone
        // probing (#8372, #8356). The JIT BCP + conflict processor interact with
        // the repeated conflict-analysis/backtrack cycles of bounded CDCL probes
        // in ways that can leave the trail in an inconsistent state. The JIT
        // conflict processor sets seen flags directly in var_data via native code
        // and can produce incorrect counter values when interleaved with the
        // outer resolution loop's backward trail scan, causing trail exhaustion
        // panics. Performance impact is negligible: backbone runs at most ~10K
        // bounded probes. CaDiCaL avoids this entirely with simple binary-clause
        // propagation, not bounded CDCL search.
        #[cfg(feature = "jit")]
        let _saved_jit_conflict_processor = self.jit_conflict_processor.take();

        let mut found_backbone = false;

        // Budget: limit total conflicts during backbone to avoid pathological
        // preprocessing overhead. On crn_11_99_u (1287 vars), unbounded backbone
        // consumed 60K conflicts (2.4s) while the actual CDCL search needed only
        // 37K (0.67s). CaDiCaL uses tick-based effort limiting (backbone.cpp:542).
        //
        // AY's backbone uses bounded CDCL probing (up to 32 conflicts per
        // variable probe), which is more expensive than CaDiCaL's binary-clause
        // backbone propagation. Budget scales with formula class (#8150):
        //   Small (<10K vars, <100K cls): min(num_vars, 10K) -- generous
        //   Medium: min(num_vars, 5K) -- standard
        //   Large (>200K vars or >3M cls): min(num_vars, 2K) -- reduced
        let formula_class = FormulaClass::classify(self.num_vars, self.arena.active_clause_count());
        let backbone_conflict_budget = formula_class.backbone_conflict_budget(self.num_vars);
        let start_conflicts = self.num_conflicts;

        // Wall-clock limit for backbone probing (#8448).
        // AY's bounded CDCL backbone is much more expensive per-probe than
        // CaDiCaL's binary-clause backbone. On medium formulas like
        // FmlaEquivChain (54K vars, 394K clauses), 2000-conflict budget
        // costs 3.35s — 22% of the 15s SAT-COMP timeout. A wall-clock
        // limit caps backbone cost regardless of per-conflict expense,
        // preventing it from becoming a bottleneck on large-clause formulas.
        // CaDiCaL uses tick-based effort limits (backbone.cpp:542) which
        // achieve a similar effect.
        //
        // 200ms per call: with 4 inprocessing rounds and 3 backbone calls
        // per round (2x backbone_binary + 1x bounded CDCL), the bounded
        // CDCL backbone is capped at 800ms total. The binary backbone is
        // much cheaper and doesn't need this limit.
        let backbone_start = ay_core::time::Instant::now();
        const BACKBONE_WALL_LIMIT_MS: u64 = 200;
        // Deterministic per-call work baseline (#det wf_6503d3eb): in
        // deterministic mode the 200ms wall cap below becomes a search_ticks
        // delta budget against this baseline (machine-independent), while the
        // conflict budget continues to apply in both modes.
        let backbone_start_ticks = self.total_search_ticks();

        for var_idx in 0..self.num_vars {
            if self.has_empty_clause {
                break;
            }
            // Stop when conflict budget is exhausted.
            if self.num_conflicts.saturating_sub(start_conflicts) >= backbone_conflict_budget {
                break;
            }
            // Stop when the wall-clock (or, in deterministic mode, search_ticks)
            // budget is reached (#8448, #det wf_6503d3eb).
            if self.inproc_over_budget(
                backbone_start,
                backbone_start_ticks,
                BACKBONE_WALL_LIMIT_MS,
                crate::determinism::BACKBONE_TICK_BUDGET,
            ) {
                break;
            }
            if self.var_lifecycle.is_removed(var_idx) || self.var_is_assigned(var_idx) {
                continue;
            }

            let var = Variable(var_idx as u32);
            let positive = Literal::positive(var);
            let negative = positive.negated();

            if self.backbone_probe_literal(positive) == BackboneProbeResult::Unsat {
                found_backbone = true;
                if !self.has_empty_clause {
                    self.backbone_materialize_unit(negative);
                }
                continue;
            }

            if self.has_empty_clause || self.var_is_assigned(var_idx) {
                continue;
            }

            if self.backbone_probe_literal(negative) == BackboneProbeResult::Unsat {
                found_backbone = true;
                if !self.has_empty_clause {
                    self.backbone_materialize_unit(positive);
                }
            }
        }

        self.suppress_phase_saving = saved_suppress_phase_saving;
        self.suppress_reduce_db = saved_suppress_reduce_db;
        self.chrono_enabled = saved_chrono_enabled;
        // Bounded probes backtrack to level 0, but chronological compaction can
        // still leave root assignments on the trail with qhead lagging behind.
        // Drain those assignments here so the inprocessing caller sees the same
        // fully-propagated invariant it had on entry. Run this BEFORE restoring
        // JIT state so standard BCP handles the drain (#8372).
        if !self.has_empty_clause && self.qhead < self.trail.len() {
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
            }
        }

        // Restore JIT state (#8372). Done after final propagation drain so the
        // drain uses standard BCP (JIT is still disabled). Sync JIT qheads to
        // the current trail position so the JIT doesn't re-scan already-processed
        // literals when it resumes.

        if self.has_empty_clause {
            self.qhead = self.trail.len();
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: backbone() did not restore decision level to 0"
        );
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: backbone() left pending propagations (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        found_backbone || self.has_empty_clause
    }

    /// Probe a single assumption with bounded CDCL search.
    ///
    /// Returns:
    /// - `Unsat` if the assumption is forced false at level 0
    /// - `Sat` if a full model is found under the assumption
    /// - `Unknown` if the conflict budget is exhausted first
    fn backbone_probe_literal(&mut self, assumption: Literal) -> BackboneProbeResult {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: backbone probe started above level 0"
        );

        let start_conflicts = self.num_conflicts;
        let result = loop {
            if self.is_interrupted() {
                break BackboneProbeResult::Unknown;
            }

            if self.has_empty_clause {
                break BackboneProbeResult::Unsat;
            }

            if let Some(conflict_ref) = self.search_propagate() {
                if self.decision_level == 0 {
                    self.record_level0_conflict_chain(conflict_ref);
                    break BackboneProbeResult::Unsat;
                }

                self.conflicts_since_restart += 1;
                self.num_conflicts += 1;
                self.on_conflict_random_decision();
                self.analyze_and_backtrack(conflict_ref, "backbone probe", |_, _| {});
                continue;
            }

            if self.lit_val(assumption) < 0 {
                break BackboneProbeResult::Unsat;
            }

            if self.num_conflicts.saturating_sub(start_conflicts) >= BACKBONE_PROBE_CONFLICT_LIMIT {
                break BackboneProbeResult::Unknown;
            }

            if self.lit_val(assumption) == 0 {
                self.decide(assumption);
                continue;
            }

            let Some(var) = self.pick_next_decision_variable() else {
                break BackboneProbeResult::Sat;
            };
            self.decide(self.pick_phase(var));
        };

        if self.decision_level > 0 {
            self.backtrack_without_phase_saving(0);
        }

        if !self.has_empty_clause {
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return BackboneProbeResult::Unsat;
            }
            if self.lit_val(assumption) < 0 {
                return BackboneProbeResult::Unsat;
            }
        }

        result
    }

    /// Materialize a discovered backbone literal as an explicit unit clause.
    ///
    /// The bounded probe can leave the backbone literal assigned at level 0 via
    /// a longer learned reason. This helper turns that root assignment into an
    /// actual unit clause so later inprocessing passes and proof reconstruction
    /// can treat it as a first-class derived unit.
    fn backbone_materialize_unit(&mut self, unit: Literal) {
        let vi = unit.variable().index();
        debug_assert!(
            self.lit_val(unit) > 0,
            "BUG: materializing non-true backbone unit {unit:?}"
        );
        debug_assert_eq!(
            self.var_data[vi].level, 0,
            "BUG: materializing non-root backbone unit {unit:?}"
        );

        if self.backbone_has_explicit_unit_clause(unit) {
            return;
        }

        // Always use TrustedTransform: backbone units are sound (discovered
        // via failed literal probing) but may not be RUP-derivable in the
        // forward checker's clause DB, which tracks only a subset of the
        // solver's learned clauses. The suppress_reduce_db flag (#7929)
        // prevents mid-probe clause deletion that invalidates DRAT proofs,
        // and TrustedTransform prevents the forward checker's RUP assertion.
        let kind = ProofAddKind::TrustedTransform;
        let proof_id = self.proof_emit_unit(unit, &[], kind);
        if proof_id != 0 && self.cold.lrat_enabled {
            self.cold.next_clause_id = proof_id;
        }

        let unit_idx = self.add_clause_db(&[unit], true);
        self.mark_subsume_dirty_if_kept(unit_idx);
        if proof_id != 0 {
            self.record_unit_proof_id_for_lit(unit, proof_id);
        }
    }

    fn backbone_has_explicit_unit_clause(&self, unit: Literal) -> bool {
        // live_indices (husk adjudication): a garbage-kept unit husk must not
        // suppress proof_emit_unit — the checker already saw its deletion, so
        // skipping the emission makes later RUP chains fail (the exact #7929
        // failure this materialization defends against).
        self.arena
            .live_indices()
            .any(|idx| self.arena.len_of(idx) == 1 && self.arena.literal(idx, 0) == unit)
    }

    // ─── Binary-clause backbone detection (CaDiCaL backbone.cpp) ────────
    //
    // Lightweight backbone detection that propagates only over binary clauses.
    // Much cheaper than the bounded-CDCL probing in `backbone()` above.
    //
    // Algorithm (CaDiCaL `compute_backbone_round`, backbone.cpp:344-474):
    // For each candidate literal, decide it, propagate only over binary watch
    // entries, and on conflict perform 1UIP resolution on the binary implication
    // graph to extract a backbone unit. Each probe starts from level 0 so both
    // polarities of every variable get probed.
    //
    // CaDiCaL uses decision stacking (probing at increasing levels without
    // backtracking between successful probes) and multi-round iteration. AY
    // uses the simpler per-variable approach: for each variable, probe positive
    // then negative polarity, backtracking to level 0 between probes. This
    // guarantees both polarities are tested and is correct for all formulas.
    // The overhead vs stacking is minimal since binary propagation is O(binary
    // clauses per literal), and each probe processes very few watchers.

    /// Run binary-clause backbone detection.
    ///
    /// Returns `true` if any backbone units were found or UNSAT was derived.
    /// CaDiCaL: `binary_clauses_backbone()` (backbone.cpp:599-629).
    pub(in crate::solver) fn backbone_binary(&mut self) -> bool {
        debug_assert_eq!(self.qhead, self.trail.len());
        if !self.require_level_zero() || self.has_empty_clause {
            return false;
        }

        // Flush stale ConflictAnalyzer seen flags before backbone probing.
        // backbone_binary_analyze directly manipulates var_data seen bits
        // without updating ConflictAnalyzer bookkeeping (seen_to_clear,
        // seen_true_count). If stale seen flags from a prior analyze_conflict
        // remain, backbone_binary_analyze may clear a flag that was tracked
        // in seen_to_clear, causing the next conflict.clear() to find a
        // mismatch between seen_true_count and actual seen flags (#8498).
        self.conflict.clear(&mut self.var_data);

        // Full propagation before backbone to ensure clean state.
        // CaDiCaL backbone.cpp:607: `if (!propagate()) { ... }`
        if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            return true;
        }

        let mut found_any = false;

        // #sparse-gap Cluster B: WALL-BOUND the per-variable ring scan and
        // RESUME across calls via cold.backbone_binary_cursor. Unbounded,
        // this pass consumed 45-55s of a 60s budget on large sparse
        // main-track instances (4 measured; one spent 13.5s for 231 units),
        // starving search. The sibling bounded-CDCL backbone 200 lines up
        // already uses exactly this wall-cap pattern (#8448); kissat's
        // binary backbone achieves coverage through MANY cheap bounded calls
        // (backboneeffort ticks), not one exhaustive sweep. Sound: backbone
        // probing only fixes implied units / detects UNSAT, so stopping
        // early just leaves work undone — never changes satisfiability.
        const BACKBONE_BINARY_WALL_LIMIT_MS: u64 = 500;
        let wall_start = ay_core::time::Instant::now();
        // Deterministic per-call work baseline (#det wf_6503d3eb): the 500ms
        // wall cap below becomes a search_ticks delta budget in deterministic
        // mode (the cursor already spreads coverage across calls).
        let wall_start_ticks = self.total_search_ticks();
        let n = self.num_vars;
        if n == 0 {
            return false;
        }
        let start_cursor = self.cold.backbone_binary_cursor % n;

        for step in 0..n {
            let var_idx = (start_cursor + step) % n;
            if self.has_empty_clause {
                self.cold.backbone_binary_cursor = var_idx;
                break;
            }
            // Honor the deadline/interrupt + the wall (or, in deterministic
            // mode, search_ticks) cap: poll every 64 variables (the
            // closure-based `should_stop` is not threaded into inprocessing).
            if step & 63 == 0
                && (self.is_interrupted()
                    || self.inproc_over_budget(
                        wall_start,
                        wall_start_ticks,
                        BACKBONE_BINARY_WALL_LIMIT_MS,
                        crate::determinism::BACKBONE_BINARY_TICK_BUDGET,
                    ))
            {
                self.cold.backbone_binary_cursor = var_idx;
                break;
            }
            if self.var_lifecycle.is_removed(var_idx) || self.var_is_assigned(var_idx) {
                continue;
            }

            let var = Variable(var_idx as u32);
            let positive = Literal::positive(var);
            let negative = positive.negated();

            // Probe positive polarity.
            if !self.var_is_assigned(var_idx) && !self.has_empty_clause {
                if let Some(uip) = self.backbone_binary_probe(positive) {
                    found_any = true;
                    self.stats.backbone_binary_units += 1;

                    // Re-propagate binary after unit assignment.
                    // CaDiCaL backbone.cpp:409: `backbone_propagate2(ticks)`
                    if self.backbone_binary_check_conflict() {
                        break; // UNSAT
                    }

                    // If the UIP was the opposite polarity of the variable,
                    // no need to probe the negative polarity.
                    if uip == negative {
                        continue;
                    }
                }
            }

            // Probe negative polarity.
            if !self.var_is_assigned(var_idx) && !self.has_empty_clause {
                if let Some(_uip) = self.backbone_binary_probe(negative) {
                    found_any = true;
                    self.stats.backbone_binary_units += 1;

                    if self.backbone_binary_check_conflict() {
                        break; // UNSAT
                    }
                }
            }
        }

        // Ensure we are at level 0.
        if self.decision_level > 0 {
            self.backtrack_without_phase_saving(0);
        }

        // Run full propagation (binary + long clauses) to drain implications.
        // CaDiCaL backbone.cpp:461: `backbone_propagate(ticks)` does full BCP
        // after backbone probing completes.
        if !self.has_empty_clause {
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
            }
        }

        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: backbone_binary() did not restore decision level to 0"
        );

        found_any || self.has_empty_clause
    }

    /// Probe a single literal for binary backbone detection.
    ///
    /// Decides `probe_lit` at level 1, propagates over binary clauses only.
    /// On conflict, resolves via 1UIP on the binary implication graph.
    /// Returns `Some(uip)` if a backbone unit was found, `None` otherwise.
    ///
    /// CaDiCaL: `backbone_decision` + `backbone_propagate2` + `backbone_analyze`
    /// (backbone.cpp:335-342, 140-170, 215-254).
    fn backbone_binary_probe(&mut self, probe_lit: Literal) -> Option<Literal> {
        debug_assert_eq!(self.decision_level, 0);
        debug_assert!(!self.var_is_assigned(probe_lit.variable().index()));

        // Make decision at level 1.
        // CaDiCaL backbone.cpp:390: `backbone_decision(probe)`
        self.decide(probe_lit);

        // Binary-only propagation.
        let conflict = self.backbone_binary_propagate();

        if let Some((clause_ref, lit_a, lit_b)) = conflict {
            // 1UIP resolution on binary implication graph.
            // CaDiCaL backbone.cpp:401: `int uip = backbone_analyze(conflict, ticks)`
            let uip = self.backbone_binary_analyze(clause_ref, lit_a, lit_b);

            // Postcondition (#8498): backbone_binary_analyze uses its own local
            // seen_vars list to track and clear seen marks directly in var_data,
            // bypassing ConflictAnalyzer bookkeeping. Verify that no residual
            // seen marks remain after analysis. A leak here would corrupt the
            // next ConflictAnalyzer.clear() or analyze_conflict() call.
            #[cfg(debug_assertions)]
            {
                debug_assert!(
                    self.conflict.seen_to_clear.is_empty(),
                    "BUG: ConflictAnalyzer.seen_to_clear non-empty after \
                     backbone_binary_analyze — external seen manipulation \
                     leaked into ConflictAnalyzer bookkeeping (#8498)"
                );
            }

            // Backtrack to level 0.
            self.backtrack_without_phase_saving(0);

            // LRAT soundness gate (second root cause of the manol-pipe-c9
            // default-features failure): backbone derives its UIP via a
            // binary-implication-graph 1UIP that does NOT collect an LRAT hint
            // chain, so every backbone unit is emitted as a hidden
            // TrustedTransform (see backbone_materialize_unit, and
            // learn_derived_unit's empty-hint downgrade). Such units are
            // stripped from the LRAT file, so a later search-learned clause that
            // resolves through a backbone variable's level-0 assignment has no
            // checker-visible antecedent and its RUP hint chain fails
            // ("multiple literals unassigned in hint ...").
            //
            // Backbone units are a sound optimization, not required for UNSAT,
            // so in LRAT mode we do NOT commit them. Backbone detection still
            // runs (cheap, and useful in DRAT/non-proof modes); we just refrain
            // from injecting an uncertifiable level-0 assignment. This mirrors
            // the probe/transred/intree empty-hint skips and the BVE/sweep LRAT
            // clamps. DRAT and non-proof modes keep the original behaviour.
            if self.cold.lrat_enabled {
                return None;
            }

            // Assign the UIP as a level-0 backbone unit.
            // CaDiCaL backbone.cpp:403: `backbone_unit_assign(uip)`
            if self.lit_val(uip) > 0 {
                // Already true at level 0 — materialize as explicit unit clause.
                self.backbone_materialize_unit(uip);
            } else if self.lit_val(uip) == 0 {
                // Unassigned — learn as derived unit.
                if self.learn_derived_unit(uip, &[]) {
                    // Conflict at level 0 → UNSAT.
                    return Some(uip);
                }
            } else {
                // Negation already true → contradiction → UNSAT.
                self.mark_empty_clause();
                return Some(uip);
            }

            Some(uip)
        } else {
            // No conflict: probe_lit is not a failed backbone candidate.
            // Backtrack to level 0 and continue.
            self.backtrack_without_phase_saving(0);
            None
        }
    }

    /// Binary-only propagation for backbone detection.
    ///
    /// Propagates `self.trail[self.qhead..]` over ONLY binary watch entries.
    /// Returns `Some((clause_ref, lit_a, lit_b))` on conflict (the two literals
    /// of the conflicting binary clause), or `None` if no conflict.
    ///
    /// CaDiCaL: `backbone_propagate2` (backbone.cpp:140-170).
    fn backbone_binary_propagate(&mut self) -> Option<(ClauseRef, Literal, Literal)> {
        while self.qhead < self.trail.len() {
            let trail_lit = self.trail[self.qhead];
            self.qhead += 1;
            let neg_lit = trail_lit.negated();

            // Scan binary watchers of the negated literal.
            let num_watchers = self.watches.len_of(neg_lit);
            for i in 0..num_watchers {
                if !self.watches.is_binary(neg_lit, i) {
                    // Binary entries are partitioned to the front.
                    // Once we hit a non-binary entry, we're done with binaries.
                    break;
                }

                let other = self.watches.blocker(neg_lit, i);
                let other_val = self.lit_val(other);

                if other_val > 0 {
                    // Other literal already true — clause satisfied.
                    continue;
                }

                let clause = self.watches.clause_ref(neg_lit, i);

                if other_val < 0 {
                    // Both literals false — binary conflict.
                    // CaDiCaL backbone.cpp:157: `conflict = w.clause`
                    return Some((clause, neg_lit, other));
                }

                // Other literal unassigned — propagate.
                // CaDiCaL backbone.cpp:163: `backbone_assign(w.blit, w.clause)`
                self.enqueue_bcp_binary(other, clause);
            }
        }

        None
    }

    /// 1UIP resolution on the binary implication graph.
    ///
    /// Given a binary conflict clause (with literals `lit_a` and `lit_b`, both
    /// false), walks backward through the trail resolving binary reasons until
    /// a single UIP is found. Returns the UIP literal (which should be assigned
    /// true at level 0).
    ///
    /// CaDiCaL: `backbone_analyze` (backbone.cpp:215-254).
    fn backbone_binary_analyze(
        &mut self,
        _conflict_clause: ClauseRef,
        lit_a: Literal,
        lit_b: Literal,
    ) -> Literal {
        // Mark both conflict clause literals as seen.
        // CaDiCaL backbone.cpp:218-221
        //
        // Note (#8498): this directly manipulates var_data[].flags (seen bit)
        // without going through ConflictAnalyzer::mark_seen. The seen flags
        // are cleaned up via the local `seen_vars` vector before returning.
        // However, if these variables overlap with ConflictAnalyzer::seen_to_clear
        // entries from a prior analysis, the clear/set cycle may leave the flag
        // in a different state than ConflictAnalyzer expects. ConflictAnalyzer::clear()
        // handles this by resetting its counter unconditionally.
        let vi_a = lit_a.variable().index();
        let vi_b = lit_b.variable().index();
        self.var_data[vi_a].set_seen(true);
        self.var_data[vi_b].set_seen(true);
        let mut seen_vars: Vec<usize> = vec![vi_a, vi_b];

        // Walk backward through trail for 1UIP.
        // CaDiCaL backbone.cpp:227-253
        for t in (0..self.trail.len()).rev() {
            let lit = self.trail[t];
            let vi = lit.variable().index();

            if !self.var_data[vi].is_seen() {
                continue;
            }

            // Get the binary reason for this literal.
            let reason_raw = self.var_data[vi].reason;

            if reason_raw == NO_REASON {
                // Decision literal — this is the UIP.
                // CaDiCaL backbone.cpp:245: `return other`
                // Clear all seen flags.
                for &sv in &seen_vars {
                    self.var_data[sv].set_seen(false);
                }
                // The UIP is the negation of this literal (the literal that
                // must be true). CaDiCaL backbone_analyze returns the UIP
                // directly as the literal to assign true.
                return lit.negated();
            }

            // Resolve with the reason clause.
            // CaDiCaL backbone.cpp:233-237: reason is a binary clause,
            // the "other" literal is the one we need to mark seen.
            //
            // The reason can be either a clause reference or a binary literal reason.
            let other_lit = if is_binary_literal_reason(reason_raw) {
                // Jump reason: the other literal is encoded directly.
                Literal(binary_reason_lit(reason_raw))
            } else if is_clause_reason(reason_raw) {
                // Clause reason: extract the other literal from the binary clause.
                let clause_idx = reason_raw as usize;
                let lits = self.arena.literals(clause_idx);
                debug_assert_eq!(
                    lits.len(),
                    2,
                    "BUG: backbone_binary_analyze expects binary reasons, got {} literals",
                    lits.len()
                );
                // Extract the other literal from the binary reason clause.
                // CaDiCaL uses XOR trick (backbone.cpp:237), but Literal
                // doesn't implement BitXor — use direct comparison.
                if lits[0] == lit {
                    lits[1]
                } else {
                    lits[0]
                }
            } else {
                // Should not happen — all propagated literals must have reasons.
                debug_assert!(
                    false,
                    "BUG: backbone_binary_analyze: unexpected reason {reason_raw:#x}"
                );
                // Clear seen and bail with the negation of this literal.
                for &sv in &seen_vars {
                    self.var_data[sv].set_seen(false);
                }
                return lit.negated();
            };

            let other_vi = other_lit.variable().index();
            if !self.var_data[other_vi].is_seen() {
                self.var_data[other_vi].set_seen(true);
                seen_vars.push(other_vi);
            } else {
                // Already seen — this is the UIP.
                // CaDiCaL backbone.cpp:244-245: `if (!f_o.seen) { ... } else { return other; }`
                // Return the literal to assign TRUE at level 0. The UIP
                // literal `other_lit` comes from a clause, so it IS the
                // literal that needs to be satisfied (assigned true).
                for &sv in &seen_vars {
                    self.var_data[sv].set_seen(false);
                }
                return other_lit;
            }
        }

        // Should not reach here if the conflict is valid.
        debug_assert!(
            false,
            "BUG: backbone_binary_analyze exhausted trail without finding UIP"
        );
        // Clear seen flags.
        for &sv in &seen_vars {
            self.var_data[sv].set_seen(false);
        }
        // Return the negation of the probe literal as a fallback.
        self.trail[self.trail_lim[0]].negated()
    }

    /// Check for binary propagation conflict after a backbone unit was assigned.
    ///
    /// Returns `true` if a conflict was detected (UNSAT), `false` otherwise.
    fn backbone_binary_check_conflict(&mut self) -> bool {
        // Propagate the newly assigned unit over binary clauses.
        if let Some((_clause, _lit_a, _lit_b)) = self.backbone_binary_propagate() {
            // Conflict after backbone unit propagation → UNSAT.
            // CaDiCaL backbone.cpp:410-415
            self.mark_empty_clause();
            return true;
        }
        false
    }
}
