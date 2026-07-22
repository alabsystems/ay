// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental inprocessing: lightweight simplification between incremental solves.
//!
//! When the solver is in incremental mode (`has_been_incremental`), the full
//! inprocessing pipeline (`run_restart_inprocessing`) still runs but destructive
//! techniques (BVE, BCE, decompose, etc.) bail out via body guards. This module
//! provides `run_incremental_inprocessing()` which is called at the start of
//! `solve_with_assumptions()` to run the safe subset of techniques between
//! incremental calls. This prevents clause database bloat in IC3 frame solvers
//! that accumulate hundreds of learned clauses per solve call (#8208).
//!
//! Safe techniques for incremental mode:
//! - Level-0 garbage collection (removes satisfied clauses)
//! - Subsumption (non-destructive: strengthens/removes subsumed clauses)
//! - Vivification (clause strengthening via BCP, no variable elimination)
//! - Transitive reduction (removes redundant binary implications)
//! - **Scoped BVE** (#8162): when push() scope is active, BVE can eliminate
//!   variables introduced after the scope marker. On pop(), eliminated
//!   variables are restored from the reconstruction stack. This enables
//!   BVE for IC3/PDR workloads that do thousands of tiny incremental
//!   solves. Only runs when `has_scoped_bve()` returns true.
//!
//! NOT safe in incremental mode (need reconstruction stack or scope tracking):
//! - BCE, CCE, decompose, sweep, congruence, factor, condition, SBVA

use super::super::*;

/// Environment override for the incremental inprocessing clause divisor
/// (#maxsat-inproc-throttle). `AY_SAT_INCR_INPROBE_DIV=N` (N>0) forces the
/// divisor to N regardless of the per-solver configured value; `0` forces the
/// legacy flat 500-conflict interval. Unset leaves the configured value
/// (`cold.incremental_inprobe_clause_divisor`) in force. Experimentation knob.
///
/// Returns `Some(Some(n))` to force divisor n, `Some(None)` to force legacy,
/// `None` when unset (use the configured field).
fn incremental_inprobe_env_override() -> Option<Option<u64>> {
    use std::sync::OnceLock;
    static V: OnceLock<Option<Option<u64>>> = OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("AY_SAT_INCR_INPROBE_DIV")
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
            .map(|n| if n > 0 { Some(n) } else { None })
    })
}

impl Solver {
    /// Run lightweight inprocessing between incremental solve calls (#8208).
    ///
    /// Called at the start of `solve_with_assumptions()` when the solver is at
    /// decision level 0 and enough conflicts have accumulated. Runs techniques
    /// that are safe in incremental mode: subsumption, vivification, transitive
    /// reduction, level-0 garbage collection, and scoped BVE (#8162) when a
    /// push() scope is active.
    ///
    /// Scoped BVE (#8162): when `has_scoped_bve()` returns true, BVE runs with
    /// a scope variable floor that prevents elimination of variables from the
    /// base formula. Variables eliminated during a scope are restored on pop()
    /// via `restore_scoped_bve_eliminations()`. This unlocks BVE for IC3/PDR
    /// workloads that do thousands of tiny incremental solves.
    ///
    /// Returns `true` if UNSAT was derived at decision level 0.
    pub(in crate::solver) fn run_incremental_inprocessing(&mut self) -> bool {
        // ── Preconditions ────────────────────────────────────────────────
        if self.is_interrupted() {
            return false;
        }
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: run_incremental_inprocessing at decision level {}",
            self.decision_level,
        );
        if self.decision_level != 0 {
            return false;
        }

        // #A2b degrade checkpoint: decision level 0, between clause
        // operations — the documented safe point. If the search-time proof
        // bookkeeping budget is exhausted (level-0 unit materialization
        // and/or inprocessing LRAT clause-replacement charges), drop to
        // no-proof search NOW: disables the LRAT clause trace and restores
        // the pristine (proof-unclamped) inprocessing controls. The verdict
        // is unaffected; the synthesized-default certificate fails closed
        // with the existing honest "no proof certificate emitted" warning.
        // Explicit proof modes never have a budget and never reach this.
        if self.cold.proof_bookkeeping_budget == Some(0) {
            self.degrade_proof_bookkeeping_after_exhaustion();
        }

        // ── Lightweight maintenance ─────────────────────────────────────
        self.drain_all_pending_garbage();
        if self.propagate_check_unsat() {
            return true;
        }

        // ── Level-0 garbage collection ──────────────────────────────────
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
            "BUG: unpropagated literals at incremental inprocessing entry (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        // Reset minimal trail rewind tracker (#8095).
        self.earliest_affected_trail_pos = None;

        // Snapshot JIT state before inprocessing so we can decide whether
        // to recompile afterwards (#8202).

        let round_start = ay_core::time::Instant::now();
        let pass_time_baseline: [u64; solver_stats::INPROCESS_TIMING_LABELS.len()] =
            self.stats.inprocessing_time_ns;
        let clauses_before = self.num_clauses();
        let mut passes_run: Vec<&'static str> = Vec::with_capacity(4);

        // ── Subsumption ─────────────────────────────────────────────────
        // Non-destructive: removes subsumed clauses and strengthens via
        // self-subsumption. Safe in incremental mode — no reconstruction
        // stack, no variable elimination.
        let should_subsume = self.should_subsume();
        if should_subsume {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Subsume);
        }
        if should_subsume {
            self.jit_invalidate_for_structural_pass();
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Subsume, Self::subsume);
            passes_run.push("subsume");
            self.cold.subsume_ran_since_bve = true; // #8502: signal pre-BVE guard
            if self.propagate_check_unsat() {
                return true;
            }
        }

        if self.is_interrupted() {
            return false;
        }

        // ── Scoped BVE (#8162) ─────────────────────────────────────────
        // When push() scope is active, BVE can eliminate variables
        // introduced after the scope marker. On pop(), eliminated
        // variables are restored from the reconstruction stack
        // (CaDiCaL restore.cpp pattern). This enables clause-count
        // reduction for IC3/PDR workloads that accumulate hundreds of
        // learned clauses per solve call without BVE cleanup.
        //
        // Guard: only runs when has_scoped_bve() is true (push() was
        // called and scope_var_starts is non-empty). The BVE body
        // already checks has_been_incremental && !has_scoped_bve()
        // and bails out, so the scope_var_floor filtering is active.
        if self.has_scoped_bve() && self.should_bve() {
            self.jit_invalidate_for_structural_pass();
            let clauses_before_bve = self.arena.irredundant_count();

            // SOUNDNESS (push/pop clause-leak root cause): scope selector
            // variables MUST remain unassigned in vals[] during scoped BVE.
            //
            // Scoped clauses are stored as [C, +S] where S is the scope
            // selector. The selector literal is the clause's *scope guard*:
            // any resolvent derived from a scoped parent inherits +S, which
            // is exactly the "max assertion level among derivation
            // ancestors" tag expressed in the selector algebra. pop()'s
            // gc_scoped_clauses() then reclaims those resolvents because
            // they contain +S.
            //
            // The previous #8579 fixup temporarily set vals[+S] = -1
            // ("scope-active polarity") before BVE. BVE's root-false literal
            // pruning then STRIPPED +S from every resolvent, storing
            // guardless IRREDUNDANT clauses derived from scoped assertions.
            // Those clauses survive pop() — gc_scoped_clauses() only deletes
            // clauses containing +S, the Z3 PR #9221 sweep only deletes
            // LEARNED clauses, and restore_scoped_bve_eliminations() only
            // reactivates variables. A guardless resolvent derived from a
            // popped scope's assertions can flip a later satisfiable
            // check-sat to a spurious UNSAT (it was only masked by the
            // arena-vs-ledger rebuild in reset_search_state, #7987).
            //
            // With S unassigned, the #8579 scenario (environment units
            // falsifying all non-selector literals of scoped parents) yields
            // the resolvent [+S] — a unit clause that is genuinely entailed
            // by the clause database (the scoped assertions contradict the
            // environment), propagates S=true at level 0, and correctly
            // makes the in-scope solve UNSAT while staying consistent with
            // pop()'s own [+S] disable unit. No special-casing required.

            // Disconnect watches for BVE (CaDiCaL elim.cpp:1046 pattern).
            // BVE uses occurrence lists, not the 2WL watch graph.
            let arena_baseline = self.arena.len();
            self.cold.instantiate_rebuilt_watches = false;
            self.watches_disconnected = true;
            self.cold.disconnected_deletions = 0;
            // Instantiate gate (lever 2, AY_AB_BVE_INST_GATE): stamp a new
            // elimination phase for the scoped incremental BVE entry.
            self.cold.bve_elim_phase_seq = self.cold.bve_elim_phase_seq.wrapping_add(1);

            let bve_unsat =
                self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::BVE, Self::bve);
            passes_run.push("bve");

            // Reconnect watches after BVE.
            let effective_baseline = if self.cold.instantiate_rebuilt_watches {
                self.arena.len()
            } else {
                arena_baseline
            };
            self.mark_trail_affected(0);
            self.watches_disconnected = false;
            self.reconnect_bve_watches(effective_baseline);

            if bve_unsat {
                return true;
            }
            if self.propagate_check_unsat() {
                return true;
            }

            self.update_bve_growth_guard(clauses_before_bve);

            // Post-BVE subsumption: BVE resolvents create new subsumption
            // opportunities. Run an additional subsumption pass to exploit
            // shorter resolvents.
            if self.inproc_ctrl.subsume.enabled {
                self.stats
                    .record_inprocessing_attempt(DiagnosticPass::Subsume);
                self.jit_invalidate_for_structural_pass();
                self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Subsume, Self::subsume);
                passes_run.push("subsume");
                self.cold.subsume_ran_since_bve = true; // #8502: signal pre-BVE guard
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }

        if self.is_interrupted() {
            return false;
        }

        // ── Transitive reduction ────────────────────────────────────────
        // Removes redundant binary clauses via BFS on the binary implication
        // graph. Safe in incremental mode — only removes learned redundant
        // binary implications, no reconstruction needed.
        let should_transred = self.should_transred();
        if should_transred {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::TransRed);
        }
        if should_transred {
            self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::TransRed, Self::transred);
            passes_run.push("transred");
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return true;
            }
        }

        if self.is_interrupted() {
            return false;
        }

        // ── Vivification ────────────────────────────────────────────────
        // Strengthens clauses by removing redundant literals via BCP.
        // No variable elimination, no reconstruction stack — safe in
        // incremental mode. This is the highest-impact technique for
        // IC3 frame solvers: vivification shortens learned clauses,
        // improving propagation strength.
        let should_vivify = self.should_vivify();
        if should_vivify {
            self.stats
                .record_inprocessing_attempt(DiagnosticPass::Vivify);
        }
        if should_vivify {
            self.jit_invalidate_for_structural_pass();
            let vivify_yield_before = self.inprocessing_yield_signal(DiagnosticPass::Vivify);
            if self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Vivify, Self::vivify) {
                return true;
            }
            let vivify_made_progress =
                self.inprocessing_yield_signal(DiagnosticPass::Vivify) > vivify_yield_before;
            passes_run.push("vivify");

            // Post-vivification subsumption: vivification shortens clauses,
            // creating new subsumption opportunities (#7393, #8134).
            let post_vivify_subsume_due = !self.use_large_sparse_subsume_idle_cooldown()
                || vivify_made_progress
                || self.should_subsume();
            if self.inproc_ctrl.subsume.enabled && post_vivify_subsume_due {
                self.stats
                    .record_inprocessing_attempt(DiagnosticPass::Subsume);
                self.jit_invalidate_for_structural_pass();
                self.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Subsume, Self::subsume);
                passes_run.push("subsume");
                self.cold.subsume_ran_since_bve = true; // #8502: signal pre-BVE guard
                if self.propagate_check_unsat() {
                    return true;
                }
            }
        }

        // ── JIT recompilation after incremental inprocessing (#8202) ────
        // Subsumption and vivification are structural passes that invalidate
        // the JIT compiled formula.  Recompile now so search resumes with
        // native BCP rather than falling back to standard 2WL for the rest
        // of this solve call.

        // ── Postconditions ──────────────────────────────────────────────
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: run_incremental_inprocessing exiting at decision level {}",
            self.decision_level,
        );
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "BUG: unpropagated literals after incremental inprocessing (qhead={} trail={})",
            self.qhead,
            self.trail.len(),
        );

        // Pending-garbage drain check.
        assert_eq!(
            self.pending_garbage_count, 0,
            "BUG: {} pending-garbage clauses at incremental inprocessing exit",
            self.pending_garbage_count,
        );

        // Proof I/O error check.
        if let Some(ref manager) = self.proof_manager {
            assert!(
                !manager.has_inprocessing_boundary_error(),
                "BUG: proof I/O error detected at incremental inprocessing boundary"
            );
        }

        // ── Telemetry ───────────────────────────────────────────────────
        let round_elapsed_ns = round_start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        let pass_time_delta_ns: u64 = self
            .stats
            .inprocessing_time_ns
            .iter()
            .zip(pass_time_baseline.iter())
            .map(|(now, before)| now.saturating_sub(*before))
            .sum();
        let overhead_ns = round_elapsed_ns.saturating_sub(pass_time_delta_ns);

        self.stats.incremental_inprocessing_rounds += 1;
        let clauses_after = self.num_clauses();
        let round_simplifications = clauses_before.saturating_sub(clauses_after) as u64;
        self.stats.inprocessing_simplifications = self
            .stats
            .inprocessing_simplifications
            .saturating_add(round_simplifications);

        tracing::debug!(
            num_clauses = clauses_after,
            passes = ?passes_run,
            overhead_ms = format_args!("{:.2}", overhead_ns as f64 / 1_000_000.0),
            simplifications = round_simplifications,
            "incremental inprocessing: round complete (#8208)"
        );

        // Update inprocessing overhead for adaptive tick scaling (#8099).
        self.cold.last_inprocessing_overhead_ms = overhead_ns as f64 / 1_000_000.0;

        // Update scheduling: advance conflict limit so we don't immediately
        // re-fire on the next solve_with_assumptions() call.
        self.cold.last_inprobe_reduction = self.cold.num_reductions;
        // #maxsat-inproc-throttle: each incremental inprocessing round scans
        // O(arena) clauses (subsumption + vivification prepass). On large
        // weighted-MaxSAT formulas — hard clauses plus accumulated totalizers
        // over hundreds of OLL core iterations — the flat 500-conflict
        // interval over-fires: profiling causal-discovery showed inprocessing
        // (arena scans) at ~50% of runtime versus ~7% for BCP, starving core
        // extraction on the lower-bound-proving endgame. Scaling the re-fire
        // interval with clause count keeps inprocessing a bounded fraction of
        // total time. Frequency-only, so it cannot change any verdict.
        let base = INPROBE_INTERVAL.max(500);
        // Env override wins (experimentation); otherwise use the per-solver
        // configured divisor (the MaxSAT engine sets Some(100); IC3/SMT/CHC
        // leave it None → legacy cadence).
        let divisor = match incremental_inprobe_env_override() {
            Some(forced) => forced,
            None => self.cold.incremental_inprobe_clause_divisor,
        };
        let delta = match divisor {
            Some(div) if div > 0 => {
                let scaled = (self.num_clauses() as u64) / div;
                base.max(scaled).min(INCREMENTAL_INPROBE_INTERVAL_CAP)
            }
            _ => base,
        };
        self.cold.next_inprobe_conflict = self.num_conflicts.saturating_add(delta);

        // Invalidate uniform formula cache after any inprocessing (#7905).
        if !passes_run.is_empty() {
            self.invalidate_uniform_formula_cache();
        }

        false
    }
}
