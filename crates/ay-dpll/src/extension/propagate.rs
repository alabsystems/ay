// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager propagation: the main BCP callback for the theory extension.
//!
//! Extracted from mod.rs for code health (#5970). Contains the body of
//! `Extension::propagate()` as a `propagate_impl()` helper, following
//! the same delegation pattern used by `check()` → `check_impl()`.

use ay_core::{FarkasAnnotation, TermId, TheoryLemmaKind, TheoryResult, TheorySolver};
use ay_sat::{ExtPropagateResult, Literal, SolverContext};

use super::types::format_term_recursive;
use super::{infer_bound_axiom_arith_kind, TheoryExtension};
use crate::theory_inference::{
    record_theory_conflict_unsat, record_theory_conflict_unsat_with_farkas,
};
#[cfg(debug_assertions)]
use crate::verification::verify_theory_conflict_with_farkas_full;
use crate::verification::{
    log_conflict_debug, log_propagation_debug, verify_euf_conflict,
    verify_lra_full_state_satisfiable, verify_propagation_semantic, verify_theory_conflict,
    verify_theory_conflict_with_farkas, verify_theory_propagation,
};

/// #8254: Maximum number of full-state soundness guard checks per solve.
const FULL_STATE_GUARD_BUDGET: u64 = 32;

/// Temporary campaign instrumentation gate (#qfax-t3-atom-space).
static PROP_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Core logic for `Extension::propagate()`.
    ///
    /// Processes pending axiom clauses, feeds new SAT trail assignments to the
    /// theory solver, runs `check_during_propagate`, handles all `TheoryResult`
    /// variants (Sat, Unknown, NeedLemmas, NeedSplit, Unsat, UnsatWithFarkas),
    /// and collects theory propagations into SAT clauses.
    pub(super) fn propagate_impl(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.eager_stats.propagate_calls += 1;

        // T3 CHC/PDR divergence guard
        // (the development design notes).
        //
        // The SAT solver drives this callback once per BCP round. A diverging
        // theory-propagation churn (the "asserting theory atom at level 0" spin)
        // makes neither conflicts nor decisions, so the CDCL loop's `should_stop`
        // poll (every 100 conflicts / 1000 decisions) never fires and the
        // executor's installed wall-clock deadline is silently shed — the solve
        // spins at 100% CPU forever. Poll the deadline HERE, the one point
        // guaranteed to run every iteration of that spin, and hand a `stop` back
        // to the SAT solver, which returns `SatResult::Unknown` (`TheoryStop`).
        // Fail-closed: a deadline hit only ever degrades the solve to Unknown
        // (a reported coverage gap), never a wrong Sat/Unsat verdict.
        //
        // `Instant::now()` is amortized to near-zero on the hot path: it is read
        // only when a deadline is actually installed (`solve_deadline.is_some()`
        // — the CHC/PDR path and CLI `:timeout`; `None` for plain no-timeout
        // solves) and only once every `DEADLINE_POLL_INTERVAL` calls, so the
        // common per-round cost is a single `Option` test plus a `u64` remainder.
        // 512 cheap level-0 re-assertions is sub-millisecond, so the deadline
        // overshoot on the divergence is negligible.
        if let Some(deadline) = self.solve_deadline {
            const DEADLINE_POLL_INTERVAL: u64 = 512;
            if self
                .eager_stats
                .propagate_calls
                .is_multiple_of(DEADLINE_POLL_INTERVAL)
                && ay_core::time::Instant::now() >= deadline
            {
                return ExtPropagateResult::none().with_stop(true);
            }
        }

        // ABSOLUTE PROPAGATE-CALL CAP — the deadline-independent divergence
        // backstop. The wall-clock deadline above only fires when
        // `solve_deadline` is populated, but proof-seeking solves reach this
        // extension WITHOUT one (the deadline plumbing does not reach the
        // theory-extension on every path), so a conflict-free/decision-free
        // level-0 theory-propagation churn (the "asserting theory atom at level
        // 0" spin) re-enters `propagate` unbounded and hangs the whole
        // verification gate. This hard cap on the round count GUARANTEES
        // termination regardless of any deadline: past the cap the extension
        // stops and the SAT core reports Unknown (a reported coverage gap —
        // fail-closed, NEVER a wrong Sat/Unsat verdict). The bound is set far
        // above any real search over the small per-obligation CHC systems the
        // verifier emits (a genuine solve decides in well under this many
        // rounds), so a legitimate proof is never truncated — only a true spin
        // is bounded. `TRUST_AY_MAX_PROPAGATE_ROUNDS` overrides it for solver
        // research.
        {
            const DEFAULT_MAX_PROPAGATE_ROUNDS: u64 = 50_000_000;
            let cap = std::env::var("TRUST_AY_MAX_PROPAGATE_ROUNDS")
                .ok()
                .and_then(|s| s.parse::<u64>().ok())
                .filter(|&c| c > 0)
                .unwrap_or(DEFAULT_MAX_PROPAGATE_ROUNDS);
            if self.eager_stats.propagate_calls > cap {
                return ExtPropagateResult::none().with_stop(true);
            }
        }

        if !self.pending_axiom_clauses.is_empty() {
            let axioms = std::mem::take(&mut self.pending_axiom_clauses);
            let axiom_terms = std::mem::take(&mut self.pending_axiom_terms);
            let axiom_farkas = std::mem::take(&mut self.pending_axiom_farkas);
            // Record bound axioms as theory lemma proof steps (#6178, #6686).
            // Without this, SAT-level BCP can derive UNSAT using these axiom
            // clauses before the theory solver produces a Farkas conflict,
            // leaving the proof tracker without a corresponding TheoryLemma step.
            //
            // #6686: Use Farkas certificates from axiom validation so the
            // exported Alethe proof has `la_generic :args (c1 c2)` instead of
            // bare `la_generic` (which carcara rejects).
            if let Some(ref mut proof_ctx) = self.proof {
                for ((t1, p1, t2, p2), farkas) in axiom_terms.into_iter().zip(axiom_farkas) {
                    let term1 = if p1 {
                        t1
                    } else {
                        let Some(&neg) = proof_ctx.negations.get(&t1) else {
                            continue;
                        };
                        neg
                    };
                    let term2 = if p2 {
                        t2
                    } else {
                        let Some(&neg) = proof_ctx.negations.get(&t2) else {
                            continue;
                        };
                        neg
                    };
                    let clause = vec![term1, term2];
                    // #6365, #6686: Record bound axioms with Farkas certificates
                    // from axiom validation. Use the extracted certificate when
                    // available; fall back to unit [1, 1] when the validation
                    // returned plain Unsat without Farkas data.
                    let upgraded = self
                        .terms
                        .and_then(|terms| infer_bound_axiom_arith_kind(terms, t1, t2, p1, p2));
                    if let Some(kind) = upgraded {
                        let farkas_cert =
                            farkas.unwrap_or_else(|| FarkasAnnotation::from_ints(&[1i64, 1]));
                        proof_ctx.tracker.add_theory_lemma_with_farkas_and_kind(
                            clause,
                            farkas_cert,
                            kind,
                        );
                    } else {
                        // Bound axioms that fail arith kind inference
                        // still export as Generic/trust. These may be EUF or
                        // combined-theory axioms that need a dedicated classifier.
                        proof_ctx
                            .tracker
                            .add_theory_lemma_with_kind(clause, TheoryLemmaKind::Generic);
                    }
                }
            }
            return ExtPropagateResult::clauses(axioms);
        }

        let trail = ctx.trail();
        let sat_level = ctx.decision_level();

        // #8008 rev2: Full trail deferral early return REMOVED. Deferring
        // all propagate work caused search thrashing on SAT-satisfiable
        // induction formulas. BCP-time theory conflicts are essential for
        // guiding the search (even tiny contradictory_variable_bounds conflicts).

        // Only capture timestamps when diagnostic tracing is active.
        // Instant::now() syscalls accounted for ~5% of DPLL hot-loop time.
        let propagate_start = self
            .diagnostic_trace
            .is_some()
            .then(ay_core::time::Instant::now);
        let mut asserted_theory_atoms = 0usize;
        let mut check_result_label = "sat";
        // Push theory scope to match SAT decision level
        // This enables incremental backtracking via pop() instead of reset()
        let mut pushed = false;
        while self.theory_level < sat_level {
            // Save trail position before push so backtrack can restore it (#5548).
            self.level_trail_positions.push(self.last_trail_pos);
            self.theory.push();
            self.theory_level += 1;
            pushed = true;
            if let Some(diag) = self.diagnostic_trace {
                diag.emit_push(self.theory_level);
            }
            if self.debug {
                safe_eprintln!("[EAGER] Push to theory level {}", self.theory_level);
            }
        }

        // Process new assignments since last call
        let new_assignments = if self.last_trail_pos < trail.len() {
            &trail[self.last_trail_pos..]
        } else {
            &[]
        };

        // Feed new theory-relevant assignments to the theory solver.
        //
        // ITE relevancy filter (#8125): atoms in inactive ITE branches are
        // deferred from BCP-time theory checks. They are flushed before the
        // final theory check in `check_impl()`. This avoids O(2^k) simplex
        // overhead on ITE-heavy formulas where BCP assigns atoms from both
        // branches but only one is active.
        //
        // #8177: When the JIT dispatch table is available, use O(1) array-indexed
        // dispatch instead of the multi-step is_theory_atom() + var_to_term.get()
        // + ITE bitset check sequence. The dispatch table combines all three
        // lookups into a single array access via dispatch_assignment().
        #[cfg(feature = "jit")]
        let use_jit_dispatch = self.jit_dispatch_table.is_some();
        #[cfg(not(feature = "jit"))]
        let use_jit_dispatch = false;

        if use_jit_dispatch {
            #[cfg(feature = "jit")]
            if let Some(ref dispatch_table) = self.jit_dispatch_table {
                for &lit in new_assignments {
                    let var_id = lit.variable().id();
                    let value = lit.is_positive();
                    let result = dispatch_table.dispatch_assignment(
                        var_id,
                        value,
                        &|cond_var_id| ctx.value(ay_sat::Variable::new(cond_var_id)),
                        sat_level,
                    );
                    self.eager_stats.jit_dispatch_atoms += 1;
                    match result {
                        ay_jit::TheoryDispatchResult::Assert { term_id, value } => {
                            let term = TermId(term_id);
                            if self.debug {
                                safe_eprintln!(
                                    "[EAGER] Asserting term {:?} = {} (var {}) at level {} [jit]",
                                    term,
                                    value,
                                    var_id,
                                    sat_level,
                                );
                            }
                            // Diagnostic trace for the level-0 assertion spin
                            // (see the divergence-guard comments above). At
                            // WARN this printed on every embedding consumer's
                            // default subscriber — e.g. spamming every compiler_consumer
                            // compile — so it stays at DEBUG.
                            if sat_level == 0 && tracing::enabled!(tracing::Level::DEBUG) {
                                if let Some(terms) = self.terms {
                                    let term_str = format_term_recursive(terms, term, 6);
                                    tracing::debug!(
                                        term = ?term,
                                        value = value,
                                        term_str = %term_str,
                                        "  asserting theory atom at level 0"
                                    );
                                }
                            }
                            self.theory.assert_literal(term, value);
                            asserted_theory_atoms += 1;
                        }
                        ay_jit::TheoryDispatchResult::DeferIte { term_id, value } => {
                            let term = TermId(term_id);
                            // #uflia-deferred-atom-loss: record the assignment
                            // level so backtrack() can retain surviving entries.
                            let level = ctx
                                .var_level(ay_sat::Variable::new(var_id))
                                .unwrap_or(sat_level);
                            self.ite_deferred_atoms.push((term, value, level, false));
                            self.eager_stats.ite_relevancy_skips += 1;
                        }
                        ay_jit::TheoryDispatchResult::Skip => {
                            // #8373/#8003: JIT dispatch returns Skip for non-theory-atom
                            // variables. Check if this is an ITE condition that
                            // needs forwarding to the theory solver.
                            let var_idx = var_id as usize;
                            let word_idx = var_idx / 64;
                            let is_ite_condition = word_idx < self.ite_condition_bitset.len()
                                && (self.ite_condition_bitset[word_idx] >> (var_idx % 64)) & 1 != 0;
                            if is_ite_condition {
                                let term = self
                                    .var_to_term
                                    .get(&var_id)
                                    .or_else(|| self.ite_condition_var_to_term.get(&var_id))
                                    .copied();
                                if let Some(term) = term {
                                    self.theory.assert_literal(term, value);
                                    asserted_theory_atoms += 1;
                                }
                            }
                        }
                    }
                }
            }
        } else {
            for &lit in new_assignments {
                let var = lit.variable();
                if self.is_theory_atom(var) {
                    if let Some(&term) = self.var_to_term.get(&var.id()) {
                        let value = lit.is_positive();

                        // ITE relevancy check (#8125, #8003): gated on AY_NO_ITE_DEFERRAL.
                        let var_id = var.id() as usize;
                        let is_ite_guarded = if crate::theory_debug_flags::no_ite_deferral() {
                            false
                        } else {
                            let word_idx = var_id / 64;
                            word_idx < self.ite_guarded_bitset.len()
                                && (self.ite_guarded_bitset[word_idx] >> (var_id % 64)) & 1 != 0
                        };
                        // ITE branch guard deferral — level-aware (#8254, #8003).
                        //
                        // When the condition IS assigned AND selects the other
                        // branch: defer at all levels (the atom is definitively
                        // in the inactive branch).
                        //
                        // When the condition is UNASSIGNED at level > 0: assert
                        // normally. CDCL backtracking handles conflicts from
                        // simultaneously-active branches. Deferring when unassigned
                        // starves the theory solver on ITE-heavy benchmarks.
                        //
                        // At level 0 with unassigned condition: assert normally.
                        // The aggressive level-0 deferral from the original #8254
                        // fix caused incompleteness; the stale-reason filter in
                        // LRA propagation provides the safety net.
                        if is_ite_guarded {
                            let (cond_var_id, is_then_branch) = self.ite_branch_guards[var_id];
                            let cond_var = ay_sat::Variable::new(cond_var_id);
                            if let Some(cond_value) = ctx.value(cond_var) {
                                if cond_value != is_then_branch {
                                    // #uflia-deferred-atom-loss: record the
                                    // assignment level for backtrack retention.
                                    let level = ctx.var_level(var).unwrap_or(sat_level);
                                    self.ite_deferred_atoms.push((term, value, level, false));
                                    self.eager_stats.ite_relevancy_skips += 1;
                                    continue;
                                }
                            }
                        }

                        if self.debug {
                            safe_eprintln!(
                                "[EAGER] Asserting term {:?} = {} (var {:?}) at level {}",
                                term,
                                value,
                                var,
                                sat_level,
                            );
                        }
                        // Diagnostic trace for the level-0 assertion spin (see
                        // the divergence-guard comments above). At WARN this
                        // printed on every embedding consumer's default
                        // subscriber — e.g. spamming every compiler_consumer compile — so
                        // it stays at DEBUG.
                        if sat_level == 0 && tracing::enabled!(tracing::Level::DEBUG) {
                            if let Some(terms) = self.terms {
                                let term_str = format_term_recursive(terms, term, 500);
                                tracing::debug!(
                                    term = ?term,
                                    value = value,
                                    term_str = %term_str,
                                    "  asserting theory atom at level 0"
                                );
                            }
                        }
                        self.theory.assert_literal(term, value);
                        asserted_theory_atoms += 1;
                    }
                } else {
                    // #8373: Forward Boolean ITE condition assignments to the
                    // theory solver. Pure Boolean variables (TermData::Var) used
                    // as ITE conditions in arithmetic constraints like
                    // `(ite x_0 (= x_3 0.0) (= x_2 x_3))` are not theory atoms
                    // (is_theory_atom returns false for Var), so they are never
                    // forwarded through the normal path. Without this, LRA's
                    // parse_linear_expr cannot resolve the ITE condition and
                    // over-approximates the ITE as a fresh variable, losing the
                    // branch-dependent arithmetic constraints.
                    //
                    // We use the ite_condition_bitset (already built in
                    // construction.rs) to identify which variables are ITE
                    // conditions. Forwarding them via assert_literal populates
                    // LRA's `asserted` map so parse_linear_expr can resolve
                    // the correct ITE branch.
                    //
                    // #8003: Look up the term from BOTH var_to_term (for
                    // theory atoms that are also ITE conditions) AND
                    // ite_condition_var_to_term (for non-theory-atom conditions
                    // like xor, and, or used in arithmetic ITEs).
                    let var_id = var.id() as usize;
                    let word_idx = var_id / 64;
                    let is_ite_condition = word_idx < self.ite_condition_bitset.len()
                        && (self.ite_condition_bitset[word_idx] >> (var_id % 64)) & 1 != 0;
                    if is_ite_condition {
                        let term = self
                            .var_to_term
                            .get(&var.id())
                            .or_else(|| self.ite_condition_var_to_term.get(&var.id()))
                            .copied();
                        if let Some(term) = term {
                            let value = lit.is_positive();
                            self.theory.assert_literal(term, value);
                            asserted_theory_atoms += 1;
                        }
                    }
                }
            }
        }
        self.last_trail_pos = trail.len();

        // Skip theory check when no SAT-observable state change occurred (#4919):
        // - No new theory atoms were asserted (assert_literal not called)
        // - No push happened (scope unchanged)
        // - At least one check has already been done (not the first call)
        // - No already-materialized propagations are queued for delivery to SAT
        // This avoids redundant simplex re-verification on BCP rounds that
        // only propagate Boolean-only literals. The theory's check result is
        // unchanged when its state is unchanged.
        //
        // #8452 (context): has_pending_analysis() gates deferred touched-row
        // work (implied bounds from prior assertions). It USED to also be part
        // of the skip condition so the theory would deliver implied bounds at
        // BCP time rather than force a decision. It is deliberately NOT required
        // below anymore — see the 2c rationale.
        //
        // 2c (coupled-integer quiescence): a pending-*analysis*-only round —
        // asserted_theory_atoms == 0, no push, no already-queued propagations,
        // but has_pending_analysis() still true — is internal theory cascade
        // work that has produced ZERO SAT-observable output this round (no new
        // trail atom fed in, no materialized propagation queued out, no
        // conflict). On coupled-integer LIA tableaux this touched-row analysis
        // can advertise "more work" indefinitely without ever changing the SAT
        // trail, starving the CDCL loop of a DECISION and stalling the solve at
        // Unknown. Returning none() here hands control back to CDCL to DECIDE,
        // which is what actually breaks the churn and drives the search to a
        // model or a real conflict.
        //
        // SOUNDNESS (this is a verifier — a false proof is catastrophic).
        // Returning none() only LETS SAT DECIDE; it never itself concludes Sat
        // or Unsat, so it cannot directly emit a wrong verdict. It also cannot
        // let a REAL conflict be dropped:
        //   * A decision does NOT discard theory state. The pending touched rows
        //     stay queued in the theory solver; the next propagate() round (once
        //     the decision assigns a theory atom) re-consults the theory, and any
        //     conflict is caught then.
        //   * Before SAT is ever declared, `Extension::check()` runs the FULL,
        //     uncapped `theory.check()` (check.rs::check_impl, gated by
        //     needs_final_check_after_sat), which drains all pending analysis to
        //     fixpoint. A genuine inconsistency surfaces there as
        //     Unsat/UnsatWithFarkas → ExtCheckResult::Conflict, so a satisfiable
        //     model is never accepted while a real conflict is still latent. This
        //     is the SAME deferred-work-plus-final-check backstop that the
        //     ITE-relevancy deferral (#8125/#8373) already relies on.
        //   * A false UNSAT is impossible too: a conflict is only emitted from a
        //     theory-produced conflict clause; skipping analysis can only FAIL to
        //     produce a conflict, never fabricate one.
        // So only completeness/search-guidance is at stake, and the entire point
        // of 2c is that DECIDING improves it. has_pending_propagations() is still
        // honored below: already-materialized propagations ARE SAT-observable
        // trail-changing work (#8422/#8452) and must be delivered, not stranded.
        if asserted_theory_atoms == 0
            && !pushed
            && self.has_checked
            && !self.theory.has_pending_propagations()
        {
            self.eager_stats.state_unchanged_skips += 1;
            self.emit_eager_event(sat_level, 0, "skip", 0, propagate_start);
            return ExtPropagateResult::none();
        }

        // #8255: Track atoms asserted since the last check_during_propagate()
        // call. Used for diagnostics and for the LRA theory's bcp_fast_skip
        // optimization (when atoms_since_last_check == 0, the theory can skip
        // the entire post-simplex propagation pass). Reset on check, backtrack,
        // and init.
        self.atoms_since_last_check += asserted_theory_atoms as u32;
        self.deferred_atom_count += asserted_theory_atoms as u32;

        // #8452 TL96: Minimal BCP theory check batching.
        //
        // Z3 NEVER batches theory checks (UINT_MAX threshold). AY uses
        // adaptive batching to amortize SAT-theory boundary crossing
        // overhead, but previous thresholds (64/128/256 streak with
        // 4/16/64 batch sizes) caused 15-39% deferral rates on QF_LRA
        // BMC/induction benchmarks, starving the solver of theory guidance.
        //
        // Revised approach: much higher streak thresholds (512/1024/2048)
        // with minimal batch sizes (2/4/8). This ensures:
        // - Small/medium benchmarks (sc-*, simple_startup_*, uart-*) almost
        //   never enter batching (512 consecutive unproductive checks is
        //   extremely rare on these formulas).
        // - Large benchmarks with truly unproductive theory checks still
        //   get batching to reduce overhead, but with tiny batch sizes
        //   that limit how long any check is deferred.
        //
        // The LRA fast-skip (O(1) when !dirty, #8255) already handles the
        // common case of redundant checks cheaply. Batching adds value only
        // when even the boundary-crossing overhead dominates on very large
        // unproductive formulas.
        const PHASE1_STREAK: u32 = 512;
        const PHASE1_BATCH: u32 = 2;
        const PHASE2_STREAK: u32 = 1024;
        const PHASE2_BATCH: u32 = 4;
        const PHASE3_STREAK: u32 = 2048;
        const PHASE3_BATCH: u32 = 8;
        let batch_target = if self.zero_propagation_streak >= PHASE3_STREAK {
            PHASE3_BATCH
        } else if self.zero_propagation_streak >= PHASE2_STREAK {
            PHASE2_BATCH
        } else if self.zero_propagation_streak >= PHASE1_STREAK {
            PHASE1_BATCH
        } else {
            0u32
        };
        // #8422: Bypass batching when the theory has pending eager propagations
        // from assert_literal() → propagate_var_atoms(). Pending propagations
        // must be returned to the SAT solver immediately.
        let theory_has_pending = self.theory.has_pending_propagations();
        // #8452: Also bypass batching when the theory has pending row analysis
        // (touched rows from implied bounds or simplex pivots). Z3's
        // unit_propagate() always runs propagate_bounds_for_touched_rows()
        // after simplex — deferring this analysis delays bound derivation
        // that could produce propagations in the current round. Without this
        // check, the theory has work to do but batching prevents it from
        // running, causing the SAT solver to make unnecessary decisions.
        let theory_has_analysis = self.theory.has_pending_analysis();
        // SOUNDNESS (#8347): Batching requires zero_propagation_streak > 0.
        // When propagations are active (streak == 0), batching delays the
        // simplex that maintains the theory's incremental state, causing
        // learned clauses from stale state.
        let batching_ready = self.has_checked
            && batch_target > 0
            && self.zero_propagation_streak > 0
            && self.pending_split.is_none()
            && self.deferred_atom_count < batch_target
            && !theory_has_pending
            && !theory_has_analysis;
        if batching_ready && sat_level == 0 {
            self.eager_stats.level0_batch_guard_hits += 1;
        }
        if batching_ready && sat_level > 0 {
            // Drain pending propagations before deferring.
            let early_propagations = self.theory.drain_pending_propagations();
            if !early_propagations.is_empty() {
                return self.process_early_propagations(
                    early_propagations,
                    sat_level,
                    asserted_theory_atoms,
                    propagate_start,
                    ctx,
                );
            }
            self.eager_stats.batch_defers += 1;
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                "batch_defer",
                0,
                propagate_start,
            );
            return ExtPropagateResult::none();
        }
        // Reset deferred count — we're about to check.
        self.deferred_atom_count = 0;
        self.pending_theory_atoms_for_batch.set(0);
        // #8255: Reset atoms-since-check counter when we actually run the check.
        self.atoms_since_last_check = 0;
        self.has_checked = true;
        if sat_level == 0 {
            self.eager_stats.level0_checks += 1;
        }

        // #9224: deferred_theory_mode removed. The heuristic (#8347) silenced
        // BCP-time theory checks when >60% of checks produced conflicts and
        // <10% produced propagations. This was designed for vpm2-30 but caused
        // induction benchmarks (sc-6, sc-8, simple_startup_5nodes) to lose all
        // theory guidance, returning Unknown instead of solving. The atoms-since-
        // last-check batching (#8255) already provides adaptive BCP throttling
        // without completely silencing the theory solver.

        // First check for theory conflicts (e.g., disequality violated by transitivity)
        // This is critical for eq_diamond where (= x0 x14) = false but transitivity
        // proves x0 = x14.
        // Use BCP-time hook: combined solvers override this to skip expensive
        // Nelson-Oppen fixpoints while standalone theories delegate to check().
        let check_res =
            if self.disable_theory_check || crate::theory_debug_flags::no_bcp_theory_check() {
                TheoryResult::Sat
            } else {
                self.total_bcp_checks += 1;
                self.theory.check_during_propagate()
            };
        let mut stop_for_inline_refinement_handoff = false;
        // #6546 Packet 5: buffer for inline lemma clauses added during
        // the check_during_propagate match. Merged into the propagation
        // `clauses` vec later before returning ExtPropagateResult.
        let mut inline_lemma_clauses: Vec<Vec<Literal>> = Vec::new();
        match check_res {
            TheoryResult::Sat => {
                // Clear stale pending single-var disequality splits from a prior
                // propagate() call (#6020). A NeedDisequalitySplit or NeedSplit
                // on a partial assignment may become unnecessary after further BCP.
                // But do NOT clear NeedExpressionSplit: multi-var disequalities
                // (E != F) need split atoms to be properly enforced. Clearing
                // them causes oscillation where the split is repeatedly discovered
                // and lost without ever reaching the pipeline (#4919).
                //
                // #6662: also clear NeedExpressionSplit if the split has
                // already been encoded in the persistent SAT solver.
                let is_stale_expr_split = matches!(
                    &self.pending_split,
                    Some(TheoryResult::NeedExpressionSplit(s))
                    if self.processed_expr_splits.is_some_and(|ps| ps.contains(&s.disequality_term))
                );
                if is_stale_expr_split
                    || !matches!(
                        &self.pending_split,
                        Some(TheoryResult::NeedExpressionSplit(_))
                    )
                {
                    self.pending_split = None;
                }
                let refinements = self.theory.take_bound_refinements();
                stop_for_inline_refinement_handoff =
                    self.should_stop_for_inline_bound_refinement_handoff(&refinements);
                self.record_pending_bound_refinements(refinements);
            }
            TheoryResult::Unknown => {
                // Theory cannot determine status yet — continue search.
                self.pending_bound_refinements.clear();
                check_result_label = "unknown";
            }
            // #6546 Packet 5: inline NeedLemmas handling during BCP.
            // Instead of storing NeedLemmas as pending_split (which requires a
            // full SAT re-solve), convert lemma clauses to SAT literals and add
            // them as inline clauses. This eliminates O(N) SAT-solve round-trips
            // for array ROW2 lemmas. Storeinv size 5: 1252 iterations → ~1.
            TheoryResult::NeedLemmas(lemmas) => {
                let mut sat_clauses = Vec::with_capacity(lemmas.len());
                let mut all_mapped = true;
                for lemma in &lemmas {
                    let sat_lits: Vec<Literal> = lemma
                        .clause
                        .iter()
                        .filter_map(|t| self.term_to_literal(t.term, t.value))
                        .collect();
                    if sat_lits.len() == lemma.clause.len() {
                        sat_clauses.push(sat_lits);
                    } else {
                        all_mapped = false;
                        break;
                    }
                }
                if all_mapped && !sat_clauses.is_empty() {
                    // All lemma terms have SAT variables — inject inline.
                    self.eager_stats.inline_lemma_clauses += sat_clauses.len() as u64;
                    check_result_label = "inline_lemmas";
                    inline_lemma_clauses.extend(sat_clauses);
                    // Record proof entries for inline lemmas (#6725).
                    // #8106: Infer specific kind instead of Generic/trust.
                    if let Some(ref mut proof_ctx) = self.proof {
                        for lemma in &lemmas {
                            let terms: Vec<TermId> = lemma
                                .clause
                                .iter()
                                .map(|lit| {
                                    if lit.value {
                                        lit.term
                                    } else {
                                        proof_ctx
                                            .negations
                                            .get(&lit.term)
                                            .copied()
                                            .unwrap_or(lit.term)
                                    }
                                })
                                .collect();
                            if let Some(term_store) = self.terms {
                                let kind = crate::theory_inference::infer_theory_lemma_kind_from_clause_terms(
                                    term_store,
                                    &terms,
                                );
                                match kind {
                                    TheoryLemmaKind::Generic => {
                                        proof_ctx.tracker.add_theory_lemma(terms);
                                    }
                                    _ => {
                                        proof_ctx.tracker.add_theory_lemma_with_kind(terms, kind);
                                    }
                                }
                            } else {
                                proof_ctx.tracker.add_theory_lemma(terms);
                            }
                        }
                    }
                } else {
                    // Fallback: some terms missing from SAT — use pending_split.
                    self.pending_split = Some(TheoryResult::NeedLemmas(lemmas));
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                }
            }
            TheoryResult::NeedExpressionSplit(split) => {
                if self
                    .processed_expr_splits
                    .is_some_and(|s| s.contains(&split.disequality_term))
                {
                    check_result_label = "sat(stale-split)";
                } else {
                    self.expr_split_seen_count += 1;
                    self.pending_split = Some(TheoryResult::NeedExpressionSplit(split));
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                }
            }
            TheoryResult::NeedExpressionSplits(splits) => {
                // #8707: Batch variant — filter out already-processed splits and
                // keep only fresh ones. If all are stale, treat as SAT; if one
                // remains, demote to singleton; otherwise pass the batch through.
                let fresh: Vec<_> = if let Some(processed) = self.processed_expr_splits {
                    splits
                        .into_iter()
                        .filter(|s| !processed.contains(&s.disequality_term))
                        .collect()
                } else {
                    splits
                };
                if fresh.is_empty() {
                    check_result_label = "sat(stale-split)";
                } else {
                    self.expr_split_seen_count += 1;
                    if fresh.len() == 1 {
                        let mut iter = fresh.into_iter();
                        let one = iter.next().unwrap();
                        self.pending_split = Some(TheoryResult::NeedExpressionSplit(one));
                    } else {
                        self.pending_split = Some(TheoryResult::NeedExpressionSplits(fresh));
                    }
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                }
            }
            TheoryResult::NeedModelEquality(eq) => {
                if self.model_equality_already_encoded(&eq) {
                    check_result_label = "sat(stale-model-eq)";
                } else {
                    self.pending_split = Some(TheoryResult::NeedModelEquality(eq));
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                }
            }
            TheoryResult::NeedModelEqualities(eqs) => {
                if let Some(check_result) = self.filter_stale_model_equalities(eqs) {
                    self.pending_split = Some(check_result);
                    self.pending_bound_refinements.clear();
                    check_result_label = "split";
                } else {
                    check_result_label = "sat(stale-model-eqs)";
                }
            }
            check_result @ TheoryResult::NeedSplit(_)
            | check_result @ TheoryResult::NeedDisequalitySplit(_)
            | check_result @ TheoryResult::NeedStringLemma(_) => {
                self.pending_split = Some(check_result);
                self.pending_bound_refinements.clear();
                check_result_label = "split";
            }
            TheoryResult::Unsat(mut conflict_terms) => {
                // #4666: exact-duplicate literals are a logical identity in a
                // conflict (X ∨ X ≡ X in the learned clause) but structurally
                // fail verification below, escalating to Unknown WITHOUT
                // learning — the theory then re-derives the identical conflict.
                // Dedupe before verifying.
                crate::verification::dedup_conflict_literals(&mut conflict_terms);
                // #6242/#9061: A theory conflict at decision level 0 makes the
                // whole query UNSAT, so it is verified below by the structural,
                // semantic, and full-state soundness guards (which emit ERROR and
                // escalate to Unknown on any rejection). This is a routine event
                // on UNSAT queries — log it at DEBUG, not WARN, so it no longer
                // masquerades as a "potential false-UNSAT" in normal output.
                if sat_level == 0 {
                    tracing::debug!(
                        conflict_len = conflict_terms.len(),
                        asserted_theory_atoms,
                        sat_level,
                        "level-0 theory conflict (verifying before trusting)"
                    );
                    for (i, lit) in conflict_terms.iter().enumerate() {
                        tracing::debug!(
                            idx = i,
                            term = ?lit.term,
                            value = lit.value,
                            "  conflict atom"
                        );
                    }
                }
                // Verify the conflict is structurally valid (#3175)
                log_conflict_debug(&conflict_terms, "Unsat");
                let mut conflict_verified = true;
                if let Err(e) = verify_theory_conflict(&conflict_terms) {
                    conflict_verified = false;
                    tracing::warn!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        "BUG(#4666): theory conflict verification failed in propagate(); escalating to Unknown"
                    );
                }
                // Domain-aware semantic re-check (#4704, #6242, #7935, #8123):
                // verify_conflict_semantic dispatches to the correct verifier
                // for each domain — EUF congruence closure, LRA/LIA fresh
                // solver, or Nelson-Oppen combined solver for mixed domains.
                // Closes the gap where mixed-domain conflicts bypassed
                // verification entirely.
                //
                // The EUF check runs first for pure-EUF theories because
                // integer-variable equalities classified as Arithmetic may
                // require congruence closure to detect satisfiability (the
                // LIA verifier returns NeedSplit for disequalities).
                let mut euf_prechecked = false;
                if self.theory.supports_euf_semantic_check() {
                    if let Some(terms) = self.terms {
                        euf_prechecked = true;
                        if let Err(e) =
                            verify_euf_conflict(&conflict_terms, terms, &self.support_axioms)
                        {
                            conflict_verified = false;
                            tracing::warn!(
                                error = %e,
                                conflict_len = conflict_terms.len(),
                                "BUG(#4704): EUF semantic verification failed in propagate(); escalating to Unknown"
                            );
                        }
                    }
                }
                if let Some(terms) = self.terms {
                    // PEQ perf: when the direct EUF re-solve above already ran,
                    // skip the byte-identical Euf-domain duplicate inside the
                    // dispatcher (it was ~30% of QF_UF PEQ solve time). Every
                    // other domain verifies exactly as before; gate strength
                    // is unchanged.
                    // #uflia-verify-memo: routed through the Executor memo —
                    // a literal set already proven jointly UNSAT this query
                    // skips the fresh re-solve; failures always re-verify.
                    let semantic_result =
                        self.verify_conflict_semantic_memo(&conflict_terms, terms, euf_prechecked);
                    if let Err(e) = semantic_result {
                        conflict_verified = false;
                        tracing::warn!(
                            error = %e,
                            conflict_len = conflict_terms.len(),
                            "BUG(#8123): semantic conflict verification failed in propagate() Unsat; escalating to Unknown"
                        );
                    }
                }
                if !conflict_verified {
                    self.pending_split = Some(TheoryResult::Unknown);
                    self.emit_eager_event(
                        sat_level,
                        asserted_theory_atoms,
                        "unknown",
                        0,
                        propagate_start,
                    );
                    return ExtPropagateResult::none();
                }
                // #7935: Full-state soundness guard for level-0 conflicts.
                // Individual conflict atoms may be genuinely contradictory, but
                // the FULL set of level-0 theory assignments should be consistent
                // for a satisfiable formula. If a fresh solver says SAT for all
                // currently-asserted theory atoms, the BCP chain derived an
                // incorrect forced assignment — reject the conflict.
                //
                // PERF: This creates a fresh LRA solver instance per level-0
                // conflict, which is O(atoms) per call. In release builds this
                // causes severe CHC regression (46/55 -> 35/55) because CHC
                // solves hundreds of SMT queries internally. Debug-only.
                if sat_level == 0
                    && self.theory.supports_farkas_semantic_check()
                    && self.full_state_guard_checks < FULL_STATE_GUARD_BUDGET
                {
                    if let Some(terms) = self.terms {
                        self.full_state_guard_checks += 1;
                        let all_theory_lits: Vec<ay_core::TheoryLit> = trail
                            .iter()
                            .filter_map(|&lit| {
                                let var = lit.variable();
                                let term = self.var_to_term.get(&var.id())?;
                                if !self.theory_atom_set.contains(term) {
                                    return None;
                                }
                                Some(ay_core::TheoryLit::new(*term, lit.is_positive()))
                            })
                            .collect();
                        if let Err(e) = verify_lra_full_state_satisfiable(&all_theory_lits, terms) {
                            self.full_state_guard_rejections += 1;
                            tracing::error!(
                                error = %e,
                                conflict_len = conflict_terms.len(),
                                total_theory_atoms = all_theory_lits.len(),
                                rejections = self.full_state_guard_rejections,
                                "BUG(#8254): level-0 conflict rejected by full-state soundness guard"
                            );
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            return ExtPropagateResult::none();
                        }
                    }
                }

                if let Some(proof) = self.proof.as_mut() {
                    let _ = record_theory_conflict_unsat(
                        proof.tracker,
                        self.terms,
                        proof.negations,
                        &conflict_terms,
                    );
                }

                // #8424: EUF chain minimization at the theory level.
                let mut conflict_terms = conflict_terms;
                if let Some(terms) = self.terms {
                    let euf_removed =
                        crate::theory_inference::minimize_euf_conflict(&mut conflict_terms, terms);
                    self.eager_stats.theory_minimize_lits_removed += euf_removed as u64;
                }

                let mut clause: Vec<Literal> = conflict_terms
                    .iter()
                    .filter_map(|t| self.term_to_literal(t.term, !t.value))
                    .collect();
                // Soundness guard (#3826): every theory explanation term MUST
                // map to a SAT literal. If any term was dropped by filter_map,
                // the resulting clause is stronger than what the theory proved.
                // Partial clauses block valid SAT assignments, causing false UNSAT.
                if clause.len() < conflict_terms.len() {
                    self.partial_clause_count += 1;
                    crate::combined_solvers::theory_stats::inc_partial_clauses();
                    if self.partial_clause_count >= 100 {
                        tracing::error!(
                            count = self.partial_clause_count,
                            "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                        );
                    }
                    tracing::error!(
                        mapped = clause.len(),
                        total = conflict_terms.len(),
                        "BUG(#4666): theory conflict mapped to partial clause; skipping"
                    );
                    self.emit_eager_event(
                        sat_level,
                        asserted_theory_atoms,
                        "unknown",
                        0,
                        propagate_start,
                    );
                    return ExtPropagateResult::none();
                }
                // #8424: Pre-minimize conflict clause with level-0 removal.
                let removed =
                    crate::theory_inference::minimize_conflict_with_levels(&mut clause, |var| {
                        ctx.var_level(var)
                    });
                self.eager_stats.theory_minimize_lits_removed += removed as u64;
                if self.debug {
                    safe_eprintln!("[EAGER] Theory check conflict: {} literals", clause.len());
                }
                self.theory_conflict_count += 1;
                self.total_bcp_conflicts += 1;
                // #8064: Count tiny BCP conflicts for ratio-based deferred
                // mode activation. Small conflicts (<=3 literals) from
                // contradictory_variable_bounds are correct but often useless
                // for guiding search on SAT-satisfiable ITE-heavy formulas.
                if clause.len() <= 3 {
                    self.consecutive_tiny_conflicts += 1;
                }
                // Conflicts reset the batching streak: a conflict IS meaningful
                // theory interaction. Incrementing the streak on conflicts caused
                // false-UNSAT on sat benchmarks (sc-6, sc-8, vpm2-30): the streak
                // grew, triggering batching that deferred theory checks, allowing
                // the SAT solver to accept theory-inconsistent assignments.
                self.zero_propagation_streak = 0;
                self.emit_eager_event(
                    sat_level,
                    asserted_theory_atoms,
                    "conflict",
                    0,
                    propagate_start,
                );
                // #8421: Collect variables from conflict clause for VSIDS bumping.
                let bump_vars: Vec<ay_sat::Variable> =
                    clause.iter().map(|lit| lit.variable()).collect();
                return ExtPropagateResult::conflict(clause).with_bump_vars(bump_vars);
            }
            TheoryResult::UnsatWithFarkas(mut conflict) => {
                // #4666: dedupe exact-duplicate literals, merging positional
                // Farkas coefficients by sum (λ₁·c + λ₂·c = (λ₁+λ₂)·c) —
                // logical identity, keeps the certificate aligned.
                crate::verification::dedup_conflict_with_farkas(&mut conflict);
                // #6242/#9061: A Farkas conflict at decision level 0 makes the
                // whole query UNSAT, so it is verified below by the structural
                // Farkas check, the semantic re-check, and the full-state
                // soundness guard (which emit ERROR and escalate to Unknown on
                // any rejection). This is a routine event on UNSAT queries — log
                // it at DEBUG, not WARN, so it no longer masquerades as a
                // "potential false-UNSAT" in normal output.
                if sat_level == 0 {
                    tracing::debug!(
                        conflict_len = conflict.literals.len(),
                        asserted_theory_atoms,
                        sat_level,
                        "level-0 Farkas conflict (verifying before trusting)"
                    );
                    if tracing::enabled!(tracing::Level::DEBUG) {
                        if let Some(terms) = self.terms {
                            for (i, lit) in conflict.literals.iter().enumerate() {
                                let term_str = format_term_recursive(terms, lit.term, 6);
                                tracing::debug!(
                                    idx = i,
                                    term = ?lit.term,
                                    value = lit.value,
                                    term_str = %term_str,
                                    "  conflict atom"
                                );
                            }
                            if let Some(ref farkas) = conflict.farkas {
                                for (i, coeff) in farkas.coefficients.iter().enumerate() {
                                    tracing::debug!(
                                        idx = i,
                                        coeff = %coeff,
                                        "  Farkas coefficient"
                                    );
                                }
                            }
                        }
                    }
                }
                // Structural Farkas verification (#3175)
                log_conflict_debug(&conflict.literals, "UnsatWithFarkas");
                let mut farkas_valid = true;
                if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
                    if e.is_missing_annotation() {
                        // Missing Farkas annotation (#6535): conflict is sound but
                        // proof certificate cannot be recorded.
                        tracing::debug!(
                            conflict_len = conflict.literals.len(),
                            "Farkas annotation missing in propagate(); conflict clause is sound, skipping proof cert"
                        );
                    } else {
                        // #8595: Farkas structural failure — use conflict without certificate.
                        tracing::warn!(
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            "BUG(#4666): Farkas conflict verification failed in propagate(); using conflict clause without certificate (#8595)"
                        );
                    }
                    farkas_valid = false;
                }
                // Semantic Farkas verification (#4515): catches theory solver
                // bugs that produce structurally-valid but logically-wrong
                // certificates. Debug-only: BigRational arithmetic per conflict
                // is too expensive for release builds (W16-5: was 42% of QF_LRA
                // solver time due to exponential equality-alternative search).
                #[cfg(debug_assertions)]
                if farkas_valid && self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        if let Err(e) = verify_theory_conflict_with_farkas_full(&conflict, terms) {
                            tracing::warn!(
                                error = %e,
                                conflict_len = conflict.literals.len(),
                                "BUG(#4666): Farkas semantic verification failed in propagate(); using conflict clause without certificate (#8595)"
                            );
                            farkas_valid = false;
                        }
                    }
                }

                // Record Farkas proof data only if the certificate is valid
                if farkas_valid {
                    if let Some(proof) = self.proof.as_mut() {
                        let _ = record_theory_conflict_unsat_with_farkas(
                            proof.tracker,
                            self.terms,
                            proof.negations,
                            &conflict,
                        );
                    }
                }

                // Domain-aware semantic re-check (#6242, #7935, #8123):
                // verify_conflict_semantic dispatches to the correct verifier
                // for each domain. Promoted to all builds and unconditional —
                // no longer gated on supports_farkas_semantic_check() since the
                // function handles all domains including EUF and mixed (#8123).
                if let Some(terms) = self.terms {
                    // #uflia-verify-memo: memoized (trust-true-only) —
                    // failures always re-verify in full.
                    if let Err(e) =
                        self.verify_conflict_semantic_memo(&conflict.literals, terms, false)
                    {
                        tracing::error!(
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            "BUG(#8123): semantic conflict verification failed in propagate() Farkas path; escalating to Unknown"
                        );
                        self.pending_split = Some(TheoryResult::Unknown);
                        self.emit_eager_event(
                            sat_level,
                            asserted_theory_atoms,
                            "unknown",
                            0,
                            propagate_start,
                        );
                        return ExtPropagateResult::none();
                    }
                }
                // #7935: Full-state soundness guard for level-0 Farkas conflicts.
                // Same logic as the Unsat path above — see detailed comment there.
                // Debug-only: creating a fresh LRA solver per conflict is too
                // expensive for release builds (see PERF note above).
                if sat_level == 0
                    && self.theory.supports_farkas_semantic_check()
                    && self.full_state_guard_checks < FULL_STATE_GUARD_BUDGET
                {
                    if let Some(terms) = self.terms {
                        self.full_state_guard_checks += 1;
                        let all_theory_lits: Vec<ay_core::TheoryLit> = trail
                            .iter()
                            .filter_map(|&lit| {
                                let var = lit.variable();
                                let term = self.var_to_term.get(&var.id())?;
                                if !self.theory_atom_set.contains(term) {
                                    return None;
                                }
                                Some(ay_core::TheoryLit::new(*term, lit.is_positive()))
                            })
                            .collect();
                        if let Err(e) = verify_lra_full_state_satisfiable(&all_theory_lits, terms) {
                            self.full_state_guard_rejections += 1;
                            tracing::error!(
                                error = %e,
                                conflict_len = conflict.literals.len(),
                                total_theory_atoms = all_theory_lits.len(),
                                rejections = self.full_state_guard_rejections,
                                "BUG(#8254): level-0 Farkas conflict rejected by full-state soundness guard"
                            );
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            return ExtPropagateResult::none();
                        }
                    }
                }

                // UnsatWithFarkas contains Farkas coefficients for interpolation
                // For DPLL purposes, we just need the conflict clause.
                // Even when the Farkas certificate is invalid, the conflict
                // literals are still correct (#5534).
                let mut clause: Vec<Literal> = conflict
                    .literals
                    .iter()
                    .filter_map(|t| self.term_to_literal(t.term, !t.value))
                    .collect();
                // Soundness guard (#3826): partial clause check (same as Unsat path).
                if clause.len() < conflict.literals.len() {
                    self.partial_clause_count += 1;
                    crate::combined_solvers::theory_stats::inc_partial_clauses();
                    if self.partial_clause_count >= 100 {
                        tracing::error!(
                            count = self.partial_clause_count,
                            "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                        );
                    }
                    tracing::error!(
                        mapped = clause.len(),
                        total = conflict.literals.len(),
                        "BUG(#4666): Farkas conflict mapped to partial clause; skipping"
                    );
                    self.emit_eager_event(
                        sat_level,
                        asserted_theory_atoms,
                        "unknown",
                        0,
                        propagate_start,
                    );
                    return ExtPropagateResult::none();
                }
                // #8424: Pre-minimize Farkas conflict clause, then level-0 removal.
                {
                    let mut removed = if let Some(ref farkas) = conflict.farkas {
                        let mut coeffs = farkas.coefficients.clone();
                        crate::theory_inference::minimize_farkas_conflict(&mut clause, &mut coeffs)
                    } else {
                        0
                    };
                    // Level-0 removal applies to both Farkas and non-Farkas paths.
                    removed += crate::theory_inference::minimize_conflict_with_levels(
                        &mut clause,
                        |var| ctx.var_level(var),
                    );
                    self.eager_stats.theory_minimize_lits_removed += removed as u64;
                }
                if self.debug {
                    safe_eprintln!(
                        "[EAGER] Theory check conflict with Farkas: {} literals",
                        clause.len()
                    );
                }
                self.theory_conflict_count += 1;
                self.total_bcp_conflicts += 1;
                // #8064: Count tiny BCP conflicts (same as Unsat path).
                if clause.len() <= 3 {
                    self.consecutive_tiny_conflicts += 1;
                }
                // Reset streak on Farkas conflict (same as Unsat path).
                self.zero_propagation_streak = 0;
                self.emit_eager_event(
                    sat_level,
                    asserted_theory_atoms,
                    "conflict",
                    0,
                    propagate_start,
                );
                // #8421: Collect variables from Farkas conflict for VSIDS bumping.
                let bump_vars: Vec<ay_sat::Variable> =
                    clause.iter().map(|lit| lit.variable()).collect();
                return ExtPropagateResult::conflict(clause).with_bump_vars(bump_vars);
            }
            // All current TheoryResult variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TheoryResult variant in propagate(): {other:?}"),
        }

        // Then check for theory propagations.
        let propagations = self.theory.propagate();

        if propagations.is_empty() {
            // #4919: track consecutive zero-propagation check() calls.
            self.zero_propagation_streak += 1;
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                check_result_label,
                inline_lemma_clauses.len(),
                propagate_start,
            );
            // After seeing the same expression split many times, stop
            // the SAT solver to hand control back to the split loop (#4919).
            // Previously threshold was 3 which caused premature Unknown on
            // benchmarks like sc-6.induction3 and uart-* where the expression
            // splits need more iterations to resolve (#4919).
            // Raised to 50 to allow the SAT solver more time to find a model
            // with the split atoms properly activated.
            let stop_for_expression_split = self.expr_split_seen_count >= 50
                && matches!(
                    &self.pending_split,
                    Some(TheoryResult::NeedExpressionSplit(_))
                );
            if stop_for_expression_split {
                tracing::debug!(count = self.expr_split_seen_count, "expression split stop");
            }
            if stop_for_inline_refinement_handoff {
                self.eager_stats.bound_refinement_handoffs += 1;
            }
            let stop = stop_for_expression_split || stop_for_inline_refinement_handoff;
            // #6546: return inline lemma clauses even when no propagations.
            if !inline_lemma_clauses.is_empty() || stop {
                return ExtPropagateResult::clauses(inline_lemma_clauses).with_stop(stop);
            }
            return ExtPropagateResult::none();
        }

        // #4919: propagations produced — reset bound starvation streak.
        self.zero_propagation_streak = 0;
        // #8013: Track total BCP propagations for deferral gating.
        self.total_bcp_propagations += propagations.len() as u64;
        // #8255: Track productive calls (calls that produced propagations).
        self.total_bcp_productive_prop_calls += 1;

        // #6546: start with inline lemma clauses from check_during_propagate.
        let mut clauses = inline_lemma_clauses;
        let mut propagation_pairs: Vec<(Vec<Literal>, Literal)> = Vec::new();

        // Lazy propagations that bypass reason materialization (#8467).
        let mut lazy_propagation_pairs: Vec<(Literal, u64)> = Vec::new();

        for mut prop in propagations {
            // #8467: True lazy justification — defer reason materialization to
            // conflict analysis time. ~90% of propagated variables are never
            // resolved during conflict analysis, so their reasons never need
            // to be materialized. Instead of calling explain_propagation() now,
            // pass the reason_data handle through to the SAT solver.
            if prop.is_lazy() {
                if let Some(reason_data) = prop.reason_data {
                    // Convert propagated literal to SAT (cheap lookup).
                    if let Some(lit) = self.term_to_literal(prop.literal.term, prop.literal.value) {
                        let var = lit.variable();
                        // Check current assignment
                        if let Some(value) = ctx.value(var) {
                            if value != prop.literal.value {
                                // Opposite assignment — must materialize for conflict.
                                if let Some(reason) = self
                                    .theory
                                    .explain_propagation(prop.literal.term, reason_data)
                                {
                                    prop.reason = reason;
                                    prop.reason_data = None;
                                    // Fall through to eager path below.
                                } else {
                                    self.theory
                                        .mark_propagation_rejected(prop.literal.term, reason_data);
                                    continue;
                                }
                            } else {
                                // Already assigned correctly — skip.
                                //
                                // #euf-prop-gap (lazy twin): same ITE-deferral
                                // blind-spot churn as the eager site — feed the
                                // SAT value back, scoped to guarded vars, same
                                // kill switch (AY_NO_PROP_FEEDBACK=1).
                                self.eager_stats.props_already_assigned += 1;
                                if Self::prop_feedback_enabled()
                                    && self.is_ite_guarded_term(prop.literal.term)
                                {
                                    self.theory
                                        .assert_literal(prop.literal.term, prop.literal.value);
                                    self.eager_stats.props_fed_back += 1;
                                }
                                continue;
                            }
                        } else if reason_data & ay_euf::EUF_LAZY_MAGIC_MASK
                            == ay_euf::EUF_LAZY_MAGIC
                            && self.is_ite_guarded_term(prop.literal.term)
                        {
                            // Unassigned but an EUF token on an ITE-GUARDED
                            // atom (#euf-lazy-explain carve-out): materialize
                            // NOW and fall through to the eager path so the
                            // propagation gets its PERMANENT clause. The
                            // #8125 relevancy filter defers guarded atoms
                            // from the trail feed, so the theory never learns
                            // their assignments and its scans re-propose the
                            // same propagation after every backtrack; with an
                            // eager clause, BCP re-fires the implication
                            // itself and the skip-site feedback catches the
                            // theory up — with a lazy (clause-less) enqueue,
                            // the entailment is re-derived through a full
                            // theory round-trip on every re-descent, which
                            // measured as a hard regression on the
                            // ITE-feedback flagships (rushhour.2: sat
                            // 16s/318 conflicts eager vs unknown@60s lazy,
                            // 56k re-deliveries). Unguarded atoms reach the
                            // theory via the normal trail feed, so their
                            // re-proposal is bounded and the lazy path stays
                            // a pure win. Scoped to EUF tokens: LRA's lazy
                            // propagations keep their #8467 behavior on
                            // ITE-heavy QF_LRA unchanged.
                            if let Some(reason) = self
                                .theory
                                .explain_propagation(prop.literal.term, reason_data)
                            {
                                prop.reason = reason;
                                prop.reason_data = None;
                                // Fall through to eager path below.
                            } else {
                                self.theory
                                    .mark_propagation_rejected(prop.literal.term, reason_data);
                                continue;
                            }
                        } else {
                            // Unassigned — use lazy path.
                            lazy_propagation_pairs.push((lit, reason_data));
                            continue;
                        }
                    } else {
                        // Term not mapped — skip.
                        continue;
                    }
                }
            }

            // #qfax-t3-unmapped-hoist: the propagated term has no SAT variable —
            // the propagation is dropped below regardless (see the
            // `props_unmapped` site), so skip it BEFORE paying structural +
            // semantic verification and proof plumbing. `term_to_var` is an
            // immutable borrow for this extension's lifetime, so "unmapped"
            // cannot change mid-solve. Behavior-identical to the late drop:
            // unmapped propagations were never delivered to SAT, never became
            // conflicts, and never produced clauses. Measured on the QF_AX
            // swap t3 family: 220k of 283k theory propagations per solve were
            // dropped here after full verification.
            if self.term_to_var.get(&prop.literal.term).is_none() {
                self.eager_stats.props_unmapped += 1;
                if *PROP_DEBUG.get_or_init(|| std::env::var_os("AY_PROP_DEBUG").is_some()) {
                    if let Some(terms) = self.terms {
                        safe_eprintln!(
                            "PROPDBG UNMAPPED {} := {}",
                            prop.literal.value,
                            format_term_recursive(terms, prop.literal.term, 8)
                        );
                    }
                }
                continue;
            }

            // Verify propagation structure (#4346)
            log_propagation_debug(&prop, "eager");
            if let Err(e) = verify_theory_propagation(&prop) {
                // #8595: Skipping a propagation is safe (completeness, not soundness),
                // but surface the failure in debug builds.
                debug_assert!(
                    false,
                    "BUG(#4666): theory propagation verification failed: {e}"
                );
                tracing::warn!(
                    error = %e,
                    "BUG(#4666): theory propagation verification failed; skipping (#8595)"
                );
                continue;
            }

            // Semantic propagation verification (#4346, #6242): reason ∧ ¬propagated → ⊥
            //
            // #8529: Promoted to all builds. Without this soundness gate, implied-
            // bound propagations with incorrect reasons cause false SAT on QF_LRA
            // benchmarks (synched.base.smt2). The fast algebraic path handles most
            // single-variable propagations in O(1). Only multi-variable propagations
            // that fail the algebraic fast path create a fresh LRA solver.
            //
            // #8256: Sampling-based verification for large formulas. On QF_LRA
            // benchmarks with 800+ row tableaux (simple_startup, labyrinth),
            // verify_propagation_semantic creates a fresh LRA solver for each
            // multi-variable propagation that fails the algebraic fast path.
            // Profile data shows this consumes 26% of total runtime on
            // simple_startup_10nodes. The sampling interval is computed once
            // and applied to every Nth propagation, maintaining the soundness
            // gate while reducing overhead from O(propagations) to O(propagations/N).
            //
            // Interval computation: for formulas with >1000 theory atoms, sample
            // every 64th propagation (catching ~1.5% of unsound propagations per
            // pass). For smaller formulas, verify every propagation (interval=1).
            // The algebraic fast path (O(1) per propagation) always runs regardless
            // of sampling — only the expensive fresh-solver fallback is sampled.
            if let Some(terms) = self.terms {
                const SEMANTIC_VERIFY_TERM_LIMIT: usize = 50_000;
                if terms.len() <= SEMANTIC_VERIFY_TERM_LIMIT {
                    // Compute sampling interval on first use (lazy init).
                    if self.semantic_verify_interval == 0 {
                        self.semantic_verify_interval = if self.theory_atoms.len() > 1000 {
                            // Large formula: sample every 64th propagation.
                            // The algebraic fast path still catches most single-variable
                            // bound-chain errors. Sampling only affects the expensive
                            // multi-variable fresh-solver path.
                            64
                        } else {
                            // Small formula: verify every propagation (no sampling).
                            1
                        };
                    }

                    self.semantic_verify_sample_counter += 1;
                    let should_verify = self.semantic_verify_interval <= 1
                        || self
                            .semantic_verify_sample_counter
                            .is_multiple_of(u64::from(self.semantic_verify_interval));

                    if should_verify {
                        ay_lia::instrument::bump_verify_prop_selected();
                        // #qfuflia-a2-verifier-reuse: EUF-domain propagations
                        // verify against the cached verify-only solver
                        // (push/assert/check/pop) instead of constructing a
                        // fresh one per propagation. Semantics identical to
                        // verify_euf_propagation; on any non-definitive
                        // outcome the check treats the propagation as
                        // unverifiable-but-allowed, exactly like the fresh
                        // path.
                        let prop_domain =
                            crate::verification::classify_propagation_domain(terms, &prop);
                        // #verify-memo (AY_VERIFY_MEMO=1, default off =
                        // byte-identical): obligation memo for the two arms
                        // WITHOUT one — the cached mixed-domain N-O verifier
                        // (each check still pays the full N-O fixpoint, ~20k
                        // verify-partition LIA checks/run on hash_sat_08_04)
                        // and the fresh-solver dispatch. Array has its own
                        // memo; EUF's cached push/pop check is already
                        // O(merges) with its own warmup/sampling. Key = the
                        // canonical literal-set signature of the exact
                        // verified obligation (sorted reasons + propagated
                        // literal — the verify_array_memo discipline). The
                        // verifier is a pure function of (terms, obligation)
                        // and TermIds are stable/hash-consed, so an identical
                        // key means an identical query and the replayed
                        // verdict is exactly what a re-run would return.
                        // Trust-TRUE-only: only ACCEPTS are memoized, every
                        // rejection re-runs the complete fail-closed check.
                        // COVERAGE is unchanged: the sampling policy above is
                        // untouched, and a hit replays a verdict recorded
                        // from a FULL verification of the byte-identical
                        // obligation this solve.
                        let verify_memo_key: Option<Vec<(u32, bool)>> =
                            if crate::verification::verify_memo_armed()
                                && self.verify_prop_memo.is_some()
                                && matches!(
                                    prop_domain,
                                    crate::verification::TheoryDomain::Unknown
                                        | crate::verification::TheoryDomain::Arithmetic
                                        | crate::verification::TheoryDomain::BitVec
                                        | crate::verification::TheoryDomain::String
                                )
                            {
                                let mut key: Vec<(u32, bool)> =
                                    prop.reason.iter().map(|l| (l.term.0, l.value)).collect();
                                key.sort_unstable();
                                key.push((prop.literal.term.0, prop.literal.value));
                                Some(key)
                            } else {
                                None
                            };
                        let verify_memo_hit =
                            match (&verify_memo_key, self.verify_prop_memo.as_deref()) {
                                (Some(k), Some(memo)) => memo.get(k) == Some(&true),
                                _ => false,
                            };
                        if verify_memo_key.is_some() {
                            ay_lia::instrument::bump_verify_prop_memo(verify_memo_hit);
                        }
                        let verified_by_cache = if verify_memo_hit {
                            // Identical obligation previously FULLY verified
                            // and accepted this solve — replay the verdict.
                            Some(true)
                        } else if prop_domain == crate::verification::TheoryDomain::Unknown {
                            ay_lia::instrument::bump_verify_prop_mixed_full();
                            // Mixed-domain: cached Nelson-Oppen verifier.
                            let cache = self.verify_mixed_cache.get_or_insert_with(|| {
                                let all_terms = prop
                                    .reason
                                    .iter()
                                    .map(|l| l.term)
                                    .chain(std::iter::once(prop.literal.term));
                                crate::verification::make_verification_combiner(terms, all_terms)
                            });
                            use ay_core::{TheoryResult, TheorySolver};
                            cache.push();
                            for lit in &prop.reason {
                                cache.register_atom(lit.term);
                            }
                            cache.register_atom(prop.literal.term);
                            for lit in &prop.reason {
                                cache.assert_literal(lit.term, lit.value);
                            }
                            cache.assert_literal(prop.literal.term, !prop.literal.value);
                            let verdict = cache.check();
                            cache.pop();
                            match verdict {
                                TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                                    Some(true)
                                }
                                TheoryResult::Sat => Some(false),
                                _ => Some(true), // Unknown/split: allow (optimistic arm)
                            }
                        } else if prop_domain == crate::verification::TheoryDomain::Array {
                            // #qfax-swap-verifier-memo: ARRAY-domain
                            // propagations memoize the FRESH verifier's
                            // verdict keyed on the exact query — (propagated
                            // term, value, sorted reason literal set). The
                            // fresh path (verify_array_propagation) re-inits
                            // the full e-graph on the first assert of every
                            // verified propagation — measured at ~34% of
                            // solve time on the SMT-COMP QF_AX swap family —
                            // and CDCL re-derives the SAME theory propagation
                            // over and over across backtracking/restarts.
                            // verify_propagation_semantic is a pure function
                            // of (terms, propagation): TermIds are stable and
                            // hash-consed, so an identical key means an
                            // identical query and the cached verdict is
                            // EXACTLY what the fresh path would return. Gate
                            // strength is unchanged — every distinct query
                            // still runs the full fail-closed fresh check.
                            // (A long-lived cached array_euf combiner was
                            // tried first and measured 3x SLOWER: its
                            // check() replays the ever-growing cross-theory
                            // equality history per call.)
                            let mut key: Vec<(u32, bool)> =
                                prop.reason.iter().map(|l| (l.term.0, l.value)).collect();
                            key.sort_unstable();
                            key.push((prop.literal.term.0, prop.literal.value));
                            match self.verify_array_memo.get(&key) {
                                Some(&allowed) => Some(allowed),
                                None => {
                                    // #12-restore mirror for ARRAY (see the EUF
                                    // arm below): fully verify the first WARMUP
                                    // array propagations (solver bugs manifest
                                    // early), then sample every 64th distinct
                                    // query. The QF_AX swap family re-derives
                                    // tens of thousands of DISTINCT (reason,
                                    // literal) queries per solve, each paying a
                                    // fresh full e-graph init. Completeness-
                                    // not-soundness framing is identical to the
                                    // EUF/LRA sampling policies already in
                                    // tree: a sampled-out propagation is
                                    // ACCEPTED (never dropped — the
                                    // #soundness-qf-ax-swap hazard was wrongly
                                    // DROPPING valid propagations), unsound
                                    // ones are caught by the warmup + sampled
                                    // fraction + per-conflict semantic
                                    // verification + the independent SAT model
                                    // gate. Sampled-out verdicts are NOT
                                    // memoized, so a later sampled re-check of
                                    // the same query still runs fresh.
                                    const ARRAY_SEM_WARMUP: u64 = 512;
                                    self.verify_array_sem_counter += 1;
                                    let n = self.verify_array_sem_counter;
                                    if n > ARRAY_SEM_WARMUP && !n.is_multiple_of(64) {
                                        Some(true)
                                    } else {
                                        let allowed =
                                            verify_propagation_semantic(&prop, terms).is_ok();
                                        // Memoize ACCEPTS only. A rejection may
                                        // be SplitUnconfirmed because the split
                                        // equality atom is not interned YET —
                                        // the identical key could verify later
                                        // once the atom exists, so caching the
                                        // rejection would pin a completeness
                                        // loss. Rejections are rare (they log
                                        // errors) and cheap to recompute at
                                        // their frequency. Bound the memo so a
                                        // pathological run cannot grow it
                                        // without limit; on overflow we just
                                        // stop inserting (every query still
                                        // verified, only slower).
                                        const VERIFY_ARRAY_MEMO_CAP: usize = 1 << 20;
                                        if allowed
                                            && self.verify_array_memo.len() < VERIFY_ARRAY_MEMO_CAP
                                        {
                                            self.verify_array_memo.insert(key, allowed);
                                        }
                                        Some(allowed)
                                    }
                                }
                            }
                        } else if prop_domain == crate::verification::TheoryDomain::Euf {
                            // #12-restore: EUF warmup-then-sample gate on the
                            // CACHED verifier arm. The cached push/assert/
                            // check/pop is O(merges) — far cheaper than the
                            // old fresh-solver rebuild — but EUF finite-model
                            // instances fire 10k+ propagations with few atoms
                            // (so the #8256 interval above stays 1 = verify
                            // EVERY prop), and per-prop scope churn measured a
                            // 2.3x wall regression on NEQ/SEQ (NEQ016_size5
                            // 1.7s->3.9s) vs the sampled fresh path it
                            // replaced. Mirror the oracle-validated #12
                            // policy: cheap STRUCTURAL check always; fully
                            // verify the first WARMUP EUF props (solver bugs
                            // manifest early); then sample every 64th.
                            // Completeness-not-soundness: a sampled-out prop
                            // is never asserted verified-wrong, and unsound
                            // EUF props are caught by the sampled fraction +
                            // the structural check + SAT model validation.
                            // EUF-ONLY — the mixed-domain arm above and the
                            // LRA/BV fresh dispatch below are untouched
                            // (LRA's gate catches REAL input-dependent
                            // unsound props, #8529).
                            if verify_theory_propagation(&prop).is_err() {
                                Some(false)
                            } else {
                                use std::cell::Cell;
                                thread_local!(static EUF_SEM_CTR: Cell<u64> = const { Cell::new(0) });
                                const WARMUP: u64 = 512;
                                let n = EUF_SEM_CTR.with(|c| {
                                    let v = c.get().wrapping_add(1);
                                    c.set(v);
                                    v
                                });
                                if n > WARMUP && !n.is_multiple_of(64) {
                                    Some(true)
                                } else {
                                    let cache = self.verify_euf_cache.get_or_insert_with(|| {
                                        ay_euf::EufSolver::new(terms).verify_only()
                                    });
                                    use ay_core::{TheoryResult, TheorySolver};
                                    cache.push();
                                    for lit in &prop.reason {
                                        cache.assert_literal(lit.term, lit.value);
                                    }
                                    cache.assert_literal(prop.literal.term, !prop.literal.value);
                                    let verdict = cache.check();
                                    cache.pop();
                                    match verdict {
                                        TheoryResult::Unsat(_)
                                        | TheoryResult::UnsatWithFarkas(_) => Some(true),
                                        TheoryResult::Sat => Some(false),
                                        // Unknown/splits: skip-not-fail (see euf.rs)
                                        _ => Some(true),
                                    }
                                }
                            }
                        } else {
                            None
                        };
                        if verified_by_cache == Some(false) {
                            tracing::error!(
                                propagated_term = ?prop.literal.term,
                                propagated_value = prop.literal.value,
                                reason_count = prop.reason.len(),
                                "BUG(#6242): propagation semantic verification failed (cached); skipping unsound propagation"
                            );
                            continue;
                        }
                        if verified_by_cache.is_none() {
                            ay_lia::instrument::bump_verify_prop_fresh_full();
                            if let Err(e) = verify_propagation_semantic(&prop, terms) {
                                tracing::error!(
                                    error = %e,
                                    propagated_term = ?prop.literal.term,
                                    propagated_value = prop.literal.value,
                                    reason_count = prop.reason.len(),
                                    "BUG(#6242): propagation semantic verification failed; skipping unsound propagation"
                                );
                                continue;
                            }
                        }
                        // #verify-memo: reaching here means the obligation was
                        // ACCEPTED (rejections `continue` above). Record the
                        // full-verification accept for identical re-derivations
                        // this solve. Bounded like VERIFY_ARRAY_MEMO_CAP; on
                        // overflow we stop inserting (every query still
                        // verified, only slower).
                        if !verify_memo_hit {
                            if let (Some(key), Some(memo)) =
                                (verify_memo_key, self.verify_prop_memo.as_deref_mut())
                            {
                                const VERIFY_PROP_MEMO_CAP: usize = 1 << 20;
                                if memo.len() < VERIFY_PROP_MEMO_CAP {
                                    memo.insert(key, true);
                                }
                            }
                        }
                    }
                } else {
                    tracing::debug!(
                        term_count = terms.len(),
                        limit = SEMANTIC_VERIFY_TERM_LIMIT,
                        "semantic propagation verification skipped: term count exceeds budget (#8558)"
                    );
                }
            }

            // Convert the propagated literal to SAT. The unmapped case
            // (`None`) was counted and skipped BEFORE verification by the
            // #qfax-t3-unmapped-hoist above, so this lookup always succeeds
            // here; the `if let` shape is kept as defensive structure.
            if let Some(lit) = self.term_to_literal(prop.literal.term, prop.literal.value) {
                let var = lit.variable();

                // Check current assignment
                if let Some(value) = ctx.value(var) {
                    if value != prop.literal.value {
                        // Theory propagated opposite of current assignment - conflict!
                        let mut conflict: Vec<Literal> = prop
                            .reason
                            .iter()
                            .filter_map(|r| self.term_to_literal(r.term, !r.value))
                            .collect();
                        // Soundness guard (#3826): partial clause check. Dropping
                        // reason terms makes the conflict stronger than what the
                        // theory proved.
                        if conflict.len() < prop.reason.len() {
                            self.partial_clause_count += 1;
                            crate::combined_solvers::theory_stats::inc_partial_clauses();
                            if self.partial_clause_count >= 100 {
                                tracing::error!(
                                    count = self.partial_clause_count,
                                    "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                                );
                            }
                            self.emit_eager_event(
                                sat_level,
                                asserted_theory_atoms,
                                "unknown",
                                0,
                                propagate_start,
                            );
                            continue;
                        }
                        // Reason literal falsification guard (#6262): every
                        // reason literal must be falsified. If not, the theory
                        // produced an invalid explanation — skip this conflict.
                        let all_reasons_falsified = conflict.iter().all(|reason_lit| {
                            let rv = reason_lit.variable();
                            ctx.value(rv).is_some_and(|v| v != reason_lit.is_positive())
                        });
                        if !all_reasons_falsified {
                            tracing::warn!(
                                propagated = ?lit,
                                reason_count = conflict.len(),
                                "BUG(#6262): theory propagation conflict has non-falsified reason literal; skipping"
                            );
                            continue;
                        }
                        conflict.push(lit);

                        if self.debug {
                            safe_eprintln!(
                                "[EAGER] Theory propagation conflict: {} literals",
                                conflict.len()
                            );
                        }
                        self.theory_conflict_count += 1;
                        self.emit_eager_event(
                            sat_level,
                            asserted_theory_atoms,
                            "conflict",
                            0,
                            propagate_start,
                        );
                        // #8421: Collect variables from propagation conflict for VSIDS bumping.
                        let bump_vars: Vec<ay_sat::Variable> =
                            conflict.iter().map(|lit| lit.variable()).collect();
                        return ExtPropagateResult::conflict(conflict).with_bump_vars(bump_vars);
                    }
                    // Already assigned correctly - skip.
                    //
                    // #euf-prop-gap: when the atom's SAT variable is
                    // ITE-GUARDED, this skip used to be an unbounded churn
                    // loop. The ITE relevancy filter (#8125) defers guarded
                    // atoms from the trail feed, so the theory never learns
                    // the SAT assignment; its propagation scans keep seeing
                    // the atom as unassigned and re-derive the SAME
                    // propagation on every BCP round — each paying explain()
                    // + verification — only for it to be dropped right here
                    // (QF_UF rushhour: 4.67M drops for 24k delivered clauses,
                    // 10/10 sampled drops ITE-guarded).
                    // Feed the assignment back to the theory exactly as the
                    // trail feed would have (same term, same value — the SAT
                    // value MATCHES the theory-entailed value here), so the
                    // theory's assign set catches up and the scans stop
                    // re-proposing. Sound: the atom IS assigned this value in
                    // the SAT trail; un-deferring an atom is always sound
                    // (the deferral is a relevancy optimization, and
                    // `check_impl` re-flushes deferred atoms anyway). Scoped
                    // to guarded vars: unguarded atoms reach the theory via
                    // the normal trail feed next round, no loop is possible.
                    self.eager_stats.props_already_assigned += 1;
                    // Kill switch: AY_NO_PROP_FEEDBACK=1 restores the old
                    // drop-only behavior (A/B lever + safety valve).
                    static NO_FEEDBACK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                    let feedback_enabled = !*NO_FEEDBACK
                        .get_or_init(|| std::env::var_os("AY_NO_PROP_FEEDBACK").is_some());
                    let ite_guarded = self.term_to_var.get(&prop.literal.term).is_some_and(|&v| {
                        let idx = v as usize;
                        let w = idx / 64;
                        w < self.ite_guarded_bitset.len()
                            && (self.ite_guarded_bitset[w] >> (idx % 64)) & 1 != 0
                    });
                    if ite_guarded && feedback_enabled {
                        self.theory
                            .assert_literal(prop.literal.term, prop.literal.value);
                        self.eager_stats.props_fed_back += 1;
                    }
                    continue;
                }

                // Literal is unassigned - create propagation clause
                // Clause: (propagated_lit ∨ ¬reason1 ∨ ¬reason2 ∨ ...)
                // Propagated literal is placed FIRST for add_theory_propagation.
                let mut clause: Vec<Literal> = Vec::with_capacity(prop.reason.len() + 1);
                clause.push(lit); // propagated literal first
                let reason_count = prop.reason.len();
                for r in &prop.reason {
                    if let Some(reason_lit) = self.term_to_literal(r.term, !r.value) {
                        clause.push(reason_lit);
                    }
                }
                // Soundness guard (#3826): if any reason term failed to map,
                // the propagation clause would be too strong. Skip it.
                if clause.len() - 1 < reason_count {
                    self.partial_clause_count += 1;
                    crate::combined_solvers::theory_stats::inc_partial_clauses();
                    if self.partial_clause_count >= 100 {
                        tracing::error!(
                            count = self.partial_clause_count,
                            "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                        );
                    }
                    continue;
                }

                // Reason literal falsification guard (#6262): every reason
                // literal (clause[1..]) must be falsified under the current SAT
                // assignment. If any reason literal is unassigned or satisfied,
                // the theory produced an invalid propagation reason — demote
                // from lightweight propagation to a full theory lemma clause
                // that handles watches correctly.
                let all_reasons_falsified = clause[1..].iter().all(|reason_lit| {
                    let rv = reason_lit.variable();
                    ctx.value(rv).is_some_and(|v| v != reason_lit.is_positive())
                });
                if !all_reasons_falsified {
                    tracing::warn!(
                        propagated = ?lit,
                        reason_count = clause.len() - 1,
                        "BUG(#6262): theory propagation has non-falsified reason literal; demoting to lemma"
                    );
                    // Add as a regular watched clause instead of a propagation.
                    // add_theory_lemma handles watches and BCP correctly for
                    // clauses with arbitrary literal assignment states.
                    clauses.push(clause);
                    continue;
                }

                if self.debug {
                    safe_eprintln!(
                        "[EAGER] Adding propagation clause: {} literals (propagates {:?}={})",
                        clause.len(),
                        var,
                        prop.literal.value
                    );
                }

                // SAT-honest-closer: at decision level 0, ALSO record this theory
                // propagation as a term-space theory lemma so the honest empty-clause
                // closer (`derive_empty_via_level0_rup`) can chain through it by genuine
                // resolution instead of the sound-but-opaque Trust fallback (the residual
                // "fell back to trust" on level-0 ROOT theory conflicts, e.g. i128 guarded
                // arithmetic). The clause here already passed the partial-clause (#3826)
                // and reason-falsification (#6262) guards, so it is a GENUINE theory
                // entailment `(prop_lit ∨ ¬reason…)`. Mirror the bound-axiom recorder at
                // the top of this fn: map each SAT literal to its term (via `negations`
                // for negative polarity), FAIL-CLOSED if any term is missing (never record
                // a strict subclause), attach a Farkas cert for a 2-literal arithmetic
                // bound implication, else Generic. Sound: recording a genuine derived
                // clause for RUP cannot mint a false proof; a missing term skips it.
                if ctx.decision_level() == 0 {
                    let terms_opt = self.terms;
                    if let Some(proof_ctx) = self.proof.as_mut() {
                        let mut term_clause: Vec<TermId> = Vec::with_capacity(clause.len());
                        let mut ok = true;
                        // Propagated literal at its asserted polarity.
                        if prop.literal.value {
                            term_clause.push(prop.literal.term);
                        } else if let Some(&neg) = proof_ctx.negations.get(&prop.literal.term) {
                            term_clause.push(neg);
                        } else {
                            ok = false;
                        }
                        // Reason literals: the clause carries `¬reason` (polarity !value).
                        if ok {
                            for r in &prop.reason {
                                if !r.value {
                                    term_clause.push(r.term);
                                } else if let Some(&neg) = proof_ctx.negations.get(&r.term) {
                                    term_clause.push(neg);
                                } else {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        // ONLY record a genuine Farkas-certified ARITHMETIC bound
                        // implication (`infer_bound_axiom_arith_kind` = Some). A `Generic`
                        // (uncertified) lemma is NOT strict-checkable — it would be an
                        // opaque trust step, defeating the honest-closure purpose AND
                        // perturbing the EUF/array/datatype proof-firewall tests — so
                        // those propagations are LEFT to the existing (sound) path. The
                        // arithmetic case is exactly the level-0 LIA-bound root conflict
                        // the i128/guarded-arithmetic fallbacks need.
                        let kind = if ok && prop.reason.len() == 1 {
                            terms_opt.and_then(|terms| {
                                infer_bound_axiom_arith_kind(
                                    terms,
                                    prop.literal.term,
                                    prop.reason[0].term,
                                    prop.literal.value,
                                    prop.reason[0].value,
                                )
                            })
                        } else {
                            None
                        };
                        if let Some(k) = kind {
                            let _ = proof_ctx.tracker.add_theory_lemma_with_farkas_and_kind(
                                term_clause,
                                FarkasAnnotation::from_ints(&[1i64, 1]),
                                k,
                            );
                        }
                    }
                }

                // Use lightweight propagation path (#4919): skip watch setup,
                // VSIDS bump, sort/dedup. Clause is stored only as reason.
                self.eager_stats.props_clause_added += 1;
                // Temporary campaign instrumentation (#qfax-t3-atom-space).
                if *PROP_DEBUG.get_or_init(|| std::env::var_os("AY_PROP_DEBUG").is_some()) {
                    if let Some(terms) = self.terms {
                        let mut rkey: Vec<(u32, bool)> =
                            prop.reason.iter().map(|l| (l.term.0, l.value)).collect();
                        rkey.sort_unstable();
                        safe_eprintln!(
                            "PROPDBG MAPPED {} rn={} rkey={:?} := {}",
                            prop.literal.value,
                            prop.reason.len(),
                            rkey,
                            format_term_recursive(terms, prop.literal.term, 8)
                        );
                    }
                }
                propagation_pairs.push((clause, lit));
            }
        }

        // #8008: Raised from 3 to 50 to match the zero-propagation path.
        // Threshold of 3 caused premature Unknown on sc-* QF_LRA benchmarks.
        let stop_for_expression_split = self.expr_split_seen_count >= 50
            && matches!(
                &self.pending_split,
                Some(TheoryResult::NeedExpressionSplit(_))
            );
        let stop = stop_for_expression_split || stop_for_inline_refinement_handoff;
        if stop_for_inline_refinement_handoff {
            self.eager_stats.bound_refinement_handoffs += 1;
        }

        let total_props = clauses.len() + propagation_pairs.len() + lazy_propagation_pairs.len();
        if total_props == 0 {
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                check_result_label,
                0,
                propagate_start,
            );
            ExtPropagateResult::new(clauses, propagation_pairs, None, stop)
        } else {
            self.theory_propagation_count += total_props as u64;
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                "propagated",
                total_props,
                propagate_start,
            );
            // #8421: Collect variables from propagation clauses for VSIDS bumping.
            // Theory propagation variables should be prioritized in decisions.
            let mut bump_vars: Vec<ay_sat::Variable> = Vec::new();
            for (clause, _) in &propagation_pairs {
                for lit in clause {
                    bump_vars.push(lit.variable());
                }
            }
            for clause in &clauses {
                for lit in clause {
                    bump_vars.push(lit.variable());
                }
            }
            // #8467: Include lazy propagation variables in VSIDS bumps.
            for (lit, _) in &lazy_propagation_pairs {
                bump_vars.push(lit.variable());
            }
            let mut result = ExtPropagateResult::new(clauses, propagation_pairs, None, stop)
                .with_bump_vars(bump_vars);
            result.lazy_propagations = lazy_propagation_pairs;
            result
        }
    }

    /// Process early-drained propagations during batch deferral (#8422).
    ///
    /// This converts TheoryPropagation into SAT propagation pairs, handling
    /// the same term-to-literal mapping, already-assigned filtering, and
    /// partial-clause guards as the main propagation path. It does NOT run
    /// check_during_propagate() or the full propagation pipeline.
    ///
    /// #8467: Handles both eager propagations (with materialized reasons) and
    /// lazy propagations (with reason_data). Lazy propagations from
    /// drain_pending_propagations are routed to the SAT solver's lazy
    /// propagation path, avoiding O(reason_len) allocation.
    ///
    /// Returns ExtPropagateResult with the converted propagations, or
    /// a conflict if one of the propagated literals contradicts the current
    /// SAT assignment.
    /// #euf-prop-gap helpers shared by every "already assigned — skip" site
    /// (the propagate_impl eager site inlines the same logic — the original
    /// landed fix). See the long rationale comment at that site: feeding the
    /// SAT-assigned value of an ITE-GUARDED atom back to the theory stops the
    /// unbounded re-derivation churn caused by the ITE relevancy filter
    /// deferring the atom from the trail feed. Sound: the atom IS assigned
    /// that value in the SAT trail; un-deferring is a relevancy no-op.
    fn prop_feedback_enabled() -> bool {
        static NO_FEEDBACK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        !*NO_FEEDBACK.get_or_init(|| std::env::var_os("AY_NO_PROP_FEEDBACK").is_some())
    }

    /// Whether the atom's SAT variable is ITE-guarded (deferred from the
    /// trail feed by the #8125 relevancy filter). Mirrors the landed
    /// propagate_impl check bit-for-bit.
    fn is_ite_guarded_term(&self, term: TermId) -> bool {
        self.term_to_var.get(&term).is_some_and(|&v| {
            let idx = v as usize;
            let w = idx / 64;
            w < self.ite_guarded_bitset.len() && (self.ite_guarded_bitset[w] >> (idx % 64)) & 1 != 0
        })
    }

    fn process_early_propagations(
        &mut self,
        propagations: Vec<ay_core::TheoryPropagation>,
        sat_level: u32,
        asserted_theory_atoms: usize,
        propagate_start: Option<ay_core::time::Instant>,
        ctx: &dyn SolverContext,
    ) -> ExtPropagateResult {
        let mut clauses: Vec<Vec<Literal>> = Vec::new();
        let mut propagation_pairs: Vec<(Vec<Literal>, Literal)> = Vec::new();
        // #8467: Lazy propagations from drain path.
        let mut lazy_propagation_pairs: Vec<(Literal, u64)> = Vec::new();

        for mut prop in propagations {
            // #8467: Handle lazy propagations from drain_pending_propagations.
            // Same logic as the main propagation loop in propagate_impl.
            if prop.is_lazy() {
                if let Some(reason_data) = prop.reason_data {
                    if let Some(lit) = self.term_to_literal(prop.literal.term, prop.literal.value) {
                        let var = lit.variable();
                        if let Some(value) = ctx.value(var) {
                            if value != prop.literal.value {
                                // Opposite assignment — must materialize for conflict.
                                if let Some(reason) = self
                                    .theory
                                    .explain_propagation(prop.literal.term, reason_data)
                                {
                                    prop.reason = reason;
                                    prop.reason_data = None;
                                    // Fall through to eager path below.
                                } else {
                                    self.theory
                                        .mark_propagation_rejected(prop.literal.term, reason_data);
                                    continue;
                                }
                            } else {
                                // Already assigned correctly — skip.
                                //
                                // #euf-prop-gap (lazy twin): same ITE-deferral
                                // blind-spot churn as the eager site — feed the
                                // SAT value back, scoped to guarded vars, same
                                // kill switch (AY_NO_PROP_FEEDBACK=1).
                                self.eager_stats.props_already_assigned += 1;
                                if Self::prop_feedback_enabled()
                                    && self.is_ite_guarded_term(prop.literal.term)
                                {
                                    self.theory
                                        .assert_literal(prop.literal.term, prop.literal.value);
                                    self.eager_stats.props_fed_back += 1;
                                }
                                continue;
                            }
                        } else if reason_data & ay_euf::EUF_LAZY_MAGIC_MASK
                            == ay_euf::EUF_LAZY_MAGIC
                            && self.is_ite_guarded_term(prop.literal.term)
                        {
                            // Unassigned EUF token on an ITE-guarded atom —
                            // materialize now and take the eager path
                            // (permanent clause). See the #euf-lazy-explain
                            // carve-out rationale at the propagate_impl twin
                            // site.
                            if let Some(reason) = self
                                .theory
                                .explain_propagation(prop.literal.term, reason_data)
                            {
                                prop.reason = reason;
                                prop.reason_data = None;
                                // Fall through to eager path below.
                            } else {
                                self.theory
                                    .mark_propagation_rejected(prop.literal.term, reason_data);
                                continue;
                            }
                        } else {
                            // Unassigned — use lazy path.
                            lazy_propagation_pairs.push((lit, reason_data));
                            continue;
                        }
                    } else {
                        continue;
                    }
                }
            }

            log_propagation_debug(&prop, "early_drain");
            if let Err(e) = verify_theory_propagation(&prop) {
                // #8595: Skipping a propagation is safe (completeness, not soundness).
                debug_assert!(
                    false,
                    "BUG(#8422): early drain propagation verification failed: {e}"
                );
                tracing::warn!(
                    error = %e,
                    "BUG(#8422): early drain propagation verification failed; skipping (#8595)"
                );
                continue;
            }

            if let Some(lit) = self.term_to_literal(prop.literal.term, prop.literal.value) {
                let var = lit.variable();

                if let Some(value) = ctx.value(var) {
                    if value != prop.literal.value {
                        // Conflict: theory propagated opposite of SAT assignment.
                        let mut conflict: Vec<Literal> = prop
                            .reason
                            .iter()
                            .filter_map(|r| self.term_to_literal(r.term, !r.value))
                            .collect();
                        if conflict.len() < prop.reason.len() {
                            self.partial_clause_count += 1;
                            crate::combined_solvers::theory_stats::inc_partial_clauses();
                            continue;
                        }
                        let all_reasons_falsified = conflict.iter().all(|reason_lit| {
                            let rv = reason_lit.variable();
                            ctx.value(rv).is_some_and(|v| v != reason_lit.is_positive())
                        });
                        if !all_reasons_falsified {
                            continue;
                        }
                        conflict.push(lit);
                        self.theory_conflict_count += 1;
                        let bump_vars: Vec<ay_sat::Variable> =
                            conflict.iter().map(|lit| lit.variable()).collect();
                        return ExtPropagateResult::conflict(conflict).with_bump_vars(bump_vars);
                    }
                    // Already assigned correctly - skip.
                    //
                    // #euf-prop-gap (early-drain eager twin): same ITE-deferral
                    // blind-spot churn as the propagate_impl eager site — feed
                    // the SAT value back, scoped to guarded vars, same kill
                    // switch (AY_NO_PROP_FEEDBACK=1).
                    self.eager_stats.props_already_assigned += 1;
                    if Self::prop_feedback_enabled() && self.is_ite_guarded_term(prop.literal.term)
                    {
                        self.theory
                            .assert_literal(prop.literal.term, prop.literal.value);
                        self.eager_stats.props_fed_back += 1;
                    }
                    continue;
                }

                // Unassigned: create propagation clause.
                let mut clause: Vec<Literal> = Vec::with_capacity(prop.reason.len() + 1);
                clause.push(lit);
                let reason_count = prop.reason.len();
                for r in &prop.reason {
                    if let Some(reason_lit) = self.term_to_literal(r.term, !r.value) {
                        clause.push(reason_lit);
                    }
                }
                if clause.len() - 1 < reason_count {
                    self.partial_clause_count += 1;
                    crate::combined_solvers::theory_stats::inc_partial_clauses();
                    continue;
                }

                // Reason falsification guard.
                let all_reasons_falsified = clause[1..].iter().all(|reason_lit| {
                    let rv = reason_lit.variable();
                    ctx.value(rv).is_some_and(|v| v != reason_lit.is_positive())
                });
                if !all_reasons_falsified {
                    // Non-falsified reasons: demote to lemma clause.
                    clauses.push(clause);
                    continue;
                }

                propagation_pairs.push((clause, lit));
            }
        }

        let total_props = clauses.len() + propagation_pairs.len() + lazy_propagation_pairs.len();
        if total_props == 0 {
            // No usable propagations from the drain -- proceed with normal batch defer.
            self.eager_stats.batch_defers += 1;
            self.emit_eager_event(
                sat_level,
                asserted_theory_atoms,
                "batch_defer",
                0,
                propagate_start,
            );
            return ExtPropagateResult::none();
        }

        self.theory_propagation_count += total_props as u64;
        self.zero_propagation_streak = 0;
        self.total_bcp_propagations += total_props as u64;
        self.total_bcp_productive_prop_calls += 1;
        self.emit_eager_event(
            sat_level,
            asserted_theory_atoms,
            "early_propagated",
            total_props,
            propagate_start,
        );
        let mut bump_vars: Vec<ay_sat::Variable> = Vec::new();
        for (clause, _) in &propagation_pairs {
            for lit in clause {
                bump_vars.push(lit.variable());
            }
        }
        for clause in &clauses {
            for lit in clause {
                bump_vars.push(lit.variable());
            }
        }
        // #8467: Include lazy propagation variables in VSIDS bumps.
        for (lit, _) in &lazy_propagation_pairs {
            bump_vars.push(lit.variable());
        }
        let mut result = ExtPropagateResult::new(clauses, propagation_pairs, None, false)
            .with_bump_vars(bump_vars);
        result.lazy_propagations = lazy_propagation_pairs;
        result
    }
}
