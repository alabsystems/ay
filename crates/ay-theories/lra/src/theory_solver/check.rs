// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `check()` pipeline for the LRA theory solver.

use super::*;

impl LraSolver {
    pub(super) fn check_impl(&mut self) -> TheoryResult {
        self.stats.check_count += 1;
        let debug = self.debug_lra;
        self.pending_bound_refinements.clear();
        // #8468: Clear BCP freshness flag — full check runs its own implied
        // bounds pass so any stale BCP freshness is irrelevant.
        self.implied_bounds_fresh = false;
        // #8003: Reset per-check pivot counter. This limits total pivots within
        // a single check() invocation, preventing dense LP problems from burning
        // unbounded CPU time in the simplex.
        self.stats.check_pivot_count = 0;
        // #8187: Reset the soundness-gate flag so it only tracks bound
        // additions that happen inside THIS invocation. Any pre-entry
        // bound-tightening state lives in `bounds_tightened_since_simplex`
        // (which drives `need_simplex` below); the gate flag is a per-call
        // latch for "bounds were added AFTER simplex ran in this call."
        self.post_simplex_bounds_added = false;

        tracing::debug!(
            asserted = self.asserted.len(),
            dirty = self.dirty,
            vars = self.vars.len(),
            rows = self.rows.len(),
            "LRA check"
        );

        // Per-atom unsupported check (#6167): only return Unknown if at least one
        // currently-asserted atom has unsupported sub-expressions. Atoms that are
        // not asserted (e.g., popped or never asserted) don't affect the result.
        let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
            && self
                .persistent_unsupported_atoms
                .iter()
                .any(|a| self.asserted.contains_key(a));

        if debug {
            safe_eprintln!(
                "[LRA] check() called, dirty={}, persistent_unsupported_atoms={}, asserted_unsupported={}",
                self.dirty,
                self.persistent_unsupported_atoms.len(),
                has_asserted_unsupported,
            );
        }

        if !self.dirty {
            if debug {
                safe_eprintln!("[LRA] Not dirty, returning early");
            }
            if !has_asserted_unsupported {
                // Soundness gate: even on the "not dirty" early-return path,
                // verify all variable values still satisfy their bounds (#6210).
                // #8187: The soundness-gate flag was reset at entry. On the
                // !dirty path no setter can fire (no atoms processed, no
                // simplex, no cascade), so `post_simplex_bounds_added` is
                // guaranteed false. #8810: run the same bound check in release
                // before returning Sat so stale assignments fail closed instead
                // of relying on model validation downstream.
                let mut result = TheoryResult::Sat;
                self.guard_sat_current_assignment_bounds(
                    &mut result,
                    "check_impl/not_dirty",
                    false,
                );
                #[cfg(debug_assertions)]
                if matches!(result, TheoryResult::Sat) {
                    self.debug_assert_bounds_satisfied();
                }
                return result;
            }
            if has_asserted_unsupported {
                tracing::warn!(
                    unsupported_count = self.persistent_unsupported_atoms.len(),
                    "LRA check_impl !dirty returning Unknown (unsupported)"
                );
            }
            return TheoryResult::Unknown;
        }
        // NOTE: Do NOT clear self.dirty here. If check() returns Unsat and the
        // SAT solver backtracks, we need dirty=true so the next check() re-runs
        // the simplex. Clearing dirty is done below, only on Sat/Unknown paths.
        // See #5537 for the false-SAT bug caused by premature dirty-flag clearing.

        // Snapshot tableau size before atom processing, so we can detect if new
        // rows were added (which requires the simplex to incorporate them).
        self.rows_at_check_start = self.rows.len();

        // Process newly-asserted atoms: parse, assert bounds, collect disequalities.
        let (disequalities, parsed_count, skipped_count) = match self.process_check_atoms(debug) {
            Ok(stats) => (stats.disequalities, stats.parsed_count, stats.skipped_count),
            Err(conflict) => return *conflict,
        };

        // Inject floor axioms for to_int terms (#5944).
        self.inject_to_int_axioms();

        // Run simplex
        if debug {
            safe_eprintln!(
                "[LRA] Atom processing: parsed={}, skipped={}, total_asserted={}, disequalities={}",
                parsed_count,
                skipped_count,
                parsed_count + skipped_count,
                disequalities.len()
            );
            // Approach G diagnostic (#4919): count bounded variables before simplex.
            // Compares against Z3's initial bound count to identify where the gap is.
            let mut free = 0u32;
            let mut lb_only = 0u32;
            let mut ub_only = 0u32;
            let mut both = 0u32;
            for info in self.vars.iter() {
                match (info.lower.is_some(), info.upper.is_some()) {
                    (false, false) => free += 1,
                    (true, false) => lb_only += 1,
                    (false, true) => ub_only += 1,
                    (true, true) => both += 1,
                }
            }
            safe_eprintln!(
                "[LRA] BEFORE simplex (check #{}): free={}, lb_only={}, ub_only={}, both={}, total={}, touched_rows={}",
                self.stats.check_count, free, lb_only, ub_only, both, self.vars.len(), self.touched_rows.len()
            );
        }
        // Simplex-skip optimization (#4919): if no bounds were tightened and no
        // new tableau rows were added during atom processing, the previous simplex
        // solution is still feasible. Skip the full simplex call — the current
        // model is still valid.
        let new_rows_added = self.rows.len() > self.rows_at_check_start;
        let need_simplex = self.bounds_tightened_since_simplex
            || new_rows_added
            || self.trivial_conflict.is_some()
            || !self.last_simplex_feasible;
        // Soundness guard (#6256): when the last simplex returned non-Sat
        // (Unsat/Unknown), variable values may be left in an infeasible state.
        // Re-run simplex instead of skipping so we preserve soundness without
        // blocking DPLL from learning the current conflict (#6209).
        let simplex_result = if need_simplex {
            self.bounds_tightened_since_simplex = false;
            // #8187: Clear the soundness-gate flag at simplex completion.
            // If run_post_simplex_propagation tightens new bounds below, this
            // flag is re-raised and the Sat-return gate picks that up.
            self.post_simplex_bounds_added = false;
            // #8009: Clear vars_tightened AFTER simplex returns so simplex can
            // use it for targeted non-basic variable scanning. Previously
            // cleared before the call, making it always empty inside simplex.
            let result = self.dual_simplex();
            self.vars_tightened_since_simplex.clear();
            self.last_simplex_feasible = matches!(result, TheoryResult::Sat);
            if self.last_simplex_feasible {
                self.enqueue_lra_basis_region_request_at_safe_boundary();
                self.drain_lra_basis_region_requests_at_safe_boundary();
                self.save_feasible_snapshot();
                // #warm-simplex: anchor the last-feasible value delta here.
                self.warm_reanchor_delta();
            } else {
                self.discard_lra_basis_region_candidate();
                // #warm-simplex: on CONFLICT, restore the last-feasible
                // assignment from the changed-vars delta (OpenSMT's conflict
                // recovery). The conflict is already fully packaged (it
                // depends on rows + bound reasons, not values), so this only
                // repositions the warm start for the post-backtrack check.
                if matches!(
                    result,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                ) {
                    self.warm_restore_last_feasible();
                }
            }
            result
        } else {
            // No bounds changed, no new rows, last simplex was feasible.
            if debug {
                safe_eprintln!("[LRA] Skipping simplex: no bounds tightened, no new rows");
            }
            TheoryResult::Sat
        };
        let simplex_is_sat = matches!(simplex_result, TheoryResult::Sat);

        // #8257: Standalone-simplex fast return. Verification/optimization
        // callers only need the simplex result. Skip all post-simplex
        // work: implied bounds, model equality discovery, phase hint caching.
        // On dense LP problems (vpm2-30, rand_*), this eliminates the
        // O(rows * width * rounds) BigRational implied-bounds overhead that
        // consumed 91% of wall time in the verification solver.
        //
        // SOUNDNESS (#8455 diseq squeeze): a bare simplex Sat is NOT a valid
        // final answer here — the fast return previously skipped two of the
        // main path's Sat-demotion gates, so a fresh verification solver could
        // answer "Sat" for a genuinely-UNSAT literal set, making the conflict
        // verifier reject a valid conflict as spurious ("fresh solver says
        // SAT") and fail-close-escalate a correct unsat to unknown:
        //
        //  1. Unsupported atoms: atom processing above may have marked atoms
        //     unsupported DURING this call (e.g. every atom mentions an
        //     uninterpreted function the standalone LRA verifier cannot
        //     interpret, as in the {g(x) >= 3, g(x) <= 3, g(x) != 3} squeeze).
        //     The entry-time `has_asserted_unsupported` is stale; recompute it
        //     and mirror the main path's Sat->Unknown downgrade (see #9224
        //     match below): an incomplete model proves nothing.
        //
        //  2. Unchecked disequalities: the simplex only sees bound encodings,
        //     so asserted disequalities must be evaluated against the model
        //     before Sat may be reported. A forced violation yields Unsat
        //     (conflict verifies); an unforced violation yields a split
        //     request (verifier accepts optimistically).
        //
        // Only a clean pass may return Sat. This removes only the false Sat;
        // all rejection paths are unchanged.
        if self.standalone_simplex_mode {
            if matches!(simplex_result, TheoryResult::Sat) {
                // Recompute after atom processing (mirrors the recompute below
                // the fast return): parsing may have added unsupported atoms.
                let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
                    && self
                        .persistent_unsupported_atoms
                        .iter()
                        .any(|a| self.asserted.contains_key(a));
                if has_asserted_unsupported {
                    self.dirty = false;
                    return TheoryResult::Unknown;
                }
                if !disequalities.is_empty() {
                    if let Some(result) = self.check_disequalities(&disequalities, debug) {
                        return result;
                    }
                }
                if !self.shared_disequality_trail.is_empty() {
                    if let Some(result) = self.check_shared_disequalities(debug) {
                        return result;
                    }
                }
            }
            self.dirty = false;
            return simplex_result;
        }

        info!(
            target: "ay::lra",
            parsed_count,
            skipped_count,
            disequalities = disequalities.len(),
            vars = self.vars.len(),
            rows = self.rows.len(),
            simplex_sat = simplex_is_sat,
            unsupported_atoms = self.persistent_unsupported_atoms.len(),
            "LRA check"
        );
        if debug {
            safe_eprintln!(
                "[LRA] simplex result: {:?}, unsupported_atoms={}",
                simplex_result,
                self.persistent_unsupported_atoms.len(),
            );
        }

        // Post-simplex: derive implied bounds, wake compound atoms, queue
        // propagations. Must run before disequality checking (#4919).
        // #8064: Run even when simplex returns infeasible -- row-based bound
        // analysis uses constraint structure, not variable values.
        self.run_post_simplex_propagation(need_simplex, debug, false);

        // Recompute has_asserted_unsupported after atom processing (new atoms
        // may have been added to persistent_unsupported_atoms during parsing).
        let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
            && self
                .persistent_unsupported_atoms
                .iter()
                .any(|a| self.asserted.contains_key(a));

        // A5 core (#qfuflia-a5): after a Sat simplex, materialize any deferred
        // equality whose expression the current assignment VIOLATES, then
        // re-run the simplex — demand-driven row generation, looped to a
        // small fixpoint. Satisfied deferrals stay row-free.
        if self.a5_core && matches!(simplex_result, TheoryResult::Sat) {
            for _round in 0..8 {
                let n = self.materialize_violated_deferred_eqs();
                if n == 0 {
                    break;
                }
                let re = self.dual_simplex();
                self.last_simplex_feasible = matches!(re, TheoryResult::Sat);
                if !matches!(re, TheoryResult::Sat) {
                    return re;
                }
            }
        }

        // If simplex returned Sat, check disequalities
        // IMPORTANT: Only check disequalities when we have complete information.
        // If any asserted atom is unsupported, the model is incomplete (e.g., ITE
        // terms created unconstrained slack variables), so we can't trust the model.
        //
        // Optimization (#4919): skip disequality evaluation when the model is unchanged
        // AND the previous evaluation found all disequalities satisfied. When need_simplex
        // was false AND no new atoms were parsed, the variable values are identical to the
        // previous check() call, so satisfied disequalities remain satisfied.
        //
        // CRITICAL (#4919): if the previous disequality check found a violation (returned
        // NeedDisequalitySplit or NeedExpressionSplit), we MUST re-check even when the model
        // hasn't changed. The violation persists and suppressing it causes false SAT results
        // that fail model validation (sc-6, sc-8, simple_startup_5 benchmarks).
        let model_may_have_changed =
            need_simplex || parsed_count > 0 || self.last_diseq_check_had_violation;
        if matches!(simplex_result, TheoryResult::Sat)
            && !disequalities.is_empty()
            && !has_asserted_unsupported
            && model_may_have_changed
        {
            if let Some(result) = self.check_disequalities(&disequalities, debug) {
                // #8707: When the disequality check requests an expression split
                // for a multi-variable disequality (e.g., pairwise `distinct`
                // over arithmetic expressions like `q_i + i != q_j + j`), the
                // legacy behaviour adds the SAT-level clause
                // `(E - F < 0) OR (E - F > 0)`. For benchmarks like n-queens
                // and SEND+MORE=MONEY, the LP keeps producing equal values
                // for variables that must be distinct, and the split loop
                // diverges because the expression-split doesn't help CDCL
                // learn the actual variable-level disequality.
                //
                // Z3's `theory_arith_aux.h:2199-2251` (`assume_eqs`) addresses
                // this by grouping variables with equal LP values and
                // proposing equality splits to CDCL. When an equality is
                // asserted, the disequality trail forces a conflict and CDCL
                // learns a variable-level blocking clause. Here we prefer the
                // `assume_eqs` guess over the expression split when the two
                // mechanisms would both apply — this is the Z3 final-check
                // round-robin order (phase 1 `assume_eqs` runs before phase 2
                // diseq handling).
                if matches!(
                    result,
                    TheoryResult::NeedExpressionSplit(_) | TheoryResult::NeedExpressionSplits(_)
                ) {
                    let mut model_eqs = self.discover_model_value_equalities();
                    // SOUNDNESS GATE (false-UNSAT on QF_LRA diseq + eq-alias):
                    // drop any proof-less model-value-equality guess that would
                    // (through the asserted-equality closure) connect into the
                    // class of an active disequality endpoint. Such a guess
                    // refutes a disequality with a NON-entailed fact (free vars
                    // only coincided in a spurious model), driving the split loop
                    // to a false UNSAT. Justified guesses (non-empty reason) are
                    // kept. Kill switch AY_NO_DISEQ_CLOSURE_GUARD restores the
                    // old behaviour.
                    self.filter_unsound_model_eq_guesses(&mut model_eqs);
                    // Fix A: only prefer model-value-equality guesses over the
                    // disequality split when at least one is justified or native
                    // arithmetic. Proof-less guesses over opaque UF-application
                    // interface variables make the eager non-persistent split
                    // loop diverge (EUF+LIA incompleteness); fall through to the
                    // already-sufficient split instead.
                    let prefer_model_eqs = model_eqs
                        .iter()
                        .any(|req| self.model_eq_pair_prefer_over_split(req));
                    if !model_eqs.is_empty() && prefer_model_eqs {
                        if debug {
                            safe_eprintln!(
                                "[LRA] assume_eqs (over expression-split): discovered {} model-value equalities",
                                model_eqs.len()
                            );
                        }
                        let mut all_requests = model_eqs;
                        if self.pending_fixed_term_equalities.len() > 1 {
                            all_requests.extend(self.take_pending_fixed_term_model_equalities());
                        }
                        if !self.pending_offset_equalities.is_empty() {
                            all_requests.extend(self.take_pending_offset_equalities());
                        }
                        // Keep dirty so re-checking still happens after CDCL
                        // learns the blocking clause (mirrors the original
                        // NeedExpressionSplit code path).
                        self.dirty = true;
                        self.last_diseq_check_had_violation = true;
                        return if all_requests.len() == 1 {
                            TheoryResult::NeedModelEquality(
                                all_requests
                                    .into_iter()
                                    .next()
                                    .expect("invariant: len() == 1"),
                            )
                        } else {
                            TheoryResult::NeedModelEqualities(all_requests)
                        };
                    }
                }
                return result;
            }
        }

        // Check shared disequalities from Nelson-Oppen (#5228).
        // These have reason-literal vectors instead of a single atom.
        if matches!(simplex_result, TheoryResult::Sat)
            && !self.shared_disequality_trail.is_empty()
            && !has_asserted_unsupported
        {
            if let Some(result) = self.check_shared_disequalities(debug) {
                if matches!(
                    result,
                    TheoryResult::NeedExpressionSplit(_) | TheoryResult::NeedExpressionSplits(_)
                ) {
                    let mut model_eqs = self.discover_model_value_equalities();
                    // SOUNDNESS GATE (see per-theory path above): drop proof-less
                    // model-eq guesses that would touch an active disequality.
                    self.filter_unsound_model_eq_guesses(&mut model_eqs);
                    // Fix A: same native-arith / justified gate as the per-theory
                    // disequality path above (see comment there).
                    let prefer_model_eqs = model_eqs
                        .iter()
                        .any(|req| self.model_eq_pair_prefer_over_split(req));
                    if !model_eqs.is_empty() && prefer_model_eqs {
                        if debug {
                            safe_eprintln!(
                                "[LRA] assume_eqs (over shared expression-split): discovered {} model-value equalities",
                                model_eqs.len()
                            );
                        }
                        let mut all_requests = model_eqs;
                        if self.pending_fixed_term_equalities.len() > 1 {
                            all_requests.extend(self.take_pending_fixed_term_model_equalities());
                        }
                        if !self.pending_offset_equalities.is_empty() {
                            all_requests.extend(self.take_pending_offset_equalities());
                        }
                        self.dirty = true;
                        return if all_requests.len() == 1 {
                            TheoryResult::NeedModelEquality(
                                all_requests
                                    .into_iter()
                                    .next()
                                    .expect("invariant: len() == 1"),
                            )
                        } else {
                            TheoryResult::NeedModelEqualities(all_requests)
                        };
                    }
                }
                return result;
            }
        }

        // #9224: Refine the unsupported-atom guard. Only downgrade UNSAT to
        // Unknown when the conflict itself involves an unsupported atom.
        // Conflicts over fully-understood atoms are valid regardless of whether
        // other unrelated unsupported atoms exist. SAT results still downgrade
        // to Unknown because the model may be incomplete.
        let mut result = match simplex_result {
            TheoryResult::Sat if has_asserted_unsupported => {
                tracing::warn!(
                    unsupported_count = self.persistent_unsupported_atoms.len(),
                    asserted_unsupported = self
                        .persistent_unsupported_atoms
                        .iter()
                        .filter(|a| self.asserted.contains_key(*a))
                        .count(),
                    "LRA check_impl simplex=Sat but unsupported, returning Unknown"
                );
                if debug {
                    safe_eprintln!(
                        "[LRA] Returning Unknown (sat with unsupported): {} unsupported atoms, {} asserted",
                        self.persistent_unsupported_atoms.len(),
                        self.persistent_unsupported_atoms
                            .iter()
                            .filter(|a| self.asserted.contains_key(*a))
                            .count(),
                    );
                }
                TheoryResult::Unknown
            }
            // #6812/#9224: When unsupported atoms are asserted, a simplex UNSAT
            // may be spurious IF the conflict depends on bounds from atoms that
            // LRA cannot fully interpret. But if the conflict only involves
            // fully-understood atoms, it is valid and should not be suppressed.
            TheoryResult::Unsat(ref lits) if has_asserted_unsupported => {
                let conflict_involves_unsupported = lits
                    .iter()
                    .any(|l| self.persistent_unsupported_atoms.contains(&l.term));
                if conflict_involves_unsupported {
                    if debug {
                        safe_eprintln!(
                            "[LRA] Returning Unknown (unsat conflict involves unsupported): {} unsupported, {} asserted",
                            self.persistent_unsupported_atoms.len(),
                            self.persistent_unsupported_atoms
                                .iter()
                                .filter(|a| self.asserted.contains_key(*a))
                                .count(),
                        );
                    }
                    TheoryResult::Unknown
                } else {
                    simplex_result
                }
            }
            TheoryResult::UnsatWithFarkas(ref conflict) if has_asserted_unsupported => {
                let conflict_involves_unsupported = conflict
                    .literals
                    .iter()
                    .any(|l| self.persistent_unsupported_atoms.contains(&l.term));
                if conflict_involves_unsupported {
                    if debug {
                        safe_eprintln!(
                            "[LRA] Returning Unknown (farkas conflict involves unsupported): {} unsupported, {} asserted",
                            self.persistent_unsupported_atoms.len(),
                            self.persistent_unsupported_atoms
                                .iter()
                                .filter(|a| self.asserted.contains_key(*a))
                                .count(),
                        );
                    }
                    TheoryResult::Unknown
                } else {
                    simplex_result
                }
            }
            other => other,
        };
        if matches!(result, TheoryResult::Sat) {
            self.queue_model_seeded_propagations(debug);
            // Collect equality requests from both fixed-term and offset equality mechanisms.
            let mut all_requests = Vec::new();
            if self.pending_fixed_term_equalities.len() > 1 {
                all_requests.extend(self.take_pending_fixed_term_model_equalities());
            }
            if !self.pending_offset_equalities.is_empty() {
                all_requests.extend(self.take_pending_offset_equalities());
            }
            // Model-value equality detection (Z3's assume_eqs): group shared
            // variables by their model value and suggest equalities. This is
            // critical for benchmarks with many equality comparisons (#8901).
            if all_requests.is_empty() {
                let mut model_eqs = self.discover_model_value_equalities();
                // SOUNDNESS GATE (see expression-split paths above): drop
                // proof-less model-eq guesses that would touch an active
                // disequality through the asserted-equality closure.
                self.filter_unsound_model_eq_guesses(&mut model_eqs);
                if debug && !model_eqs.is_empty() {
                    safe_eprintln!(
                        "[LRA] assume_eqs: discovered {} model-value equalities",
                        model_eqs.len()
                    );
                }
                all_requests.extend(model_eqs);
            }
            if !all_requests.is_empty() {
                result = if all_requests.len() == 1 {
                    TheoryResult::NeedModelEquality(
                        all_requests
                            .into_iter()
                            .next()
                            .expect("invariant: len() == 1"),
                    )
                } else {
                    TheoryResult::NeedModelEqualities(all_requests)
                };
            }
        }
        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            // eprintln!("[LRA-DEBUG] check() returning UNSAT/UnsatWithFarkas (simplex passthrough)");
            self.stats.conflict_count += 1;
            self.stats.full_check_conflict_count += 1;
            // Leave dirty=true so next check() re-runs the simplex after
            // backtrack. Without this, backtrack without pop causes check()
            // to skip the simplex and return false Sat (#5537).
        } else {
            // Sat or Unknown: simplex state is consistent, safe to cache.
            self.dirty = false;
        }

        // #8187/#8810 soundness gate: when returning Sat, verify all variable
        // values satisfy their bounds in release mode. This catches false-SAT
        // bugs at the point of origin before the result propagates to the DPLL
        // loop or relies on model validation.
        //
        // Release behavior: explicitly re-evaluate the cached assignment
        // against the current bounds:
        //
        //   * If every bound is still satisfied -> the cascade tightened
        //     bounds that the cached model already respects. It is sound to
        //     return Sat. Clear `post_simplex_bounds_added` since the
        //     assignment has been shown consistent with the new bound set.
        //
        //   * If any bound is violated -> the cached assignment is stale for
        //     the active bounds. Demote Sat to Unknown, mark simplex stale, and
        //     keep dirty=true; the next check() will re-run simplex and either
        //     find a feasible model or generate a proper Farkas conflict.
        //
        // The earlier #8187 gate only checked this in release when
        // `post_simplex_bounds_added` was true. That fixed the known cascade
        // race, but left other stale-cache paths protected only by the debug
        // assertion. #8810 makes the release check unconditional on final Sat.
        //
        // One previous version of this gate unconditionally demoted on
        // `post_simplex_bounds_added == true`, which preserved soundness
        // but sacrificed completeness: benchmarks where the cascade added
        // bounds the assignment already satisfied (e.g.
        // sc-8.induction3.cvc.smt2, EZSMT+ 1.smt2/5.smt2) looped on
        // Unknown+dirty until the timeout. See #8187, #8810, #5534.
        //
        // Debug behavior: `debug_assert_bounds_satisfied()` runs
        // unconditionally when returning Sat to catch any latent
        // false-SAT that slips past the release check.
        if matches!(result, TheoryResult::Sat) {
            self.guard_sat_current_assignment_bounds(&mut result, "check_impl/final", false);
        }
        #[cfg(debug_assertions)]
        if matches!(result, TheoryResult::Sat) {
            self.debug_assert_bounds_satisfied();
        }

        result
    }

    /// Request SAT-level link lemmas for term-level arithmetic ITEs before
    /// accepting Sat.
    ///
    /// `parse_linear_expr` interns `(ite cond then else)` as an opaque
    /// variable (see the `TermData::Ite` arm) and records the tuple in
    /// `ite_link_terms`. The opaque variable is sound for conflicts (any
    /// infeasibility proved with the variable unconstrained holds for every
    /// ITE value), but Sat models need the exact branch semantics. This hook
    /// converts a Sat result into `NeedModelEqualities` carrying, for each
    /// recorded ITE whose link equalities are not yet in the term store:
    ///
    /// - `cond        => (= ite then)`  (reason `[cond=true]`, implied)
    /// - `(not cond)  => (= ite else)`  (reason `[cond=false]`, implied)
    ///
    /// The split-loop encoders turn each implied request into the SAT clause
    /// `!reason \/ (= lhs rhs)` plus arithmetic triangle atoms, so the branch
    /// coupling lives at the Boolean level with the condition literal as a
    /// real premise in every downstream explanation. Once both equality atoms
    /// exist in the term store, the request is not repeated (`find_eq` gate),
    /// so fixpoint termination is preserved across solver reconstructions.
    pub(crate) fn request_ite_link_lemmas_on_sat(&mut self, result: TheoryResult) -> TheoryResult {
        if !matches!(result, TheoryResult::Sat) || self.ite_link_terms.is_empty() {
            return result;
        }

        let mut requests = Vec::new();
        for &(ite_term, cond, then_t, else_t) in &self.ite_link_terms {
            if self.terms().find_eq(ite_term, then_t).is_some()
                && self.terms().find_eq(ite_term, else_t).is_some()
            {
                continue;
            }
            // Normalize negated conditions so the reason literal refers to the
            // positively-encoded atom.
            let (cond_key, cond_true_value) = match self.terms().get(cond) {
                TermData::Not(inner) => (*inner, false),
                _ => (cond, true),
            };
            requests.push(ModelEqualityRequest {
                lhs: ite_term,
                rhs: then_t,
                reason: vec![TheoryLit::new(cond_key, cond_true_value)],
                implied: true,
            });
            requests.push(ModelEqualityRequest {
                lhs: ite_term,
                rhs: else_t,
                reason: vec![TheoryLit::new(cond_key, !cond_true_value)],
                implied: true,
            });
        }

        if requests.is_empty() {
            return result;
        }
        // Keep dirty so the post-encode re-check re-runs the full pipeline.
        self.dirty = true;
        if requests.len() == 1 {
            TheoryResult::NeedModelEquality(
                requests.into_iter().next().expect("invariant: len() == 1"),
            )
        } else {
            TheoryResult::NeedModelEqualities(requests)
        }
    }

    /// Lightweight BCP-time check: run arithmetic consistency and post-simplex
    /// propagation, but defer disequality/model-only work to the final check.
    pub(super) fn check_during_propagate_impl(&mut self) -> TheoryResult {
        self.stats.check_count += 1;
        let debug = self.debug_lra;
        if !self.pending_bound_refinements.is_empty() {
            self.pending_bound_refinements.clear();
        }
        // #8003: Reset per-check pivot counter (same as check_impl).
        self.stats.check_pivot_count = 0;
        // #8187: Reset the soundness-gate flag (see check_impl doc above).
        self.post_simplex_bounds_added = false;

        // #8255: Check dirty BEFORE computing has_asserted_unsupported.
        // The dirty check is O(1) and the most common fast-exit path for BCP.
        // The has_asserted_unsupported check is O(|persistent_unsupported_atoms|)
        // and only needed when dirty=false AND unsupported atoms exist (rare for
        // pure QF_LRA), or when we reach the result classification at the end.
        // Deferring it to when actually needed avoids ~2K unnecessary set scans
        // per solve on sc-8 (6219 checks * 55% non-fast-skip = 2786 calls that
        // previously computed this eagerly).
        if !self.dirty {
            // Only compute has_asserted_unsupported on the !dirty path where
            // we actually need it for the return value.
            let has_asserted_unsupported = !self.persistent_unsupported_atoms.is_empty()
                && self
                    .persistent_unsupported_atoms
                    .iter()
                    .any(|a| self.asserted.contains_key(a));
            if has_asserted_unsupported {
                tracing::warn!(
                    unsupported_count = self.persistent_unsupported_atoms.len(),
                    "LRA BCP check !dirty returning Unknown (unsupported)"
                );
                return TheoryResult::Unknown;
            }
            // #8187/#8810 soundness gate, mirroring check_impl's final gate:
            // even on the !dirty BCP early-return, the cached assignment can be
            // stale relative to the active bounds — e.g. a basic variable left
            // at an epsilon value just above a non-strict upper bound after a
            // budget-bounded simplex (hhk2008 var 72). The previous code ran
            // `debug_assert_bounds_satisfied()` here UNCONDITIONALLY with no
            // guard, so such a stale assignment crashed debug builds and (with
            // asserts off) returned a false SAT in release. Re-validate the
            // assignment and demote Sat -> Unknown on any violation so the debug
            // assert only runs on a genuinely feasible model and release fails
            // closed.
            let mut result = TheoryResult::Sat;
            self.guard_sat_current_assignment_bounds(
                &mut result,
                "check_during_propagate/not_dirty",
                true,
            );
            #[cfg(debug_assertions)]
            if matches!(result, TheoryResult::Sat) {
                self.debug_assert_bounds_satisfied();
            }
            return result;
        }

        self.rows_at_check_start = self.rows.len();

        let atom_stats = match self.process_check_atoms_bcp(debug) {
            Ok(stats) => stats,
            Err(conflict) => return *conflict,
        };

        self.inject_to_int_axioms();

        let new_rows_added = self.rows.len() > self.rows_at_check_start;
        let need_simplex = self.bounds_tightened_since_simplex
            || new_rows_added
            || self.trivial_conflict.is_some()
            || !self.last_simplex_feasible;

        // #8255: Fast exit when atom processing found zero new arithmetic atoms
        // to assert AND there's no pending simplex work. In this case the theory
        // state is unchanged from the last check: no new bounds were tightened,
        // no rows touched, no dirty vars. The only trail advancement was over
        // already-bounded or non-arithmetic atoms. Skip simplex + post-simplex
        // entirely and clear dirty (since the trail is now fully processed).
        if atom_stats.parsed_count == 0
            && !need_simplex
            && self.touched_rows.is_empty()
            && self.propagation_dirty_vars.is_empty()
            && !self.direct_bounds_changed_since_implied
        {
            self.stats.bcp_post_simplex_fast_skips += 1;
            let has_deferred_disequalities =
                !self.disequality_trail.is_empty() || !self.shared_disequality_trail.is_empty();
            let has_deferred_full_check_work = has_deferred_disequalities
                || !self.pending_fixed_term_equalities.is_empty()
                || !self.pending_offset_equalities.is_empty();
            self.dirty = has_deferred_full_check_work || self.bounds_tightened_since_simplex;
            return TheoryResult::Sat;
        }
        // #8064: Use dual_simplex_propagate() for all BCP simplex calls.
        //
        // Previously, a three-phase budget reduction system progressively
        // dropped the simplex budget to 10 -> 2 -> 1 pivot(s) based on
        // check/conflict counts. This caused ~15 QF_LRA benchmarks to
        // return Unknown: after 200 BCP checks, Phase 3 allowed only 1
        // pivot, at which point the pre_loop_fast_path in
        // dual_simplex_with_max_iters returns Sat immediately when the
        // infeasible heap is empty. The theory solver became blind to
        // conflicts and the DPLL loop explored the Boolean space endlessly.
        //
        // Fix: always use dual_simplex_propagate() which has a proportional
        // budget of max(50, rows). This budget:
        // - Is large enough to catch real conflicts (not just trivial ones)
        // - Scales with problem size
        // - Still caps degenerate cases
        // - Returns Sat on budget exhaustion, deferring to full check()
        //
        // #8187: Attempted deferred-simplex mode (skip BCP simplex for large
        // formulas, Z3-style) caused false UNSAT on simple_startup_7nodes.
        // Root cause: check_impl does not reliably re-discover conflicts
        // deferred from BCP when bounds_tightened_since_simplex is stale.
        // BCP simplex MUST remain unconditional until the full-check path
        // is hardened. See ay-lra/src/lib.rs:full_check_conflict_count.
        //
        // SOUNDNESS: only clear bounds_tightened_since_simplex when simplex
        // runs to completion (no budget exhaustion). When budget exhausts,
        // keep the flag TRUE so the full check_impl() re-runs simplex.
        let simplex_result = if need_simplex {
            let prev_exhaustions = self.stats.propagation_budget_exhaustions;
            let r = self.dual_simplex_propagate();
            let budget_exhausted = self.stats.propagation_budget_exhaustions > prev_exhaustions;
            if budget_exhausted {
                self.stats.bcp_simplex_skips += 1;
                self.discard_lra_basis_region_candidate();
            } else {
                self.bounds_tightened_since_simplex = false;
                // #8187: Clear the soundness-gate flag at simplex completion
                // ONLY when simplex ran to completion (budget not exhausted).
                // Budget-exhausted simplex leaves variable values in a
                // potentially inconsistent state, so the gate must still fire.
                self.post_simplex_bounds_added = false;
                self.vars_tightened_since_simplex.clear();
            }
            self.last_simplex_feasible = matches!(r, TheoryResult::Sat);
            if self.last_simplex_feasible {
                self.enqueue_lra_basis_region_request_at_safe_boundary();
                self.drain_lra_basis_region_requests_at_safe_boundary();
                self.save_feasible_snapshot();
                // #warm-simplex: anchor the last-feasible value delta here.
                self.warm_reanchor_delta();
            } else {
                self.discard_lra_basis_region_candidate();
                // #warm-simplex conflict recovery (see check_impl).
                if matches!(r, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)) {
                    self.warm_restore_last_feasible();
                }
            }
            r
        } else {
            TheoryResult::Sat
        };
        // #8553: Bound propagation is always active (Z3 arith_propagation_threshold
        // = UINT_MAX). The simplex budget (max(200, 5*num_vars)) bounds per-call cost.
        //
        // #8255: BCP fast-skip -- when simplex didn't run, no rows were touched
        // by atom processing, no dirty vars accumulated, and no direct bounds
        // changed since the last implied-bounds pass, run_post_simplex_propagation
        // is provably a no-op:
        //   1. Implied bounds block is gated by
        //      (need_simplex || has_cascade_rows)
        //      -- all false, so it's skipped entirely.
        //   2. Dirty-var propagation iterates propagation_dirty_vars -- empty,
        //      so compound and bound propagations produce nothing.
        // Skipping the function call avoids the scratch-buffer take/clear/sort
        // overhead that accumulates across thousands of BCP callbacks.
        let bcp_fast_skip = !need_simplex
            && self.touched_rows.is_empty()
            && self.propagation_dirty_vars.is_empty()
            && !self.direct_bounds_changed_since_implied;
        if !bcp_fast_skip {
            self.run_post_simplex_propagation(need_simplex, debug, true);
            // #8468: Mark implied bounds as fresh so propagate_impl() can skip
            // its own compute_implied_bounds call when no new direct bounds
            // have been asserted between check and propagate.
            // #8422: Only mark fresh when the fixpoint fully converged. When the
            // fixpoint hit the cap (propagate_direct_touched_rows_pending still
            // true), the cascade has unconsumed touched_rows that propagate_impl
            // should continue processing. Setting implied_bounds_fresh=true in
            // this case would skip that continuation, losing propagation volume.
            self.implied_bounds_fresh = !self.propagate_direct_touched_rows_pending;
        } else {
            self.stats.bcp_post_simplex_fast_skips += 1;
        }

        // #8255: Lazy has_asserted_unsupported evaluation. For pure QF_LRA
        // benchmarks (most), persistent_unsupported_atoms is empty, making
        // the entire unsupported-atom guard dead code. Check emptiness first
        // (O(1)) and only do the O(|unsupported|) intersection scan when the
        // set is non-empty AND the result needs it (Sat or conflict paths).
        // Previously, this O(n) scan ran unconditionally on every BCP check,
        // contributing to the 84% propagation-loop overhead reported in #8255.
        //
        // #9224: Refine unsupported-atom guard (same logic as check_impl).
        // Only downgrade UNSAT when the conflict itself involves unsupported atoms.
        let mut result = if self.persistent_unsupported_atoms.is_empty() {
            // Fast path: no unsupported atoms at all. Skip the entire guard.
            simplex_result
        } else {
            // Slow path: unsupported atoms exist. Compute intersection with asserted.
            let has_asserted_unsupported = self
                .persistent_unsupported_atoms
                .iter()
                .any(|a| self.asserted.contains_key(a));
            match simplex_result {
                TheoryResult::Sat if has_asserted_unsupported => {
                    tracing::warn!(
                        unsupported_count = self.persistent_unsupported_atoms.len(),
                        "LRA BCP check simplex=Sat but unsupported, returning Unknown"
                    );
                    TheoryResult::Unknown
                }
                TheoryResult::Unsat(ref lits) if has_asserted_unsupported => {
                    let conflict_involves_unsupported = lits
                        .iter()
                        .any(|l| self.persistent_unsupported_atoms.contains(&l.term));
                    if conflict_involves_unsupported {
                        TheoryResult::Unknown
                    } else {
                        simplex_result
                    }
                }
                TheoryResult::UnsatWithFarkas(ref conflict) if has_asserted_unsupported => {
                    let conflict_involves_unsupported = conflict
                        .literals
                        .iter()
                        .any(|l| self.persistent_unsupported_atoms.contains(&l.term));
                    if conflict_involves_unsupported {
                        TheoryResult::Unknown
                    } else {
                        simplex_result
                    }
                }
                other => other,
            }
        };

        // #8187 soundness gate (BCP path): when returning Sat with
        // `post_simplex_bounds_added` TRUE, `run_post_simplex_propagation`
        // tightened a direct bound AFTER the simplex-completion clear in
        // this invocation. The cached variable values may be stale relative
        // to the new bound set.
        //
        // Re-evaluate the current assignment against the new bounds to
        // distinguish a spurious cascade (bounds still satisfied -- safe
        // Sat) from a genuine invalidation (bound violated -- must demote).
        //
        // Completeness (this path): if the cache satisfies every bound, we
        // are sound to return Sat and clear the gate flag. If we demoted
        // unconditionally here, benchmarks where the cascade merely
        // restates derivable bounds (e.g. sc-8.induction3.cvc.smt2) would
        // loop on Unknown+dirty -- the next BCP check sees dirty=true,
        // re-runs simplex, reaches the same state, and the gate fires
        // again.
        //
        // Soundness (this path): if any bound is violated, demote Sat to
        // Unknown. The dirty/deferred-work bookkeeping below picks this up
        // (keeps dirty=true via the `matches!(result, TheoryResult::Unknown)`
        // branch) so the next check() re-runs simplex on the fresh bounds
        // and generates a conflict if the tableau is now infeasible.
        //
        // This is the site that produced the non-deterministic false SAT on
        // sc-8.induction3 and the related QF_LRA benchmarks (#8810, #5534,
        // #8187). The original gate bypassed `debug_assert_bounds_satisfied`
        // when the flag was true and returned Sat unchecked. The
        // intermediate fix (TL1, commit 53db8e719) unconditionally demoted,
        // restoring soundness at the cost of completeness. This version
        // preserves both.
        // #8187/#8810 soundness gate (unconditional): the previous gate only
        // re-validated the cached assignment when `post_simplex_bounds_added`
        // was true. But a budget-exhausted dual_simplex_propagate can leave a
        // basic variable out of bounds in the epsilon dimension (hhk2008 var 72
        // = epsilon above a non-strict upper bound 0) with that flag false, so
        // the old gate let the false SAT through — caught only by the debug
        // assert below (a debug-only crash) and silently wrong in release.
        // Validate the full assignment against every active bound (InfRational /
        // epsilon space) and demote Sat -> Unknown on any violation, mirroring
        // check_impl's final gate. Dropping to Unknown is always sound; the
        // guard sets `dirty` so the next check() re-runs simplex on fresh bounds.
        self.guard_sat_current_assignment_bounds(&mut result, "check_during_propagate/final", true);

        let has_deferred_disequalities =
            !self.disequality_trail.is_empty() || !self.shared_disequality_trail.is_empty();
        let has_deferred_full_check_work = has_deferred_disequalities
            || !self.pending_fixed_term_equalities.is_empty()
            || !self.pending_offset_equalities.is_empty();

        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            self.stats.conflict_count += 1;
        } else {
            // Preserve deferred full-check work: the final check() must revisit
            // skipped disequality/model-equality logic even when the arithmetic
            // state itself is already simplex-feasible.
            // #8064: Also preserve dirty when bounds_tightened_since_simplex is
            // still set (from budget exhaustion). Otherwise check_impl() will
            // see dirty=false and skip re-running simplex, missing conflicts.
            // #8187: Additionally keep dirty=true when the gate demoted Sat to
            // Unknown so the next check() re-runs simplex on fresh bounds.
            self.dirty = has_deferred_full_check_work
                || self.bounds_tightened_since_simplex
                || matches!(result, TheoryResult::Unknown);
            if has_deferred_disequalities {
                self.last_diseq_check_had_violation = true;
            }
        }

        // #8187 debug soundness gate: when returning Sat, verify all variable
        // values satisfy their bounds unconditionally. When the demotion above
        // fired, `result` is no longer Sat. When the demotion did not fire,
        // `post_simplex_bounds_added` is false and the assert is genuinely
        // safe to run.
        #[cfg(debug_assertions)]
        if matches!(result, TheoryResult::Sat) {
            self.debug_assert_bounds_satisfied();
        }

        result
    }

    /// Save the current variable values as a feasible-model snapshot (#8064).
    ///
    /// Called whenever simplex returns Sat. The snapshot is used by
    /// `suggest_phase()` to provide LP-model-consistent phase hints even
    /// when the current simplex state is infeasible.
    /// Save variable values for the feasible snapshot used by phase advice.
    ///
    /// #8255: Skip the O(num_vars) copy when simplex didn't pivot since the
    /// last snapshot. If total_pivots hasn't changed, no variable values were
    /// modified by simplex, so the snapshot is identical to what we already have.
    /// On sc-6.induction3, simplex_sat fires 8782 times but many are trivially
    /// feasible (pre-loop fast path, 0 pivots). Skipping these eliminates
    /// thousands of O(vars) Rational clone loops during BCP.
    pub(crate) fn save_feasible_snapshot(&mut self) {
        // #inc-guard-memo anchor: trust ONLY the fully-verified simplex Sat
        // exit (`last_simplex_verified` — heap-empty basic check + full
        // non-basic `violates_bounds` scan, the guard's exact predicate).
        // Optimistic Sats (budget-exhaustion conversion, pre-loop fast path,
        // BLAS bridge — the #8810 hhk2008 family) leave the flag false, so
        // the propagation-time guards keep their full rescan for them. This
        // O(1) anchor is what collapses the measured 3.3e9 redundant
        // var-scans at BMC depth 14.
        self.guard_clean_valid = self.last_simplex_verified;
        if self.stats.total_pivots == self.pivots_at_last_snapshot
            && !self.feasible_value_snapshot.is_empty()
        {
            self.stats.snapshot_pivot_skips += 1;
            return;
        }
        self.pivots_at_last_snapshot = self.stats.total_pivots;
        let n = self.vars.len();
        let old_len = self.feasible_value_snapshot.len();

        // #D1: Incrementally refresh the phase-hint cache. The full rebuild
        // re-evaluates EVERY registered atom with exact Rational arithmetic
        // after every feasible simplex result — the #1 in-solver hot leaf
        // (~17% of solver time on DRAGON-class BMC). Instead, detect which
        // variable values actually changed since the last snapshot and
        // re-evaluate only the atoms over those variables (via var_to_atoms).
        // Atoms over unchanged variables keep their cached phase, which is
        // exactly the value a full rebuild would recompute
        // (evaluate_atom_phase_inner depends only on the atom's expression
        // variables, and registration.rs indexes every atom under each such
        // variable). Phase hints are heuristic, but this stays bit-identical
        // to the full rebuild for every atom present, so suggest_phase remains
        // deterministic. Fall back to a full rebuild whenever the snapshot or
        // the cache was reset (old_len == 0 || cache empty) so the two
        // structures stay in sync.
        if old_len == 0 || self.phase_hint_cache.is_empty() {
            self.feasible_value_snapshot.resize(n, Rational::zero());
            for (i, var_info) in self.vars.iter().enumerate() {
                self.feasible_value_snapshot[i] = var_info.value.x_rational();
            }

            // #8008: Pre-compute phase hints for all registered atoms against
            // the fresh feasible snapshot. This makes suggest_phase() an O(1)
            // lookup instead of O(coefficients) Rational arithmetic per atom.
            self.rebuild_phase_hint_cache();
            return;
        }

        self.feasible_value_snapshot.resize(n, Rational::zero());
        let mut changed_vars: Vec<u32> = Vec::new();
        for i in 0..n {
            let new_val = self.vars[i].value.x_rational();
            if i >= old_len || self.feasible_value_snapshot[i] != new_val {
                changed_vars.push(i as u32);
            }
            self.feasible_value_snapshot[i] = new_val;
        }

        if changed_vars.is_empty() {
            // Simplex pivoted but every variable's rational value reverted to
            // its previous feasible value — the cache is already correct.
            return;
        }
        // When most variables changed, the incremental gather (which collects,
        // sorts, and dedups the union of var_to_atoms over every changed var)
        // would cost more than a straight full rebuild and can blow up the tail
        // (overlapping wide-atom lists). Cap it: fall back to the full rebuild
        // once a quarter of the variables changed. This bounds the worst case
        // to the original full-rebuild cost while keeping the localized-change
        // fast path that BMC's per-decision checks hit.
        if changed_vars.len().saturating_mul(4) >= n {
            self.rebuild_phase_hint_cache();
        } else {
            self.rebuild_phase_hint_cache_incremental(&changed_vars);
        }
    }

    /// Rebuild the phase hint cache for all registered atoms using the current
    /// variable values (which should be feasible when called from
    /// save_feasible_snapshot).
    ///
    /// Evaluates each atom's linear expression against the current model and
    /// stores the model-consistent polarity. Atoms whose variables are not yet
    /// initialized (out of bounds) are skipped.
    ///
    /// Uses split borrows: iterates `registered_atoms` and `atom_cache` (read),
    /// evaluates against `vars` (read), writes to `phase_hint_cache` (write).
    fn rebuild_phase_hint_cache(&mut self) {
        self.phase_hint_cache.clear();
        // Collect atoms to iterate without holding a borrow on self.
        // registered_atoms is typically small (hundreds of atoms), so the
        // Vec allocation is negligible compared to the Rational arithmetic saved.
        let atoms: Vec<TermId> = self.registered_atoms.iter().copied().collect();
        for atom in atoms {
            if let Some(phase) = Self::evaluate_atom_phase_inner(&self.atom_cache, &self.vars, atom)
            {
                self.phase_hint_cache.insert(atom, phase);
            }
        }
        // A rebuild may have changed any suggestion; advance the phase-hint
        // epoch so the SAT-side seeder re-seeds rather than skipping. See
        // `LraSolver::phase_hint_epoch` / `TheorySolver::phase_hint_epoch`.
        self.phase_hint_epoch = self.phase_hint_epoch.wrapping_add(1);
    }

    /// #D1: Incremental counterpart to `rebuild_phase_hint_cache`. Re-evaluates
    /// only the atoms that reference a variable in `changed_vars` (looked up via
    /// `var_to_atoms`), preserving cache entries for atoms over unchanged
    /// variables. `registration.rs` indexes every atom under each variable in
    /// its expression (`registration.rs:126-157`), so any atom whose evaluated
    /// phase could have changed since the last feasible snapshot is guaranteed
    /// to be revisited here. Atoms that now evaluate to `None` (e.g. an
    /// uninitialized variable) are removed to match the full-rebuild semantics
    /// (which only inserts `Some`-valued atoms).
    fn rebuild_phase_hint_cache_incremental(&mut self, changed_vars: &[u32]) {
        // Gather the unique set of atoms touching any changed variable. A
        // wide atom may appear under several changed variables; dedup so it is
        // evaluated once (re-evaluation is idempotent, this only bounds work).
        let mut atoms: Vec<TermId> = Vec::new();
        for &var in changed_vars {
            if let Some(list) = self.var_to_atoms.get(&var) {
                atoms.extend_from_slice(list);
            }
        }
        atoms.sort_unstable();
        atoms.dedup();
        for atom in atoms {
            match Self::evaluate_atom_phase_inner(&self.atom_cache, &self.vars, atom) {
                Some(phase) => {
                    self.phase_hint_cache.insert(atom, phase);
                }
                None => {
                    self.phase_hint_cache.remove(&atom);
                }
            }
        }
        // An incremental rebuild touched at least one atom over a changed
        // variable; advance the phase-hint epoch so the SAT-side seeder
        // re-seeds. See `TheorySolver::phase_hint_epoch`.
        self.phase_hint_epoch = self.phase_hint_epoch.wrapping_add(1);
    }

    /// Evaluate a single atom against variable values and return the
    /// model-consistent polarity.
    ///
    /// Static helper to avoid borrow conflicts during cache rebuild.
    /// Takes the atom_cache and vars as explicit references.
    fn evaluate_atom_phase_inner(
        atom_cache: &HashMap<TermId, Option<ParsedAtomInfo>>,
        vars: &[VarInfo],
        atom: TermId,
    ) -> Option<bool> {
        let info = atom_cache.get(&atom)?.as_ref()?;

        // Evaluate the expression using current variable values.
        let mut val = info.expr.constant.clone();
        for &(var, ref coeff) in &info.expr.coeffs {
            let vi = var as usize;
            let var_info = vars.get(vi)?;
            val += coeff * &var_info.value.x_rational();
        }

        // Equality atoms: (= x y) true iff expr == 0
        if info.is_eq {
            return Some(val.is_zero());
        }

        // Distinct atoms: (distinct x y) true iff expr != 0
        if info.is_distinct {
            return Some(!val.is_zero());
        }

        // Inequality atoms with boundary-case fix: strict atoms at val == 0
        // return Some(false) instead of None. Z3's compare_values() returns
        // false for strict inequalities at the boundary (0 < 0 is false,
        // 0 > 0 is false). Returning None caused the SAT solver to use its
        // default phase (positive), which may be theory-inconsistent.
        if info.is_le {
            if info.strict {
                // atom asserts expr < 0
                Some(val.is_negative())
            } else {
                // atom asserts expr <= 0
                Some(!val.is_positive())
            }
        } else {
            // atom asserts expr >= 0 (or expr > 0 if strict)
            if info.strict {
                Some(val.is_positive())
            } else {
                Some(!val.is_negative())
            }
        }
    }
}
