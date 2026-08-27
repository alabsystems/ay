// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Final theory consistency check for the eager extension.
//!
//! Extracted from `mod.rs` to keep that file under the 1,200-line target.
//! Contains the `check_impl` helper called by the `Extension::check` trait method.

use ay_core::{TheoryLit, TheoryResult, TheorySolver};
use ay_sat::ExtCheckResult;

use crate::theory_inference::{
    record_theory_conflict_unsat, record_theory_conflict_unsat_with_farkas,
};
use crate::verification::{
    conflict_has_array_context, log_conflict_debug, verify_euf_conflict, verify_theory_conflict,
    verify_theory_conflict_with_farkas, verify_theory_conflict_with_farkas_full,
};
use ay_sat::{Literal, SolverContext};

use super::TheoryExtension;

fn dedup_conflict_terms(conflict_terms: &mut Vec<TheoryLit>) -> usize {
    let before = conflict_terms.len();
    let mut seen = ay_core::kani_compat::det_hash_set_with_capacity(before);
    conflict_terms.retain(|lit| seen.insert(*lit));
    before - conflict_terms.len()
}

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// #8008: Replay all deferred push/assert operations from BCP time.
    fn flush_deferred_trail(&mut self, ctx: &dyn SolverContext) {
        let trail = ctx.trail();
        let sat_level = ctx.decision_level();
        while self.theory_level < sat_level {
            self.level_trail_positions.push(self.last_trail_pos);
            self.theory.push();
            self.theory_level += 1;
        }
        let start = self.last_trail_pos;
        for &lit in &trail[start..] {
            let var = lit.variable();
            if self.is_theory_atom(var) {
                if let Some(&term) = self.var_to_term.get(&var.id()) {
                    let value = lit.is_positive();
                    self.theory.assert_literal(term, value);
                }
            } else {
                // #8373/#8003: Forward ITE condition assignments to theory.
                // Same logic as propagate_impl — see comment there.
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
                    }
                }
            }
        }
        self.last_trail_pos = trail.len();
    }

    /// Core logic for `Extension::check()`.
    ///
    /// Performs a final theory consistency check and translates the result into
    /// an `ExtCheckResult` that the SAT solver can act on (Sat, Conflict,
    /// AddClauses, Unknown).
    pub(super) fn check_impl(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        // #8008: Flush deferred trail before theory check.
        if self.full_trail_deferral_active {
            self.flush_deferred_trail(ctx);
        }

        // #8125 Phase 2: Selective ITE-deferred atom flush with fallback.
        //
        // Phase 1 flushed ALL deferred atoms before the final theory check,
        // losing the benefit of ITE relevancy filtering. Phase 2 re-checks
        // each deferred atom's guard status and partitions them:
        //   - Active-branch atoms: flushed immediately (guard now selects
        //     their branch, or guard is unassigned)
        //   - Inactive-branch atoms: held back for the initial theory check
        //
        // After the theory check:
        //   - If Sat: the inactive atoms were irrelevant. Record the count
        //     in `ite_deferred_kept` and return.
        //   - If non-Sat: flush all remaining atoms and re-check. The theory
        //     may need the inactive-branch atoms for completeness (the atom
        //     might participate in constraints outside the ITE context).
        // #uflia-deferred-atom-loss: entries are RETAINED after flushing (the
        // `flushed` flag dedups re-asserts) so that a later backjump — which
        // pops the theory scope holding the assert while SAT keeps the
        // assignment — can re-flush them instead of losing the atom forever.
        let has_inactive_deferred = if !self.ite_deferred_atoms.is_empty() {
            let mut deferred = std::mem::take(&mut self.ite_deferred_atoms);
            let mut inactive_count = 0usize;
            let mut flushed_count = 0u64;
            for entry in deferred.iter_mut() {
                let (term, value, _level, already_flushed) = *entry;
                if already_flushed {
                    continue;
                }
                let should_flush = if let Some(&sat_var_id) = self.term_to_var.get(&term) {
                    let var_id = sat_var_id as usize;
                    let is_ite_guarded = {
                        let word_idx = var_id / 64;
                        word_idx < self.ite_guarded_bitset.len()
                            && (self.ite_guarded_bitset[word_idx] >> (var_id % 64)) & 1 != 0
                    };
                    if is_ite_guarded {
                        let (cond_var_id, is_then_branch) = self.ite_branch_guards[var_id];
                        let cond_var = ay_sat::Variable::new(cond_var_id);
                        match ctx.value(cond_var) {
                            Some(cond_value) if cond_value != is_then_branch => {
                                // Guard still selects the other branch — defer.
                                false
                            }
                            _ => true,
                        }
                    } else {
                        true
                    }
                } else {
                    true
                };

                if should_flush {
                    self.theory.assert_literal(term, value);
                    entry.3 = true;
                    flushed_count += 1;
                } else {
                    inactive_count += 1;
                }
            }
            self.eager_stats.ite_deferred_flushed += flushed_count;
            self.ite_deferred_atoms = deferred;
            inactive_count > 0
        } else {
            false
        };

        // #5462: combined theories that override needs_final_check_after_sat()
        // defer split/model-equality results from their full check to the
        // post-SAT dispatch in the split-loop macro. Running the full check
        // here is needed for Unsat/UnsatWithFarkas conflict detection, but
        // NeedSplit/NeedModelEquality cannot be handled inside the SAT solve
        // (they'd be reported as Unknown, causing premature SAT termination).
        // For these, store in pending_split and return Sat so the SAT solver
        // hands back the model. The macro's post-SAT code handles the split.
        let needs_final = self.theory.needs_final_check_after_sat();

        let result = self.dispatch_theory_check(needs_final, ctx);

        // #8373: When inactive-branch atoms were held back, ALWAYS flush them
        // and re-check before accepting a Sat result. The deferred atoms may
        // participate in constraints outside their ITE context: an atom like
        // (= x_3 0.0) could appear in both an ITE branch and a standalone
        // assertion. Skipping it lets the theory return Sat even though the
        // full set of asserted atoms is UNSAT.
        //
        // Previously (#8125 Phase 2), Sat results trusted the deferral and
        // returned immediately. This caused false SAT on gasburner-prop3-2,
        // clocksynchro, and other QF_LRA benchmarks where the same arithmetic
        // atom appears in multiple assertion contexts.
        if has_inactive_deferred {
            // Flush all remaining deferred atoms and re-check unconditionally.
            // #uflia-deferred-atom-loss: entries stay in the list (flagged
            // flushed) so a post-backjump re-check can restore them.
            let mut remaining = std::mem::take(&mut self.ite_deferred_atoms);
            let mut flushed_count = 0u64;
            for entry in remaining.iter_mut() {
                if !entry.3 {
                    self.theory.assert_literal(entry.0, entry.1);
                    entry.3 = true;
                    flushed_count += 1;
                }
            }
            self.eager_stats.ite_deferred_flushed += flushed_count;
            self.ite_deferred_atoms = remaining;
            return self.dispatch_theory_check(needs_final, ctx);
        }

        result
    }

    /// Run theory.check() and dispatch the result.
    ///
    /// Extracted to allow the Phase 2 ITE two-pass strategy: first check
    /// without inactive-branch atoms, then retry with all atoms if needed.
    fn dispatch_theory_check(
        &mut self,
        needs_final: bool,
        ctx: &dyn SolverContext,
    ) -> ExtCheckResult {
        match self.theory.check() {
            TheoryResult::Sat => {
                // The theory is satisfied under the current complete assignment.
                // Clear stale pending single-var splits (#6303), but preserve
                // NeedExpressionSplit (#6586, parity with propagate() #4919).
                //
                // Multi-var disequalities (x != y) require expression split atoms
                // (x-y > 0 OR x-y < 0) to be enforced. The LRA theory returns
                // Sat here because it only checks arithmetic constraints — it
                // does not natively enforce disequalities. If we clear the
                // NeedExpressionSplit, the pipeline returns Sat without ever
                // creating the split atoms, producing an unsound result.
                //
                // For single-var splits (NeedSplit, NeedDisequalitySplit), Sat
                // from the final check means the split was resolved or is no
                // longer needed, so clearing is correct.
                //
                // Oscillation prevention: the pipeline's split clause dedup
                // (added_split_clauses HashSet) prevents re-adding the same
                // split clause, and max_splits bounds iteration count.
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
                self.record_pending_bound_refinements(refinements);
                ExtCheckResult::Sat
            }
            TheoryResult::Unknown => {
                tracing::warn!(
                    needs_final,
                    theory_type = std::any::type_name::<T>(),
                    "dispatch_theory_check got TheoryResult::Unknown"
                );
                self.pending_bound_refinements.clear();
                ExtCheckResult::Unknown
            }
            // #6546 Packet 5: inline NeedLemmas in check() — convert to
            // AddClauses so the SAT solver adds the theory lemmas and
            // continues solving instead of returning to the split loop.
            //
            // #8319: AY_NO_INLINE_LEMMAS disables this path, reverting to
            // the pending_split fallback.
            TheoryResult::NeedLemmas(lemmas) if crate::theory_debug_flags::no_inline_lemmas() => {
                self.pending_split = Some(TheoryResult::NeedLemmas(lemmas));
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::NeedLemmas(lemmas) => self.handle_check_need_lemmas(lemmas, needs_final),
            TheoryResult::NeedExpressionSplit(split) => {
                if self
                    .processed_expr_splits
                    .is_some_and(|s| s.contains(&split.disequality_term))
                {
                    return ExtCheckResult::Sat;
                }
                self.pending_split = Some(TheoryResult::NeedExpressionSplit(split));
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::NeedExpressionSplits(splits) => {
                // #8707/#8751/#8762: Batch variant from LRA's disequality-check pass
                // (port of Z3's mutate_assignment). Filter out already-processed
                // splits and keep only fresh ones. If all are stale, treat as SAT;
                // if one remains, demote to the singleton variant; otherwise pass
                // the batch through via pending_split so the split-loop macros
                // can encode each. Mirrors propagate.rs:593.
                let fresh: Vec<_> = if let Some(processed) = self.processed_expr_splits {
                    splits
                        .into_iter()
                        .filter(|s| !processed.contains(&s.disequality_term))
                        .collect()
                } else {
                    splits
                };
                if fresh.is_empty() {
                    return ExtCheckResult::Sat;
                }
                self.pending_split = if fresh.len() == 1 {
                    let mut iter = fresh.into_iter();
                    Some(TheoryResult::NeedExpressionSplit(
                        iter.next().expect("fresh is non-empty"),
                    ))
                } else {
                    Some(TheoryResult::NeedExpressionSplits(fresh))
                };
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::NeedModelEquality(eq) => {
                if self.model_equality_already_encoded(&eq) {
                    return ExtCheckResult::Sat;
                }
                self.pending_split = Some(TheoryResult::NeedModelEquality(eq));
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::NeedModelEqualities(eqs) => {
                let Some(check_result) = self.filter_stale_model_equalities(eqs) else {
                    return ExtCheckResult::Sat;
                };
                self.pending_split = Some(check_result);
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            check_result @ TheoryResult::NeedSplit(_)
            | check_result @ TheoryResult::NeedDisequalitySplit(_)
            | check_result @ TheoryResult::NeedStringLemma(_) => {
                self.pending_split = Some(check_result);
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::Unsat(conflict_terms) => self.handle_check_unsat(conflict_terms, ctx),
            TheoryResult::UnsatWithFarkas(conflict) => {
                self.handle_check_unsat_with_farkas(conflict, ctx)
            }
            // All current TheoryResult variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TheoryResult variant in check(): {other:?}"),
        }
    }

    /// Handle `NeedLemmas` in `check()` — convert to `AddClauses`.
    fn handle_check_need_lemmas(
        &mut self,
        lemmas: Vec<ay_core::TheoryLemma>,
        needs_final: bool,
    ) -> ExtCheckResult {
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
            self.eager_stats.inline_lemma_clauses += sat_clauses.len() as u64;
            // Record proof entries for inline lemmas.
            // #trust->0 C1.iii: route through the classifier funnel (with the
            // polarity-before-routing contract) instead of recording bare
            // Generic/trust — this site had the same mechanics as its
            // propagate() sibling but never ran the funnel (site 15).
            if let Some(ref mut proof_ctx) = self.proof {
                for lemma in &lemmas {
                    let _ = crate::theory_inference::record_materialized_lemma_clause(
                        proof_ctx.tracker,
                        self.terms,
                        proof_ctx.negations,
                        &lemma.clause,
                    );
                }
            }
            ExtCheckResult::AddClauses(sat_clauses)
        } else {
            // Fallback: some terms missing from SAT — use pending_split.
            self.pending_split = Some(TheoryResult::NeedLemmas(lemmas));
            self.pending_bound_refinements.clear();
            if needs_final {
                ExtCheckResult::Sat
            } else {
                ExtCheckResult::Unknown
            }
        }
    }

    /// Handle `Unsat` conflict from theory check.
    fn handle_check_unsat(
        &mut self,
        mut conflict_terms: Vec<TheoryLit>,
        ctx: &dyn SolverContext,
    ) -> ExtCheckResult {
        let duplicate_count = dedup_conflict_terms(&mut conflict_terms);
        if duplicate_count > 0 {
            tracing::warn!(
                duplicate_count,
                conflict_len = conflict_terms.len(),
                "theory conflict contained duplicate literals; deduplicated before SAT clause mapping"
            );
        }

        // Conflict verification gate (fail-closed).
        //
        // A theory conflict that fails structural, EUF, or domain-aware
        // semantic verification must NOT be learned as a global clause — the
        // solve degrades to Unknown. This mirrors the eager `propagate()` Unsat
        // path (the sibling in this module) and the landed pipeline fixes
        // (6b7a57f921 / 472d9c23df): the former #8595 "use conflict anyway"
        // arms here laundered unverifiable theory conflicts into wrong UNSAT
        // verdicts. Verifiable-domain skips inside `verify_conflict_semantic`
        // (nonlinear, LIRA int/real mix, unsupported/unknown domains,
        // contradictory-literal tautologies) return Ok, so only genuine
        // spurious-conflict verdicts reach the bail.
        log_conflict_debug(&conflict_terms, "check() UNSAT");
        let mut conflict_verified = true;
        // Structural verification (#3175).
        if let Err(e) = verify_theory_conflict(&conflict_terms) {
            conflict_verified = false;
            tracing::warn!(
                error = %e,
                conflict_len = conflict_terms.len(),
                "BUG(#4666): theory conflict structural verification failed in check(); escalating to Unknown"
            );
        }
        // EUF semantic re-check (#4704): for theories that support it,
        // verify via congruence closure. Catches invalid EUF conflicts
        // that the domain-aware check misclassifies as Arithmetic (Int
        // variable equalities) and accepts optimistically.
        let mut euf_prechecked = false;
        if self.theory.supports_euf_semantic_check() {
            if let Some(terms) = self.terms {
                // Threads the combined conflict-verification support set
                // (`self.support_axioms`, forwarded from DpllT's dt tautologies
                // ++ unconditional-Forall ground instances at construction).
                // Every element is true in every model of the problem, so it can
                // only CONFIRM a genuine conflict, never launder a spurious one;
                // empty for quantifier-free / non-datatype problems (#8123,
                // #AUFLIA-support).
                euf_prechecked = true;
                if let Err(e) = verify_euf_conflict(&conflict_terms, terms, &self.support_axioms) {
                    conflict_verified = false;
                    tracing::warn!(
                        theory = std::any::type_name::<T>(),
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        "BUG(#4704): EUF semantic verification failed in check(); escalating to Unknown"
                    );
                }
            }
        }
        // Domain-aware semantic re-check (#6242, #8123):
        // verify_conflict_semantic dispatches to the correct verifier for
        // each domain (EUF, LRA/LIA, or Nelson-Oppen combined solver for
        // mixed). Fail-closed, in parity with the eager `propagate()` Unsat
        // path: any verification error means the conflict cannot be trusted, so
        // it is not learned and the solve degrades to Unknown. The string
        // `ConflictIsSat` case (incomplete-reason word conflict) is subsumed —
        // it is one of the errors this gate now rejects unconditionally.
        //
        // SOLE CARVE-OUT — array-context `ConflictIsSat`: the isolated
        // verification combiner runs `verify_only` without the eager
        // ROW1/ROW2 + extensionality lemma preprocessing the production array
        // solver drives, so it reports `Sat` on VALID array-extensionality
        // conflicts (store-commutativity). That verdict is a KNOWN false
        // positive, not a spuriousness proof, so we accept optimistically —
        // the same known-incomplete-verifier treatment the nonlinear (#7978)
        // and LIRA (#6853) skips already apply inside verify_conflict_semantic.
        // This carve-out is deliberately scoped to the eager path: the SHARED
        // verifier still rejects array `ConflictIsSat`, so the fail-closed
        // pipeline gates (6b7a57f921 / 472d9c23df) keep catching genuinely-
        // spurious ROW-verifiable array conflicts. (#store-commutativity)
        if let Some(terms) = self.terms {
            // PEQ perf: skip the byte-identical Euf-domain duplicate re-solve
            // when the direct EUF re-check above already ran (same rationale
            // as the eager propagate() sibling; gate strength unchanged).
            // #uflia-verify-memo: routed through the Executor memo — a
            // literal set already proven jointly UNSAT this query skips the
            // fresh-combiner re-solve; failures always re-verify in full.
            let semantic_result =
                self.verify_conflict_semantic_memo(&conflict_terms, terms, euf_prechecked);
            if let Err(e) = semantic_result {
                if matches!(e, crate::verification::VerificationError::ConflictIsSat)
                    && conflict_has_array_context(terms, &conflict_terms)
                {
                    tracing::debug!(
                        conflict_len = conflict_terms.len(),
                        "check() Unsat: array-context conflict semantic re-verification returned \
                         Sat — a known false positive of the extensionality-incomplete isolated \
                         combiner; accepting conflict optimistically (#store-commutativity)"
                    );
                } else {
                    conflict_verified = false;
                    tracing::warn!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        "BUG(#8123): semantic conflict verification failed in check() Unsat path; escalating to Unknown"
                    );
                    if ay_core::misc_cli_flags().debug_split_exit {
                        for lit in &conflict_terms {
                            safe_eprintln!(
                                "[conflict-probe] {:?}={} :: {}",
                                lit.term,
                                lit.value,
                                super::types::format_term_recursive(terms, lit.term, 8)
                                    .chars()
                                    .take(180)
                                    .collect::<String>()
                            );
                        }
                    }
                }
            }
        }
        if !conflict_verified {
            // Fail-closed RECOVERY (#euf-conflict-rederive): the theory's own
            // conflict failed verification (its incremental explain() can emit
            // an under-justified reason set once the e-graph has collapsed past
            // the first inconsistency — observed on QF_UF NEQ finite-model
            // instances). The FULL trail may still be genuinely theory-unsat,
            // so before degrading the whole solve to Unknown, re-derive a
            // conflict from a FRESH EufSolver over the complete assignment and
            // run it through the SAME verification gates. Only a conflict that
            // passes every gate is learned; anything else keeps the fail-closed
            // Unknown. This never weakens the gate — it replaces an
            // unverifiable clause with an independently verified one.
            if self.theory.supports_euf_semantic_check() {
                if let Some(terms) = self.terms {
                    use ay_core::TheorySolver as _;
                    let mut fresh = ay_euf::EufSolver::new(terms);
                    for l in ctx.trail() {
                        if let Some(&t) = self.var_to_term.get(&l.variable().id()) {
                            fresh.assert_literal(t, l.is_positive());
                        }
                    }
                    if let TheoryResult::Unsat(mut re_conflict) = fresh.check() {
                        dedup_conflict_terms(&mut re_conflict);
                        // (Euf-domain duplicate skipped: verify_euf_conflict
                        // just ran on this exact conflict; other domains still
                        // verify via the dispatcher.)
                        let re_verified = verify_theory_conflict(&re_conflict).is_ok()
                            && verify_euf_conflict(&re_conflict, terms, &self.support_axioms)
                                .is_ok()
                            && crate::verification::verify_conflict_semantic_euf_prechecked(
                                &re_conflict,
                                terms,
                                &self.support_axioms,
                            )
                            .is_ok();
                        if re_verified {
                            tracing::warn!(
                                original_len = conflict_terms.len(),
                                rederived_len = re_conflict.len(),
                                "check() Unsat: unverifiable theory conflict replaced by \
                                 fresh-solver re-derived conflict that passes all gates \
                                 (#euf-conflict-rederive)"
                            );
                            conflict_terms = re_conflict;
                            conflict_verified = true;
                        }
                    }
                }
            }
            if !conflict_verified {
                return ExtCheckResult::Unknown;
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
        if let Some(terms) = self.terms {
            let euf_removed =
                crate::theory_inference::minimize_euf_conflict(&mut conflict_terms, terms);
            self.eager_stats.theory_minimize_lits_removed += euf_removed as u64;
        }

        let mut clause: Vec<Literal> = conflict_terms
            .iter()
            .filter_map(|t| self.term_to_literal(t.term, !t.value))
            .collect();

        // #6846: mid-search variable minting.
        //
        // A theory conflict can name a term the pre-solve encoding never gave a
        // SAT variable — most often an N-O model equality the combiner only
        // discovers once the search is under way. `term_to_literal` drops those
        // silently, the clause comes back short, and the guard below fails closed
        // to `Unknown`. That is sound but incomplete, and it is the stated reason
        // AUFLIA is pinned to the lazy pipeline (`combined/mod.rs` #6846: "the
        // eager extension drops theory conflicts when model equality terms lack
        // SAT variable mappings ... causing Unknown on ... add5, add6, read7").
        //
        // Name the missing terms instead. The clause is the negation of a
        // theory-inconsistent conjunction, i.e. T-VALID, so it is a legitimate
        // theory lemma. It is returned as `AddClauses`, NOT `Conflict`: a freshly
        // minted variable is unassigned, so the clause is not falsified by the
        // current assignment and could not drive conflict analysis. The
        // `AddClauses` path backtracks to level 0 before adding
        // (`theory_backend.rs` #8480), which is exactly the state where a clause
        // over new variables is well-formed, and then re-enters the search.
        if clause.len() < conflict_terms.len() && mint_theory_vars_enabled() {
            let missing: Vec<(ay_core::term::TermId, bool)> = conflict_terms
                .iter()
                .filter(|t| self.var_for_term(t.term).is_none())
                .map(|t| (t.term, !t.value))
                .collect();
            let mut minted_all = true;
            for (term, _) in &missing {
                if self.mint_var_for_term(*term, ctx).is_none() {
                    minted_all = false;
                    break;
                }
            }
            if minted_all {
                let full: Vec<Literal> = conflict_terms
                    .iter()
                    .filter_map(|t| self.term_to_literal(t.term, !t.value))
                    .collect();
                if full.len() == conflict_terms.len() {
                    tracing::debug!(
                        minted = missing.len(),
                        lits = full.len(),
                        "#6846: minted SAT variables for an otherwise-partial theory conflict"
                    );
                    self.theory_conflict_count += 1;
                    return ExtCheckResult::AddClauses(vec![full]);
                }
            }
        }

        // Soundness guard (#3826): partial/empty clause → Unknown.
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
                "BUG(#4666): theory conflict mapped to partial clause in check()"
            );
            ExtCheckResult::Unknown
        } else {
            self.minimize_context_conflict(&conflict_terms, &mut clause, ctx);
            self.theory_conflict_count += 1;
            ExtCheckResult::Conflict(clause)
        }
    }

    /// Handle `UnsatWithFarkas` conflict from theory check.
    fn handle_check_unsat_with_farkas(
        &mut self,
        mut conflict: ay_core::TheoryConflict,
        ctx: &dyn SolverContext,
    ) -> ExtCheckResult {
        // #4666: dedupe exact-duplicate literals, merging positional Farkas
        // coefficients by sum (λ₁·c + λ₂·c = (λ₁+λ₂)·c) — logical identity,
        // keeps the certificate aligned (parity with handle_check_unsat's
        // dedup_conflict_terms).
        crate::verification::dedup_conflict_with_farkas(&mut conflict);
        // Structural Farkas verification (#3175)
        log_conflict_debug(&conflict.literals, "check() UnsatWithFarkas");
        let mut farkas_valid = true;
        if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
            if e.is_missing_annotation() {
                // Missing Farkas annotation (#6535): conflict is sound but
                // proof certificate cannot be recorded.
                tracing::debug!(
                    conflict_len = conflict.literals.len(),
                    "Farkas annotation missing in check(); conflict clause is sound, skipping proof cert"
                );
            } else {
                // Certificate downgrade: the Farkas certificate is unusable, so
                // drop it. The conflict itself is re-verified by the fail-closed
                // semantic backstop below and is only learned if that succeeds
                // (no more fail-open "use anyway" path).
                tracing::warn!(
                    error = %e,
                    conflict_len = conflict.literals.len(),
                    "BUG(#4666): Farkas structural verification failed in check(); dropping certificate, deferring to semantic backstop"
                );
            }
            farkas_valid = false;
        }
        // Semantic Farkas verification (#4515). Runs in ALL builds
        // (adversarial-review followup on #rank-4 increment 2; was debug-only
        // per W16-5): the certificate is this arm's strongest verdict check —
        // the verify_conflict_semantic call below stays a soft gate (#8123).
        if farkas_valid && self.theory.supports_farkas_semantic_check() {
            if let Some(terms) = self.terms {
                if let Err(e) = verify_theory_conflict_with_farkas_full(&conflict, terms) {
                    // Certificate downgrade: semantically invalid certificate.
                    // Drop it and defer to the fail-closed semantic backstop
                    // below, which only learns the conflict if it verifies.
                    tracing::warn!(
                        error = %e,
                        conflict_len = conflict.literals.len(),
                        "BUG(#4666): Farkas semantic verification failed in check(); dropping certificate, deferring to semantic backstop"
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

        // Domain-aware semantic re-check (#6242, #8123): the fail-closed
        // backstop. verify_conflict_semantic dispatches to the correct verifier
        // for each domain; a conflict that cannot be verified is not learned and
        // the solve degrades to Unknown, in parity with the eager `propagate()`
        // Farkas path and the landed pipeline fixes. Verifiable-domain skips
        // inside verify_conflict_semantic return Ok, so a valid certificate-less
        // conflict (e.g. GCD-infeasibility) still passes here and stays
        // learnable; only genuine spurious-conflict verdicts reach the bail (the
        // string `ConflictIsSat` incomplete-reason case is one of them).
        //
        // Array-context `ConflictIsSat` is the sole carve-out — see the Unsat
        // arm above: the extensionality-incomplete isolated combiner's `Sat`
        // verdict on a valid array conflict is a known false positive, accepted
        // optimistically here while the shared verifier keeps the pipeline
        // gates fail-closed. (#store-commutativity)
        if let Some(terms) = self.terms {
            // #uflia-verify-memo: memoized (trust-true-only) — failures
            // always re-verify in full, preserving the `ConflictIsSat`
            // array-context carve-out below byte-identically.
            if let Err(e) = self.verify_conflict_semantic_memo(&conflict.literals, terms, false) {
                if matches!(e, crate::verification::VerificationError::ConflictIsSat)
                    && conflict_has_array_context(terms, &conflict.literals)
                {
                    tracing::debug!(
                        conflict_len = conflict.literals.len(),
                        "check() Farkas: array-context conflict semantic re-verification returned \
                         Sat — a known false positive of the extensionality-incomplete isolated \
                         combiner; accepting conflict optimistically (#store-commutativity)"
                    );
                } else {
                    tracing::warn!(
                        error = %e,
                        conflict_len = conflict.literals.len(),
                        "BUG(#8123): semantic conflict verification failed in check() Farkas path; escalating to Unknown"
                    );
                    return ExtCheckResult::Unknown;
                }
            }
        }

        // The conflict passed semantic verification. Even when the Farkas
        // certificate was dropped as invalid, the conflict literals are correct
        // (re-verified above) — use them (#5534).
        let mut clause: Vec<Literal> = conflict
            .literals
            .iter()
            .filter_map(|t| self.term_to_literal(t.term, !t.value))
            .collect();
        // Soundness guard (#3826): partial/empty clause → Unknown.
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
                "BUG(#4666): Farkas conflict mapped to partial clause in check()"
            );
            ExtCheckResult::Unknown
        } else {
            // #8424: Pre-minimize Farkas conflict clause, then level-0 removal.
            let mut removed = if let Some(ref farkas) = conflict.farkas {
                let mut coeffs = farkas.coefficients.clone();
                crate::theory_inference::minimize_farkas_conflict(&mut clause, &mut coeffs)
            } else {
                0
            };
            // Level-0 removal applies to both Farkas and non-Farkas paths.
            removed += crate::theory_inference::minimize_conflict_with_levels(&mut clause, |var| {
                ctx.var_level(var)
            });
            self.eager_stats.theory_minimize_lits_removed += removed as u64;
            self.theory_conflict_count += 1;
            ExtCheckResult::Conflict(clause)
        }
    }
}

/// #6846 kill switch: mid-search SAT-variable minting for theory conflicts.
///
/// Default OFF. Minting changes a fail-closed `Unknown` into an added T-valid
/// lemma, which is a real behaviour change on every eager route, so it stays
/// opt-in until its ablation is done.
pub(super) fn mint_theory_vars_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| ay_core::misc_cli_flags().dpll_mint_theory_vars)
}
