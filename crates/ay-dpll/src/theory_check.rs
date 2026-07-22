// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory consistency checking for `DpllT`.
//!
//! Contains `check_theory_core`, the central theory-check method that handles
//! propagation, conflict detection, Farkas certificate verification, and
//! proof-tracking integration. Extracted from `lib.rs` as part of #6860.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;

use ay_core::{term::TermData, TermId, TheoryResult, TheorySolver};
use ay_sat::Literal;

use crate::verification::{
    self, verify_conflict_semantic, verify_propagation_semantic, verify_theory_conflict,
    verify_theory_conflict_with_farkas, verify_theory_conflict_with_farkas_full,
    verify_theory_propagation,
};
use crate::{proof_tracker, theory_inference, DpllT, TheoryCheck};

impl<T: TheorySolver> DpllT<'_, T> {
    /// Check theory consistency and handle propagations/conflicts
    ///
    /// DPLL(T) Integration:
    /// When the theory propagates a literal L with reason {R1, R2, ...}, we add
    /// the clause (-R1 ∨ -R2 ∨ ... ∨ L) to the SAT solver. This enables SAT-level
    /// unit propagation to prune the search space using theory deductions.
    ///
    /// Without this, ay would explore exponentially more branches on benchmarks
    /// like eq_diamond where transitivity propagations are critical.
    pub(crate) fn check_theory(&mut self) -> TheoryCheck {
        self.check_theory_core(None)
    }

    /// Core theory check logic used by `check_theory` and the proof-tracking solve loop.
    ///
    /// When `tracking` is `Some`, records theory conflict steps into the proof tracker.
    pub(crate) fn check_theory_core(
        &mut self,
        mut tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> TheoryCheck {
        let debug = self.debug_dpll;
        let label = if tracking.is_some() {
            "check_theory_with_proof_tracking"
        } else {
            "check_theory"
        };
        // Build the combined conflict-verification support set ONCE (dt
        // tautologies ++ unconditional-Forall ground instances). Both sources
        // are true in every model of the problem, so asserting them in the fresh
        // verifier can only CONFIRM a genuine conflict, never launder a spurious
        // one. Empty for quantifier-free / non-datatype problems (byte-identical
        // to the prior `&self.dt_verification_axioms`-only behavior).
        let support_axioms = self.combined_support_axioms();

        // First check for propagations and add them to SAT solver
        let has_diag = self.diagnostic_trace.is_some();
        let propagate_start = has_diag.then(Instant::now);
        let propagations = self.theory.propagate();
        let propagate_duration = propagate_start.map(|s| s.elapsed());
        let mut clauses_added = 0;

        for prop in propagations {
            // Verify propagation structure (#4346)
            verification::log_propagation_debug(&prop, label);
            if let Err(e) = verify_theory_propagation(&prop) {
                // Production soundness gate: theory returned an invalid
                // propagation. Skip it rather than injecting a bad literal
                // into the DPLL trail, which would lead to unsound results.
                safe_eprintln!(
                    "BUG: Theory returned invalid propagation in {label}: {e}\n\
                     Propagated: {:?}={}\nReason: {:?}",
                    prop.literal.term,
                    prop.literal.value,
                    prop.reason
                );
                tracing::warn!("skipping invalid theory propagation in {label}: {e}");
                continue;
            }

            // #8529: Promoted to all builds. This is a soundness gate: without
            // it, implied-bound propagations with incorrect reasons cause false
            // SAT on QF_LRA benchmarks (synched.base.smt2). The cost is one
            // try_algebraic_verify() call per propagation (fast path, ~O(1) for
            // single-variable bounds) plus one fresh LRA solver creation per
            // propagation that fails the algebraic fast path. On synched.base
            // (719 propagations, 133-line formula), the overhead is ~50ms.
            //
            // Previously #8782 demoted this to debug-only, but that introduced
            // false SAT bugs in release builds.
            if let Some(terms) = self.terms {
                const SEMANTIC_VERIFY_TERM_LIMIT: usize = 50_000;
                if terms.len() <= SEMANTIC_VERIFY_TERM_LIMIT {
                    if let Err(e) = verify_propagation_semantic(&prop, terms) {
                        tracing::error!(
                            label,
                            error = %e,
                            term = ?prop.literal.term,
                            value = prop.literal.value,
                            reason_count = prop.reason.len(),
                            "BUG(#6242): propagation semantic verification failed; skipping unsound propagation"
                        );
                        continue;
                    }
                } else {
                    tracing::debug!(
                        term_count = terms.len(),
                        limit = SEMANTIC_VERIFY_TERM_LIMIT,
                        "semantic propagation verification skipped: term count exceeds budget (#8558)"
                    );
                }
            }

            {
                // #6546: dynamically register unmapped theory terms so propagation
                // clauses are never dropped as partial.
                let lit = self.term_to_literal_or_register(prop.literal.term, prop.literal.value);
                // Check if this conflicts with current assignment
                if let Some(var) = self.var_for_term(prop.literal.term) {
                    if let Some(value) = self.sat.value(var) {
                        if value != prop.literal.value {
                            // Theory propagated a value but SAT assigned the opposite.
                            // Batch the conflict as a clause (#6546): instead of returning
                            // immediately on the first conflict, collect ALL conflicts so
                            // the SAT solver learns multiple clauses per restart.
                            // #6546: use dynamic registration to avoid partial
                            // clause drops. Array theory terms generated during
                            // check() may not be in term_to_var yet.
                            let mut conflict: Vec<Literal> = prop
                                .reason
                                .iter()
                                .map(|r| self.term_to_literal_or_register(r.term, !r.value))
                                .collect();
                            // Soundness guard (#3826): partial clause check.
                            if conflict.len() < prop.reason.len() {
                                self.partial_clause_count += 1;
                                crate::combined_solvers::theory_stats::inc_partial_clauses();
                                if self.partial_clause_count >= 100 {
                                    tracing::error!(
                                        count = self.partial_clause_count,
                                        "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                                    );
                                }
                                self.theory_unknown_count += 1;
                                self.emit_theory_check_event(
                                    "propagate",
                                    "unknown",
                                    None,
                                    None,
                                    propagate_duration,
                                );
                                return TheoryCheck::Unknown;
                            }
                            conflict.push(lit);
                            if debug {
                                safe_eprintln!(
                                    "[DPLL] Theory propagation conflict: {} literals",
                                    conflict.len()
                                );
                            }
                            self.emit_theory_check_event(
                                "propagate",
                                "conflict",
                                None,
                                Some(conflict.len()),
                                propagate_duration,
                            );
                            return TheoryCheck::Conflict(conflict);
                        }
                        // Already assigned to the correct value - no clause needed
                        continue;
                    }
                }

                // Literal is not yet assigned - add propagation clause
                // Clause: (¬reason1 ∨ ¬reason2 ∨ ... ∨ propagated_lit)
                // #6546: use dynamic registration to avoid partial clause drops.
                let mut clause: Vec<Literal> = prop
                    .reason
                    .iter()
                    .map(|r| self.term_to_literal_or_register(r.term, !r.value))
                    .collect();
                clause.push(lit);

                if debug {
                    safe_eprintln!(
                        "[DPLL] Adding theory propagation clause: {} literals (propagates {})",
                        clause.len(),
                        if lit.is_positive() { "true" } else { "false" }
                    );
                }

                self.sat.add_clause(clause);
                clauses_added += 1;
            }
        }

        // If we added propagation clauses, signal to re-solve
        if clauses_added > 0 {
            if debug {
                safe_eprintln!("[DPLL] Added {} theory propagation clauses", clauses_added);
            }
            self.emit_theory_check_event(
                "propagate",
                "propagated",
                Some(clauses_added),
                None,
                propagate_duration,
            );
            return TheoryCheck::Propagated(clauses_added);
        }

        self.emit_theory_check_event("propagate", "none", Some(0), None, propagate_duration);

        // Then check consistency (BCP-time hook for combined solvers)
        let check_start = has_diag.then(Instant::now);
        let consistency_result = self.theory.check_during_propagate();
        let consistency_duration = check_start.map(|s| s.elapsed());
        match consistency_result {
            TheoryResult::Sat => {
                self.emit_theory_check_event(
                    "consistency",
                    "sat",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::Sat
            }
            TheoryResult::Unknown => {
                self.theory_unknown_count += 1;
                self.emit_theory_check_event(
                    "consistency",
                    "unknown",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::Unknown
            }
            TheoryResult::NeedSplit(split) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_split",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedSplit(split)
            }
            TheoryResult::NeedDisequalitySplit(split) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_disequality_split",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedDisequalitySplit(split)
            }
            TheoryResult::NeedExpressionSplit(split) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_expression_split",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedExpressionSplit(split)
            }
            TheoryResult::NeedExpressionSplits(splits) => {
                let Some(split) = splits.into_iter().next() else {
                    self.theory_unknown_count += 1;
                    self.emit_theory_check_event(
                        "consistency",
                        "unknown",
                        None,
                        None,
                        consistency_duration,
                    );
                    return TheoryCheck::Unknown;
                };
                self.emit_theory_check_event(
                    "consistency",
                    "need_expression_split",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedExpressionSplit(split)
            }
            TheoryResult::NeedStringLemma(lemma) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_string_lemma",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedStringLemma(lemma)
            }
            TheoryResult::NeedLemmas(lemmas) => {
                if let Some((ref mut tracker, negations)) = tracking {
                    for lemma in &lemmas {
                        let terms = self
                            .theory_clause_to_terms(&lemma.clause, negations)
                            .unwrap_or_else(|| lemma.clause.iter().map(|lit| lit.term).collect());
                        let _ = tracker.add_theory_lemma(terms);
                    }
                }
                self.emit_theory_check_event(
                    "consistency",
                    "need_lemmas",
                    Some(lemmas.len()),
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedLemmas(lemmas)
            }
            TheoryResult::NeedModelEquality(eq) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_model_equality",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedModelEquality(eq)
            }
            TheoryResult::NeedModelEqualities(eqs) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_model_equalities",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedModelEqualities(eqs)
            }
            TheoryResult::Unsat(mut conflict_terms) => {
                // #4666: exact-duplicate literals are a logical identity in a
                // conflict (X ∨ X ≡ X in the learned clause) but structurally
                // fail verification below, which degrades this check to
                // TheoryCheck::Unknown WITHOUT learning a blocking clause — the
                // theory then re-derives the identical conflict (observed
                // thousands of times on verification-consumer VCs). Dedupe before verifying.
                verification::dedup_conflict_literals(&mut conflict_terms);
                // Temporary debug: print conflict terms for #3826 diagnosis.
                if debug {
                    safe_eprintln!(
                        "[DPLL] Theory UNSAT conflict: {} terms",
                        conflict_terms.len()
                    );
                    for (i, lit) in conflict_terms.iter().enumerate() {
                        if let Some(terms) = self.terms {
                            safe_eprintln!(
                                "[DPLL]   conflict[{}]: term={:?} value={} kind={:?}",
                                i,
                                lit.term,
                                lit.value,
                                terms.get(lit.term)
                            );
                            // Deep print: show sub-terms for equality atoms
                            if let TermData::App(_, args) = terms.get(lit.term) {
                                for &arg in args.iter() {
                                    safe_eprintln!(
                                        "[DPLL]     sub {:?}: {:?}",
                                        arg,
                                        terms.get(arg)
                                    );
                                    if let TermData::App(_, sub_args) = terms.get(arg) {
                                        for &sa in sub_args.iter() {
                                            safe_eprintln!(
                                                "[DPLL]       sub {:?}: {:?}",
                                                sa,
                                                terms.get(sa)
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // Structural verification in all builds (#3175)
                verification::log_conflict_debug(
                    &conflict_terms,
                    if label == "check_theory" {
                        "DpllT::check_theory Unsat"
                    } else {
                        "DpllT::check_theory_with_proof_tracking Unsat"
                    },
                );
                if let Err(e) = verify_theory_conflict(&conflict_terms) {
                    tracing::error!(
                        context = label,
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        conflict = ?conflict_terms,
                        "BUG: theory conflict verification failed; returning Unknown"
                    );
                    self.theory_unknown_count += 1;
                    self.emit_theory_check_event(
                        "consistency",
                        "unknown",
                        None,
                        Some(conflict_terms.len()),
                        consistency_duration,
                    );
                    return TheoryCheck::Unknown;
                }
                // Domain-aware semantic re-check (#4704, #4912, #8123):
                // verify_conflict_semantic dispatches to the appropriate
                // verifier for each domain (EUF, LIA/LRA, or Nelson-Oppen
                // combined solver for mixed-domain conflicts). This replaces
                // the EUF-only check that previously let mixed-domain
                // conflicts bypass semantic verification.
                // Budget guard skips for large term stores.
                if let Some(terms) = self.terms {
                    const SEMANTIC_VERIFY_TERM_LIMIT: usize = 50_000;
                    if terms.len() <= SEMANTIC_VERIFY_TERM_LIMIT {
                        if let Err(e) =
                            verify_conflict_semantic(&conflict_terms, terms, &support_axioms)
                        {
                            tracing::error!(
                                context = label,
                                error = %e,
                                conflict_len = conflict_terms.len(),
                                "BUG(#8123): semantic conflict verification failed in theory_check Unsat path; returning Unknown"
                            );
                            self.emit_theory_check_event(
                                "consistency",
                                "unknown",
                                None,
                                Some(conflict_terms.len()),
                                consistency_duration,
                            );
                            return TheoryCheck::Unknown;
                        }
                    } else {
                        tracing::debug!(
                            term_count = terms.len(),
                            limit = SEMANTIC_VERIFY_TERM_LIMIT,
                            conflict_len = conflict_terms.len(),
                            "semantic conflict verification skipped: term count exceeds budget (#8558)"
                        );
                    }
                }
                if let Some((ref mut tracker, negations)) = tracking {
                    theory_inference::record_theory_conflict_unsat(
                        tracker,
                        self.terms,
                        negations,
                        &conflict_terms,
                    );
                }
                // #8424: EUF chain minimization at the theory level (before
                // SAT literal conversion). Removes redundant equality premises
                // that are not on the shortest BFS chain.
                let mut conflict_terms = conflict_terms;
                if let Some(terms) = self.terms {
                    let euf_removed =
                        theory_inference::minimize_euf_conflict(&mut conflict_terms, terms);
                    self.theory_minimize_lits_removed += euf_removed as u64;
                }
                // #6546: dynamically register unmapped terms so conflict clauses
                // are never dropped as partial.
                let mut clause: Vec<Literal> = conflict_terms
                    .iter()
                    .map(|t| self.term_to_literal_or_register(t.term, !t.value))
                    .collect();
                {
                    // #8424: Pre-minimize conflict clause with level-0 removal.
                    let removed =
                        theory_inference::minimize_conflict_with_levels(&mut clause, |var| {
                            self.sat.var_level(var)
                        });
                    self.theory_minimize_lits_removed += removed as u64;
                    // #8165: Track conflict clause literal counts.
                    let clause_len = clause.len() as u64;
                    self.conflict_total_literals += clause_len;
                    if clause_len > self.conflict_max_literals {
                        self.conflict_max_literals = clause_len;
                    }
                    self.emit_theory_check_event(
                        "consistency",
                        "conflict",
                        None,
                        Some(clause.len()),
                        consistency_duration,
                    );
                    TheoryCheck::Conflict(clause)
                }
            }
            TheoryResult::UnsatWithFarkas(mut conflict) => {
                // #4666: dedupe exact-duplicate literals, merging positional
                // Farkas coefficients by sum (λ₁·c + λ₂·c = (λ₁+λ₂)·c) —
                // logical identity, keeps the certificate aligned.
                verification::dedup_conflict_with_farkas(&mut conflict);
                // Structural Farkas verification in all builds (#3175)
                verification::log_conflict_debug(
                    &conflict.literals,
                    if label == "check_theory" {
                        "DpllT::check_theory UnsatWithFarkas"
                    } else {
                        "DpllT::check_theory_with_proof_tracking UnsatWithFarkas"
                    },
                );
                // Graceful degradation (#5536): when Farkas certificate verification
                // fails (structural or semantic), drop the certificate but keep the
                // conflict clause. The conflict literals are derived from sound simplex
                // analysis and are valid for CDCL learning. Only the proof certificate
                // is invalid. This matches extension.rs propagation path behavior.
                let mut farkas_valid = true;
                if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
                    if e.is_missing_annotation() {
                        // Missing Farkas annotation (#6535): conflict is sound but
                        // proof certificate cannot be recorded.
                        tracing::debug!(
                            context = label,
                            conflict_len = conflict.literals.len(),
                            "Farkas annotation missing; conflict clause is sound, skipping proof cert"
                        );
                    } else {
                        // #8165: Track Farkas structural verification failures.
                        self.farkas_certificate_failures += 1;
                        tracing::error!(
                            context = label,
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            conflict = ?conflict.literals,
                            "BUG(#5536): Farkas structural verification failed; using conflict clause without certificate"
                        );
                    }
                    // #8165: Track Farkas certificate downgrades (cert dropped, conflict kept).
                    self.farkas_certificate_downgrades += 1;
                    farkas_valid = false;
                }
                // Semantic Farkas verification (#4515). Runs in ALL builds
                // (adversarial-review followup on #rank-4 increment 2; was
                // debug-only per W16-5): a semantically verified certificate
                // is this arm's release backstop for the UNSAT verdict.
                let mut farkas_semantically_verified = false;
                if farkas_valid && self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        match verify_theory_conflict_with_farkas_full(&conflict, terms) {
                            Ok(()) => farkas_semantically_verified = true,
                            Err(e) => {
                                // #8165: Track Farkas semantic verification failures.
                                self.farkas_certificate_failures += 1;
                                self.farkas_certificate_downgrades += 1;
                                tracing::error!(
                                    context = label,
                                    error = %e,
                                    conflict_len = conflict.literals.len(),
                                    conflict = ?conflict.literals,
                                    "BUG(#5536): Farkas semantic verification failed; using conflict clause without certificate"
                                );
                                farkas_valid = false;
                            }
                        }
                    }
                }
                // Release backstop (adversarial-review followup): when the
                // UNSAT verdict is NOT covered by a semantically verified
                // certificate, run the same domain-aware semantic re-check
                // the Unsat arm runs (#8123), with the same hard
                // failure -> Unknown bail and term-count budget (#8558).
                if !farkas_semantically_verified {
                    if let Some(terms) = self.terms {
                        const SEMANTIC_VERIFY_TERM_LIMIT: usize = 50_000;
                        if terms.len() <= SEMANTIC_VERIFY_TERM_LIMIT {
                            if let Err(e) =
                                verify_conflict_semantic(&conflict.literals, terms, &support_axioms)
                            {
                                tracing::error!(
                                    context = label,
                                    error = %e,
                                    conflict_len = conflict.literals.len(),
                                    "BUG(#8123): semantic conflict verification failed in theory_check UnsatWithFarkas path; returning Unknown"
                                );
                                self.emit_theory_check_event(
                                    "consistency",
                                    "unknown",
                                    None,
                                    Some(conflict.literals.len()),
                                    consistency_duration,
                                );
                                return TheoryCheck::Unknown;
                            }
                        } else {
                            tracing::debug!(
                                term_count = terms.len(),
                                limit = SEMANTIC_VERIFY_TERM_LIMIT,
                                conflict_len = conflict.literals.len(),
                                "semantic conflict verification skipped: term count exceeds budget (#8558)"
                            );
                        }
                    }
                }
                // Record Farkas proof data only if the certificate is valid
                if farkas_valid {
                    if let Some((ref mut tracker, negations)) = tracking {
                        theory_inference::record_theory_conflict_unsat_with_farkas(
                            tracker, self.terms, negations, &conflict,
                        );
                    }
                }
                // #6546: dynamically register unmapped terms so Farkas conflict
                // clauses are never dropped as partial.
                let mut clause: Vec<Literal> = conflict
                    .literals
                    .iter()
                    .map(|t| self.term_to_literal_or_register(t.term, !t.value))
                    .collect();
                // #8424: Pre-minimize Farkas conflict clause, then level-0 removal.
                let mut removed = if let Some(ref farkas) = conflict.farkas {
                    let mut coeffs = farkas.coefficients.clone();
                    theory_inference::minimize_farkas_conflict(&mut clause, &mut coeffs)
                } else {
                    0
                };
                // Level-0 removal applies to both Farkas and non-Farkas paths.
                removed += theory_inference::minimize_conflict_with_levels(&mut clause, |var| {
                    self.sat.var_level(var)
                });
                self.theory_minimize_lits_removed += removed as u64;
                // #8165: Track conflict clause literal counts.
                let clause_len = clause.len() as u64;
                self.conflict_total_literals += clause_len;
                if clause_len > self.conflict_max_literals {
                    self.conflict_max_literals = clause_len;
                }
                self.emit_theory_check_event(
                    "consistency",
                    "conflict",
                    None,
                    Some(clause.len()),
                    consistency_duration,
                );
                TheoryCheck::Conflict(clause)
            }
            // All current TheoryResult variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TheoryResult variant in theory_check(): {other:?}"),
        }
    }
}
