// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `StringSolver`.
//!
//! Implements the DPLL(T) theory interface for the string theory.

use super::*;
use ay_core::safe_eprintln;

impl TheorySolver for StringSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.state.assert_literal(self.terms, literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        // Soundness gate (#8454): if an earlier pop() detected trail underflow
        // (corrupted union-find / EQC state), refuse to produce a result.
        if self.state.poisoned {
            safe_eprintln!(
                "BUG: strings check() skipped — solver poisoned by earlier invariant violation"
            );
            return TheoryResult::Unknown;
        }
        self.cycle_conflict_trustworthy = false;
        tracing::debug!("strings check");
        // CVC5-style internal fact loop: base/core/regexp checks, merge
        // inferred equalities, repeat until fixpoint or conflict (#3429).
        const MAX_INTERNAL_FACT_ROUNDS: usize = 128;
        let mut deferred_lemma: Option<StringLemma> = None;
        let mut sticky_incomplete = false; // survives core.clear() (#3608)
        let mut cycle_fired = false; // persists across rounds (#3875)
        for _round in 0..MAX_INTERNAL_FACT_ROUNDS {
            self.infer.clear();
            self.core.clear();
            self.regexp.clear();
            // Step 1: Base solver — constant conflicts.
            if self
                .base
                .check_init(self.terms, &self.state, &mut self.infer)
            {
                self.conflict_count += 1;
                return self.infer.to_theory_result();
            }
            // Step 2: Core solver — normal form computation and checking.
            if self
                .core
                .check(self.terms, &self.state, &mut self.infer, &mut self.skolems)
            {
                self.conflict_count += 1;
                self.cycle_conflict_trustworthy = cycle_fired; // #3875
                return self.infer.to_theory_result();
            }
            cycle_fired |= self.infer.has_cycle_inferences(); // #3875

            if let Some(lemma) = self.core.take_pending_lemma() {
                if self.infer.has_internal_equalities() {
                    deferred_lemma = Some(lemma); // defer — pending eqs may change needs
                } else {
                    return TheoryResult::NeedStringLemma(lemma);
                }
            }

            // Step 2b: Regex solver — ground membership evaluation.
            if self.regexp.check(self.terms, &self.state, &mut self.infer) {
                self.conflict_count += 1;
                return self.infer.to_theory_result();
            }

            // Latch incompleteness across rounds (#3608).
            sticky_incomplete |= self.core.is_incomplete() || self.regexp.is_incomplete();

            // Step 3: Merge internal equalities from N_UNIFY-style rules.
            let merge_result = self.merge_internal_equalities();
            if merge_result.merged_any {
                // Merges may resolve latched incompleteness; re-evaluate.
                sticky_incomplete = false;
                continue;
            }

            // Emit deferred splits for empty-explanation equalities (#4025).
            if let Some(split) = merge_result.deferred_splits.into_iter().next() {
                return TheoryResult::NeedStringLemma(split);
            }

            // No new internal facts — return deferred lemma if any.
            if let Some(lemma) = deferred_lemma.take() {
                return TheoryResult::NeedStringLemma(lemma);
            }
            if sticky_incomplete {
                return TheoryResult::Unknown;
            }
            return self.infer.to_theory_result();
        }

        // Safety cap reached; avoid claiming Sat without convergence.
        deferred_lemma.map_or(TheoryResult::Unknown, TheoryResult::NeedStringLemma)
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        if self.terms.sort(lhs) != self.terms.sort(rhs) {
            return;
        }
        if !matches!(self.terms.sort(lhs), Sort::String | Sort::Int) {
            return;
        }

        self.state.register_term(self.terms, lhs);
        self.state.register_term(self.terms, rhs);
        if self.state.find(lhs) == self.state.find(rhs) {
            return;
        }

        let _ = self.state.merge_with_explanation(lhs, rhs, reason);

        // Zero-length inference (#3526): when N-O propagates str.len(x) = 0,
        // infer x = "" directly. The SAT-level bridge axiom
        // [NOT(str.len(x)=0), x=""] cannot fire because the LIA-derived
        // equality isn't propagated as a SAT literal in the CEGAR architecture.
        if *self.terms.sort(lhs) == Sort::Int {
            self.infer_empty_from_zero_length(lhs, rhs, reason);
        }
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = self.infer.drain_propagations();
        self.propagation_count += props.len() as u64;
        props
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("strings_checks", self.check_count),
            ("strings_conflicts", self.conflict_count),
            ("strings_propagations", self.propagation_count),
        ]
    }

    fn push(&mut self) {
        self.state.push();
        self.skolems.push();
    }

    fn pop(&mut self) {
        self.state.pop();
        self.skolems.pop();
        self.core.clear();
        self.regexp.clear();
        self.infer.clear();
    }

    fn reset(&mut self) {
        self.state.reset();
        self.skolems.reset();
        self.core.clear();
        self.regexp.clear();
        self.infer.clear();
        // Re-register empty string after reset so cycle detection and
        // endpoint-empty inferences work even when the formula has no
        // explicit "" literal. The TermId is stable across resets.
        if let Some(empty_id) = self.pre_registered_empty {
            self.state.set_empty_string_id(self.terms, empty_id);
        }
    }

    /// Soft reset: clear assertion/EQC state but preserve statistics,
    /// empty string ID, and reduced terms (#3762).
    ///
    /// Unlike `reset()`, this preserves:
    /// - Cumulative statistics (`check_count`, `conflict_count`, `propagation_count`)
    /// - Reduced term markers in `CoreSolver` (structural, valid across SAT models)
    /// - Pre-registered empty string ID
    ///
    /// Called between CEGAR iterations where the SAT model changes but
    /// the formula structure (reduced terms, statistics) should persist.
    fn soft_reset(&mut self) {
        self.state.reset();
        self.skolems.reset();
        // core.clear() preserves reduced_terms -- only clears ephemeral state.
        self.core.clear();
        self.regexp.clear();
        self.infer.clear();
        self.cycle_conflict_trustworthy = false;
        // Re-register empty string (same as reset).
        if let Some(empty_id) = self.pre_registered_empty {
            self.state.set_empty_string_id(self.terms, empty_id);
        }
    }
}
