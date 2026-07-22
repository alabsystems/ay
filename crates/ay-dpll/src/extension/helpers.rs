// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small utility methods on `TheoryExtension` used by the propagation loop.
//!
//! Extracted from mod.rs to keep it under the 1,200-line target (#6862).

use ay_core::time::Instant;
use ay_core::{BoundRefinementRequest, ModelEqualityRequest, TermId, TheoryResult, TheorySolver};
use ay_sat::{Literal, Variable};

use crate::diagnostic_trace::duration_to_micros;
use crate::executor::BoundRefinementReplayKey;

use super::{BoundRefinementHandoff, TheoryExtension};

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Get the SAT variable for a term ID, if it exists
    pub(super) fn var_for_term(&self, term: TermId) -> Option<Variable> {
        self.term_to_var.get(&term).map(|&v| Variable::new(v))
    }

    /// Convert a theory literal to a SAT literal
    pub(super) fn term_to_literal(&self, term: TermId, value: bool) -> Option<Literal> {
        self.var_for_term(term).map(|var| {
            if value {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            }
        })
    }

    /// Check if a variable corresponds to a theory atom.
    ///
    /// Uses a dense bitset for O(1) lookup without hashing, falling back to
    /// the hashmap path only when the variable ID is out of bitset range
    /// (should not happen in practice since the bitset is sized to cover all
    /// variables in var_to_term).
    #[inline]
    pub(super) fn is_theory_atom(&self, var: Variable) -> bool {
        let id = var.id() as usize;
        let word_idx = id / 64;
        if word_idx < self.theory_var_bitset.len() {
            (self.theory_var_bitset[word_idx] >> (id % 64)) & 1 != 0
        } else {
            // Fallback for out-of-range IDs (should not happen).
            if let Some(&term) = self.var_to_term.get(&var.id()) {
                self.theory_atom_set.contains(&term)
            } else {
                false
            }
        }
    }

    /// Emit diagnostic trace event for eager propagation.
    ///
    /// `start` is `None` when diagnostic tracing is disabled, avoiding
    /// the `Instant::now()` syscall in the hot BCP loop.
    pub(super) fn emit_eager_event(
        &self,
        sat_level: u32,
        new_assertions: usize,
        check_result: &str,
        propagations: usize,
        start: Option<Instant>,
    ) {
        if let Some(diag) = self.diagnostic_trace {
            let micros = start.map_or(0, |s| duration_to_micros(s.elapsed()));
            diag.emit_eager_propagate(
                sat_level,
                new_assertions,
                check_result,
                propagations,
                micros,
            );
        }
    }

    pub(super) fn should_stop_for_inline_bound_refinement_handoff(
        &self,
        refinements: &[BoundRefinementRequest],
    ) -> bool {
        match &self.bound_refinement_handoff {
            BoundRefinementHandoff::FinalCheckOnly => false,
            BoundRefinementHandoff::StopAndReplayInline { known_replays } => {
                refinements.iter().any(|refinement| {
                    !known_replays.contains(&BoundRefinementReplayKey::new(refinement))
                })
            }
        }
    }

    pub(super) fn model_equality_already_encoded(&self, eq: &ModelEqualityRequest) -> bool {
        self.terms
            .and_then(|terms| terms.find_eq(eq.lhs, eq.rhs))
            .is_some_and(|eq_atom| self.term_to_var.contains_key(&eq_atom))
    }

    /// Semantic conflict verification through the Executor-owned memo
    /// (#4535 / #uflia-verify-memo).
    ///
    /// TRUST-TRUE-ONLY: a memoized `true` verdict short-circuits to `Ok(())`
    /// — the identical sorted literal set was already proven jointly UNSAT
    /// under this query's term/support state, so learning the clause is
    /// exactly as justified as on the first derivation. Any other case
    /// (miss, or memoized `false`) re-runs the FULL verification so every
    /// failure keeps its exact `VerificationError` kind (the check-path
    /// array-context carve-out pattern-matches `ConflictIsSat`). The fresh
    /// verdict is recorded for both outcomes; `false` entries still serve
    /// the lazy arms' fail-closed memo hits.
    ///
    /// `euf_prechecked` selects the duplicate-EUF-skip dispatcher variant;
    /// both variants return identical verdicts for identical inputs (see
    /// `verify_conflict_semantic_euf_prechecked`), so they share one memo.
    pub(super) fn verify_conflict_semantic_memo(
        &mut self,
        conflict: &[ay_core::TheoryLit],
        terms: &ay_core::TermStore,
        euf_prechecked: bool,
    ) -> Result<(), crate::verification::VerificationError> {
        let key: Option<Vec<ay_core::TheoryLit>> = self.verify_memo.as_ref().map(|_memo| {
            let mut key = conflict.to_vec();
            key.sort_unstable();
            key
        });
        if let (Some(memo), Some(key)) = (self.verify_memo.as_deref_mut(), key.as_ref()) {
            if memo.get(key) == Some(&true) {
                ay_lia::instrument::bump_verify_conflict_ext(true);
                return Ok(());
            }
        }
        // #verify-memo instrumentation: full fail-closed re-verification runs
        // (memo miss, memoized-false, or no memo wired).
        ay_lia::instrument::bump_verify_conflict_ext(false);
        let result = if euf_prechecked {
            crate::verification::verify_conflict_semantic_euf_prechecked(
                conflict,
                terms,
                &self.support_axioms,
            )
        } else {
            crate::verification::verify_conflict_semantic(conflict, terms, &self.support_axioms)
        };
        if let (Some(memo), Some(key)) = (self.verify_memo.as_deref_mut(), key) {
            memo.insert(key, result.is_ok());
        }
        result
    }

    pub(super) fn filter_stale_model_equalities(
        &self,
        eqs: Vec<ModelEqualityRequest>,
    ) -> Option<TheoryResult> {
        let mut fresh: Vec<ModelEqualityRequest> = eqs
            .into_iter()
            .filter(|eq| !self.model_equality_already_encoded(eq))
            .collect();
        match fresh.len() {
            0 => None,
            1 => Some(TheoryResult::NeedModelEquality(
                fresh
                    .pop()
                    .expect("invariant: one fresh model equality remains"),
            )),
            _ => Some(TheoryResult::NeedModelEqualities(fresh)),
        }
    }
}
