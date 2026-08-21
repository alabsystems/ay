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
        self.term_to_var
            .get(&term)
            .or_else(|| self.minted_term_to_var.get(&term))
            .map(|&v| Variable::new(v))
    }

    /// Mint a fresh SAT variable to name `term` mid-search (#6846).
    ///
    /// Returns `None` when minting is not safe or not enabled, in which case the
    /// caller must keep its previous fail-closed behaviour.
    ///
    /// Safety of the id choice: the new id starts at the solver's current
    /// `num_vars()` and advances by one per mint, so it can never alias an
    /// existing variable. `SolverContext::num_vars` defaults to 0 for contexts
    /// that do not track it (the test doubles), and 0 is treated as "unknown" —
    /// refusing rather than guessing, because guessing would alias a fresh term
    /// onto a live variable and silently corrupt the assignment.
    ///
    /// The mapping is recorded permanently for this solve: a term must map to
    /// exactly one variable for the whole search, or two clauses could name the
    /// same atom differently.
    pub(super) fn mint_var_for_term(
        &mut self,
        term: TermId,
        ctx: &dyn ay_sat::SolverContext,
    ) -> Option<Variable> {
        if let Some(existing) = self.var_for_term(term) {
            return Some(existing);
        }
        let base = ctx.num_vars();
        if base == 0 {
            return None;
        }
        let id = u32::try_from(base + self.minted_term_to_var.len()).ok()?;
        self.minted_term_to_var.insert(term, id);
        self.minted_var_to_term.insert(id, term);
        self.minted_var_count += 1;
        Some(Variable::new(id))
    }

    /// Convert a theory literal to a SAT literal
    /// #dt-context-derivation: record the (surviving blocking clause,
    /// level-0 premise facts) pair for a theory conflict about to be
    /// level-0-minimized by `minimize_conflict_with_levels`. The minimization
    /// strips exactly the blocking literals falsified at decision level 0 —
    /// i.e. the asserted premises that make the surviving clause
    /// context-dependent. The record grants no authority: sealing and the
    /// certification fragment independently re-derive the entailment. Fails
    /// closed to no record on any term/literal/negation mapping gap.
    pub(super) fn record_context_conflict_premises(
        &mut self,
        conflict_terms: &[ay_core::TheoryLit],
        ctx: &dyn ay_sat::SolverContext,
    ) {
        const MAX_CONTEXT_CONFLICT_LITERALS: usize = 64;
        if self.context_records.is_none()
            || conflict_terms.is_empty()
            || conflict_terms.len() > MAX_CONTEXT_CONFLICT_LITERALS
        {
            return;
        }
        let Some(proof) = self.proof.as_ref() else {
            return;
        };
        let negations = proof.negations;
        let mut premises: Vec<TermId> = Vec::new();
        let mut surviving: Vec<TermId> = Vec::new();
        for conflict_lit in conflict_terms {
            let Some(literal) = self.term_to_literal(conflict_lit.term, !conflict_lit.value) else {
                return;
            };
            let Some(&negation) = negations.get(&conflict_lit.term) else {
                return;
            };
            let (fact, blocking) = if conflict_lit.value {
                (conflict_lit.term, negation)
            } else {
                (negation, conflict_lit.term)
            };
            if ctx.var_level(literal.variable()) == Some(0) {
                premises.push(fact);
            } else {
                surviving.push(blocking);
            }
        }
        if premises.is_empty() || surviving.is_empty() {
            return;
        }
        // Level-0 reason expansion: a stripped premise is often itself a
        // BCP-derived fact (e.g. a negative tester forced by a committed
        // equality), not an asserted term. Walk the level-0 implication
        // graph and record one auxiliary hint per derived fact — clause =
        // the fact's unit, premises = the negations of its reason clause's
        // other literals — so the consumption chain can discharge the whole
        // tree down to assertion activation units. Bounded; every mapping
        // gap simply stops that branch (fail-closed).
        const MAX_REASON_EXPANSIONS: usize = 1024;
        let mut expansions: Vec<crate::executor::DtContextConflictRecord> = Vec::new();
        {
            let mut visited: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
            let mut pending: Vec<Literal> = Vec::new();
            for conflict_lit in conflict_terms {
                if let Some(literal) = self.term_to_literal(conflict_lit.term, conflict_lit.value) {
                    if ctx.var_level(literal.variable()) == Some(0) {
                        pending.push(literal);
                    }
                }
            }
            let fact_term_of = |this: &Self, literal: Literal| -> Option<TermId> {
                let atom = *this.var_to_term.get(&(literal.variable().index() as u32))?;
                if literal.is_positive() {
                    Some(atom)
                } else {
                    negations.get(&atom).copied()
                }
            };
            while let Some(true_literal) = pending.pop() {
                if visited.len() >= MAX_REASON_EXPANSIONS
                    || !visited.insert(true_literal.variable().index() as u32)
                {
                    continue;
                }
                let Some(initial_side) = ctx.var_reason_side(true_literal.variable()) else {
                    continue;
                };
                if initial_side.is_empty() {
                    continue;
                }
                let Some(fact) = fact_term_of(self, true_literal) else {
                    continue;
                };
                // A side literal over a Tseitin AUX variable has no term; it
                // is itself level-0-propagated, so resolve THROUGH it by
                // flattening its own reason side in (unit resolution on the
                // aux variable — the composed premises still entail the
                // fact). Bounded; any gap abandons this fact fail-closed.
                let mut side_facts: Vec<TermId> = Vec::new();
                let mut atom_sides: Vec<Literal> = Vec::new();
                let mut side_work = initial_side;
                let mut seen_side: std::collections::BTreeSet<u64> =
                    std::collections::BTreeSet::new();
                let mut flatten_budget = 64usize;
                let mut complete = true;
                while let Some(side_literal) = side_work.pop() {
                    if flatten_budget == 0 {
                        complete = false;
                        break;
                    }
                    flatten_budget -= 1;
                    let side_key = (side_literal.variable().index() as u64) * 2
                        + u64::from(side_literal.is_positive());
                    if !seen_side.insert(side_key) {
                        continue;
                    }
                    // The side literal is FALSE; its negation is the fact.
                    if let Some(side_fact) = fact_term_of(self, side_literal.negated()) {
                        if !side_facts.contains(&side_fact) {
                            side_facts.push(side_fact);
                            atom_sides.push(side_literal);
                        }
                        continue;
                    }
                    let aux_true = side_literal.negated();
                    if ctx.var_level(aux_true.variable()) != Some(0) {
                        complete = false;
                        break;
                    }
                    let Some(aux_side) = ctx.var_reason_side(aux_true.variable()) else {
                        complete = false;
                        break;
                    };
                    side_work.extend(aux_side);
                }
                if !complete || side_facts.is_empty() {
                    continue;
                }
                for side_literal in atom_sides {
                    pending.push(side_literal.negated());
                }
                expansions.push(crate::executor::DtContextConflictRecord {
                    clause: vec![fact],
                    premises: side_facts,
                });
            }
        }
        let Some(records) = self.context_records.as_deref_mut() else {
            return;
        };
        records.record(surviving, premises);
        for expansion in expansions {
            records.record(expansion.clause, expansion.premises);
        }
    }

    /// Whether the #dt-context-derivation record sink is at capacity (so the
    /// lazy path can skip reason materialization entirely).
    pub(super) fn context_records_full(&self) -> bool {
        self.context_records
            .as_deref()
            .is_none_or(crate::executor::DtContextConflictSink::is_full)
    }

    /// #dt-context-derivation: hint-record one theory propagation as
    /// `fact ← reason facts` so certification-time premise chains can
    /// discharge level-0 theory propagations (lazy reasons are invisible to
    /// the SAT-side reason walk). Pure hint: no tracker step, no clause, no
    /// behavior change; sealing independently re-derives the entailment.
    pub(super) fn record_context_propagation(
        &mut self,
        literal: &ay_core::TheoryLit,
        reason: &[ay_core::TheoryLit],
    ) {
        const MAX_CONTEXT_PREMISES: usize = 16;
        if reason.is_empty()
            || reason.len() > MAX_CONTEXT_PREMISES
            || self.context_records.is_none()
        {
            return;
        }
        let Some(proof) = self.proof.as_ref() else {
            return;
        };
        let negations = proof.negations;
        let fact_of = |lit: &ay_core::TheoryLit| -> Option<TermId> {
            if lit.value {
                Some(lit.term)
            } else {
                negations.get(&lit.term).copied()
            }
        };
        let Some(fact) = fact_of(literal) else {
            return;
        };
        let mut premises: Vec<TermId> = Vec::with_capacity(reason.len());
        for reason_lit in reason {
            let Some(premise) = fact_of(reason_lit) else {
                return;
            };
            if premise != fact && !premises.contains(&premise) {
                premises.push(premise);
            }
        }
        if premises.is_empty() {
            return;
        }
        let Some(records) = self.context_records.as_deref_mut() else {
            return;
        };
        records.record(vec![fact], premises);
    }

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
