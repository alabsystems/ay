// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification and SAT delivery of ordinary theory conflicts.
//!
//! Structural, domain-semantic, and bounded full-state guards run before proof
//! recording or clause emission. Any rejected or partially mapped explanation
//! fails closed by returning no conflict to SAT.

use ay_core::{TheoryLit, TheoryResult, TheorySolver};
use ay_sat::{ExtPropagateResult, Literal};

use super::*;
use crate::theory_inference::record_theory_conflict_unsat;
use crate::verification::{
    log_conflict_debug, verify_lra_full_state_satisfiable, verify_theory_conflict,
};

#[derive(Clone, Copy)]
pub(crate) enum ConflictOrigin {
    Plain,
    Farkas,
}

/// Result of mapping a validated theory conflict to SAT literals.
/// `Falsified` requires every literal to be false in the current SAT context.
/// A named variable can still be unassigned after minting or backtracking;
/// a complete mapping alone grants no conflict-analysis authority.
pub(crate) enum MappedConflict {
    Falsified(Vec<Literal>),
    Lemma(Vec<Literal>),
}

impl MappedConflict {
    fn from_clause(clause: Vec<Literal>, ctx: &dyn ay_sat::SolverContext) -> Self {
        if clause
            .iter()
            .all(|literal| ctx.value(literal.variable()) == Some(!literal.is_positive()))
        {
            Self::Falsified(clause)
        } else {
            Self::Lemma(clause)
        }
    }
}

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn handle_plain_conflict(
        &mut self,
        mut conflict: Vec<TheoryLit>,
        round: &PropagationRound<'_>,
    ) -> ExtPropagateResult {
        crate::verification::dedup_conflict_literals(&mut conflict);
        self.log_plain_level0_conflict(&conflict, round);
        log_conflict_debug(&conflict, "Unsat");
        if !self.plain_conflict_is_verified(&conflict) {
            self.pending_split = Some(TheoryResult::Unknown);
            self.emit_conflict_unknown(round);
            return ExtPropagateResult::none();
        }
        if !self.verify_full_state_guard(&conflict, round, ConflictOrigin::Plain) {
            self.emit_conflict_unknown(round);
            return ExtPropagateResult::none();
        }
        if let Some(proof) = self.proof.as_mut() {
            let _ =
                record_theory_conflict_unsat(proof.tracker, self.terms, proof.negations, &conflict);
        }
        if self.proof.is_none() {
            if let Some(terms) = self.terms {
                let removed = crate::theory_inference::minimize_euf_conflict(&mut conflict, terms);
                self.eager_stats.theory_minimize_lits_removed += removed as u64;
            }
        }
        let Some(mapped) = self.map_conflict_clause(&conflict, ConflictOrigin::Plain, round.ctx)
        else {
            self.emit_conflict_unknown(round);
            return ExtPropagateResult::none();
        };
        let mut clause = match mapped {
            MappedConflict::Falsified(clause) => clause,
            MappedConflict::Lemma(clause) => {
                // A complete theory clause can still contain a satisfied or
                // unassigned literal, including a retained minted mapping.
                // Deliver it as a lemma, never as a falsified conflict.
                self.emit_eager_event(
                    round.sat_level,
                    round.asserted_atoms,
                    "lemma",
                    0,
                    round.started_at,
                );
                let mut result = ExtPropagateResult::default();
                result.clauses = vec![clause];
                return result;
            }
        };
        if !matches!(
            self.minimize_context_conflict(&conflict, &mut clause, round.ctx),
            crate::theory_inference::ConflictClauseReduction::Clause { .. }
        ) {
            self.pending_split = Some(TheoryResult::Unknown);
            self.emit_conflict_unknown(round);
            return ExtPropagateResult::none();
        }
        self.finish_theory_conflict(clause, round, ConflictOrigin::Plain)
    }

    fn plain_conflict_is_verified(&mut self, conflict: &[TheoryLit]) -> bool {
        let mut verified = true;
        if let Err(error) = verify_theory_conflict(conflict) {
            verified = false;
            tracing::warn!(
                error = %error,
                conflict_len = conflict.len(),
                "BUG(#4666): theory conflict verification failed in propagate(); escalating to Unknown"
            );
        }
        // `Some(verdict)` only when the direct EUF re-check ran AND accepted;
        // a rejection leaves it `None` so the dispatcher re-derives the exact
        // error (and the memo records the rejection, not an acceptance).
        let mut euf_precheck = None;
        if self.theory.supports_euf_semantic_check() {
            if let Some(terms) = self.terms {
                match crate::verification::verify_euf_conflict_classified(
                    conflict,
                    terms,
                    &self.support_axioms,
                ) {
                    Ok(verdict) => euf_precheck = Some(verdict),
                    Err(error) => {
                        verified = false;
                        tracing::warn!(
                            error = %error,
                            conflict_len = conflict.len(),
                            "BUG(#4704): EUF semantic verification failed in propagate(); escalating to Unknown"
                        );
                    }
                }
            }
        }
        if let Some(terms) = self.terms {
            if let Err(error) = self.verify_conflict_semantic_memo(conflict, terms, euf_precheck) {
                verified = false;
                tracing::warn!(
                    error = %error,
                    conflict_len = conflict.len(),
                    "BUG(#8123): semantic conflict verification failed in propagate() Unsat; escalating to Unknown"
                );
            }
        }
        verified
    }

    fn log_plain_level0_conflict(&self, conflict: &[TheoryLit], round: &PropagationRound<'_>) {
        if round.sat_level != 0 {
            return;
        }
        tracing::debug!(
            conflict_len = conflict.len(),
            asserted_theory_atoms = round.asserted_atoms,
            sat_level = round.sat_level,
            "level-0 theory conflict (verifying before trusting)"
        );
        for (index, literal) in conflict.iter().enumerate() {
            tracing::debug!(
                idx = index,
                term = ?literal.term,
                value = literal.value,
                "  conflict atom"
            );
        }
    }

    pub(super) fn verify_full_state_guard(
        &mut self,
        conflict: &[TheoryLit],
        round: &PropagationRound<'_>,
        origin: ConflictOrigin,
    ) -> bool {
        if round.sat_level != 0
            || !self.theory.supports_farkas_semantic_check()
            || self.full_state_guard_checks >= FULL_STATE_GUARD_BUDGET
        {
            return true;
        }
        let Some(terms) = self.terms else {
            return true;
        };
        self.full_state_guard_checks += 1;
        let all_literals: Vec<TheoryLit> = round
            .trail
            .iter()
            .filter_map(|&literal| {
                let term = self.var_to_term.get(&literal.variable().id())?;
                self.theory_atom_set
                    .contains(term)
                    .then(|| TheoryLit::new(*term, literal.is_positive()))
            })
            .collect();
        if let Err(error) = verify_lra_full_state_satisfiable(&all_literals, terms) {
            self.full_state_guard_rejections += 1;
            match origin {
                ConflictOrigin::Plain => tracing::error!(
                    error = %error,
                    conflict_len = conflict.len(),
                    total_theory_atoms = all_literals.len(),
                    rejections = self.full_state_guard_rejections,
                    "BUG(#8254): level-0 conflict rejected by full-state soundness guard"
                ),
                ConflictOrigin::Farkas => tracing::error!(
                    error = %error,
                    conflict_len = conflict.len(),
                    total_theory_atoms = all_literals.len(),
                    rejections = self.full_state_guard_rejections,
                    "BUG(#8254): level-0 Farkas conflict rejected by full-state soundness guard"
                ),
            }
            return false;
        }
        true
    }

    pub(super) fn map_conflict_clause(
        &mut self,
        conflict: &[TheoryLit],
        origin: ConflictOrigin,
        ctx: &dyn ay_sat::SolverContext,
    ) -> Option<MappedConflict> {
        self.map_conflict_clause_minting(
            conflict,
            origin,
            ctx,
            super::super::check::mint_theory_vars_enabled(),
        )
    }

    /// Map a theory conflict to SAT literals, optionally minting
    /// variables for unencoded terms (#6846 BCP parity with the
    /// `check()` path in `extension/check.rs`). Farkas-origin
    /// conflicts never mint: their coefficient vector is aligned to
    /// the original literal list and the proof path is unchanged, so
    /// a partial Farkas mapping keeps failing closed.
    pub(crate) fn map_conflict_clause_minting(
        &mut self,
        conflict: &[TheoryLit],
        origin: ConflictOrigin,
        ctx: &dyn ay_sat::SolverContext,
        mint_enabled: bool,
    ) -> Option<MappedConflict> {
        let clause: Vec<Literal> = conflict
            .iter()
            .filter_map(|term| self.term_to_literal(term.term, !term.value))
            .collect();
        if clause.len() == conflict.len() {
            return Some(MappedConflict::from_clause(clause, ctx));
        }
        if mint_enabled && matches!(origin, ConflictOrigin::Plain) {
            let mut minted_clause = Vec::with_capacity(conflict.len());
            let mut complete = true;
            for term in conflict {
                match self.term_to_literal_minting(term.term, !term.value, ctx, true) {
                    Some(literal) => minted_clause.push(literal),
                    None => {
                        complete = false;
                        break;
                    }
                }
            }
            if complete {
                tracing::debug!(
                    lits = minted_clause.len(),
                    "#6846: minted SAT variables for an otherwise-partial BCP theory conflict"
                );
                return Some(MappedConflict::from_clause(minted_clause, ctx));
            }
        }
        self.partial_clause_count += 1;
        crate::combined_solvers::theory_stats::inc_partial_clauses();
        if self.partial_clause_count >= 100 {
            tracing::error!(
                count = self.partial_clause_count,
                "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
            );
        }
        match origin {
            ConflictOrigin::Plain => tracing::error!(
                mapped = clause.len(),
                total = conflict.len(),
                "BUG(#4666): theory conflict mapped to partial clause; skipping"
            ),
            ConflictOrigin::Farkas => tracing::error!(
                mapped = clause.len(),
                total = conflict.len(),
                "BUG(#4666): Farkas conflict mapped to partial clause; skipping"
            ),
        }
        None
    }

    pub(super) fn finish_theory_conflict(
        &mut self,
        clause: Vec<Literal>,
        round: &PropagationRound<'_>,
        origin: ConflictOrigin,
    ) -> ExtPropagateResult {
        if self.debug {
            match origin {
                ConflictOrigin::Plain => {
                    safe_eprintln!("[EAGER] Theory check conflict: {} literals", clause.len());
                }
                ConflictOrigin::Farkas => safe_eprintln!(
                    "[EAGER] Theory check conflict with Farkas: {} literals",
                    clause.len()
                ),
            }
        }
        self.theory_conflict_count += 1;
        self.total_bcp_conflicts += 1;
        if clause.len() <= 3 {
            self.consecutive_tiny_conflicts += 1;
        }
        self.zero_propagation_streak = 0;
        self.emit_eager_event(
            round.sat_level,
            round.asserted_atoms,
            "conflict",
            0,
            round.started_at,
        );
        let bump_vars = clause.iter().map(|literal| literal.variable()).collect();
        ExtPropagateResult::conflict(clause).with_bump_vars(bump_vars)
    }

    pub(super) fn emit_conflict_unknown(&mut self, round: &PropagationRound<'_>) {
        self.emit_eager_event(
            round.sat_level,
            round.asserted_atoms,
            "unknown",
            0,
            round.started_at,
        );
    }
}
