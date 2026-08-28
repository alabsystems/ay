// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification and SAT delivery of Farkas-annotated theory conflicts.

use ay_core::{TheoryConflict, TheoryResult, TheorySolver};
use ay_sat::ExtPropagateResult;

use super::conflict::ConflictOrigin;
use super::*;
use crate::theory_inference::record_theory_conflict_unsat_with_farkas;
#[cfg(debug_assertions)]
use crate::verification::verify_theory_conflict_with_farkas_full;
use crate::verification::{log_conflict_debug, verify_theory_conflict_with_farkas};

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn handle_farkas_conflict(
        &mut self,
        mut conflict: TheoryConflict,
        round: &PropagationRound<'_>,
    ) -> ExtPropagateResult {
        crate::verification::dedup_conflict_with_farkas(&mut conflict);
        self.log_farkas_level0_conflict(&conflict, round);
        log_conflict_debug(&conflict.literals, "UnsatWithFarkas");
        let certificate_valid = self.farkas_certificate_is_valid(&conflict);
        if certificate_valid {
            if let Some(proof) = self.proof.as_mut() {
                let _ = record_theory_conflict_unsat_with_farkas(
                    proof.tracker,
                    self.terms,
                    proof.negations,
                    &conflict,
                );
            }
        }
        if !self.farkas_conflict_is_semantically_valid(&conflict) {
            self.pending_split = Some(TheoryResult::Unknown);
            self.emit_conflict_unknown(round);
            return ExtPropagateResult::none();
        }
        if !self.verify_full_state_guard(&conflict.literals, round, ConflictOrigin::Farkas) {
            self.emit_conflict_unknown(round);
            return ExtPropagateResult::none();
        }
        let Some(mut clause) = self.map_conflict_clause(&conflict.literals, ConflictOrigin::Farkas)
        else {
            self.emit_conflict_unknown(round);
            return ExtPropagateResult::none();
        };
        let mut removed = conflict.farkas.as_ref().map_or(0, |annotation| {
            let mut coefficients = annotation.coefficients.clone();
            crate::theory_inference::minimize_farkas_conflict(&mut clause, &mut coefficients)
        });
        removed +=
            crate::theory_inference::minimize_conflict_with_levels(&mut clause, |variable| {
                round.ctx.var_level(variable)
            });
        self.eager_stats.theory_minimize_lits_removed += removed as u64;
        self.finish_theory_conflict(clause, round, ConflictOrigin::Farkas)
    }

    fn farkas_certificate_is_valid(&self, conflict: &TheoryConflict) -> bool {
        let valid = match verify_theory_conflict_with_farkas(conflict) {
            Ok(()) => true,
            Err(error) if error.is_missing_annotation() => {
                tracing::debug!(
                    conflict_len = conflict.literals.len(),
                    "Farkas annotation missing in propagate(); conflict clause is sound, skipping proof cert"
                );
                false
            }
            Err(error) => {
                tracing::warn!(
                    error = %error,
                    conflict_len = conflict.literals.len(),
                    "BUG(#4666): Farkas conflict verification failed in propagate(); using conflict clause without certificate (#8595)"
                );
                false
            }
        };
        #[cfg(debug_assertions)]
        let valid = {
            let mut valid = valid;
            if valid && self.theory.supports_farkas_semantic_check() {
                if let Some(terms) = self.terms {
                    if let Err(error) = verify_theory_conflict_with_farkas_full(conflict, terms) {
                        tracing::warn!(
                            error = %error,
                            conflict_len = conflict.literals.len(),
                            "BUG(#4666): Farkas semantic verification failed in propagate(); using conflict clause without certificate (#8595)"
                        );
                        valid = false;
                    }
                }
            }
            valid
        };
        valid
    }

    fn farkas_conflict_is_semantically_valid(&mut self, conflict: &TheoryConflict) -> bool {
        let Some(terms) = self.terms else {
            return true;
        };
        if let Err(error) = self.verify_conflict_semantic_memo(&conflict.literals, terms, false) {
            tracing::error!(
                error = %error,
                conflict_len = conflict.literals.len(),
                "BUG(#8123): semantic conflict verification failed in propagate() Farkas path; escalating to Unknown"
            );
            return false;
        }
        true
    }

    fn log_farkas_level0_conflict(&self, conflict: &TheoryConflict, round: &PropagationRound<'_>) {
        if round.sat_level != 0 {
            return;
        }
        tracing::debug!(
            conflict_len = conflict.literals.len(),
            asserted_theory_atoms = round.asserted_atoms,
            sat_level = round.sat_level,
            "level-0 Farkas conflict (verifying before trusting)"
        );
        if !tracing::enabled!(tracing::Level::DEBUG) {
            return;
        }
        if let Some(terms) = self.terms {
            for (index, literal) in conflict.literals.iter().enumerate() {
                let rendered =
                    crate::extension::types::format_term_recursive(terms, literal.term, 6);
                tracing::debug!(
                    idx = index,
                    term = ?literal.term,
                    value = literal.value,
                    term_str = %rendered,
                    "  conflict atom"
                );
            }
            if let Some(annotation) = conflict.farkas.as_ref() {
                for (index, coefficient) in annotation.coefficients.iter().enumerate() {
                    tracing::debug!(idx = index, coeff = %coefficient, "  Farkas coefficient");
                }
            }
        }
    }
}
