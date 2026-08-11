// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transactional ownership transfer for preprocessing-built extensions.

use super::super::config_preprocess_cleanup::PreprocessOutcome;
use super::super::*;
use std::collections::BTreeSet;

/// Prepared before SAT preprocessing so source variables can be frozen, but
/// committed only after preprocessing has completed successfully.
pub(in crate::solver) struct PendingPreprocessingExtension<E> {
    pub(super) prepared: PreparedExtension<E>,
    consumed_clause_slots: Vec<(usize, Vec<u32>, u64)>,
    arena_compactions_at_prepare: u64,
}

impl Solver {
    pub(in crate::solver) fn prepare_preprocessing_extension<E, B>(
        &mut self,
        build_extension: &mut B,
    ) -> Option<PendingPreprocessingExtension<E>>
    where
        E: Extension,
        B: FnMut(&[Vec<Literal>]) -> Option<PreparedExtension<E>>,
    {
        let (mut clauses, clause_offsets) = self.snapshot_irredundant_clauses();
        let prepared = build_extension(&clauses)?;
        let frozen_variables = prepared
            .frozen_variables
            .iter()
            .map(|var| var.index())
            .collect::<BTreeSet<_>>();
        if frozen_variables
            .iter()
            .any(|&var_idx| var_idx >= self.num_vars)
        {
            return None;
        }

        let mut consumed_clause_slots =
            Vec::with_capacity(prepared.consumed_clause_positions.len());
        let mut seen_positions = BTreeSet::new();
        for &position in &prepared.consumed_clause_positions {
            if !seen_positions.insert(position) {
                continue;
            }
            let (clause, &clause_idx) = clauses
                .get_mut(position)
                .zip(clause_offsets.get(position))?;
            // Exact replacement is compositional only while preprocessing
            // preserves every variable shared with the extension.
            if clause
                .iter()
                .any(|lit| !frozen_variables.contains(&lit.variable().index()))
            {
                return None;
            }
            // Move consumed payload out of the builder snapshot before
            // canonicalizing it. Accumulated keys replace snapshot payload
            // instead of duplicating the whole consumed-clause aggregate.
            let clause = std::mem::take(clause);
            consumed_clause_slots.push((
                clause_idx,
                crate::symmetry::canonical_clause_key(&clause),
                self.clause_id(ClauseRef(clause_idx as u32)),
            ));
        }

        for var in &prepared.frozen_variables {
            if var.index() < self.num_vars {
                self.freeze(*var);
            }
        }

        Some(PendingPreprocessingExtension {
            prepared,
            consumed_clause_slots,
            arena_compactions_at_prepare: self.cold.num_arena_compactions,
        })
    }

    /// Transfer all consumed clauses to the extension, or transfer none.
    ///
    /// A source changed by preprocessing means its proof identity may no
    /// longer justify extension lemmas. In that case the caller drops the
    /// pending extension and continues with the already-preprocessed CNF.
    pub(super) fn commit_preprocessing_extension<E>(
        &mut self,
        pending: &mut PendingPreprocessingExtension<E>,
    ) -> bool {
        if self.cold.num_arena_compactions != pending.arena_compactions_at_prepare {
            return false;
        }

        // Validate every bounded source slot before deleting any.
        for (clause_idx, original_key, original_id) in &pending.consumed_clause_slots {
            if *clause_idx >= self.arena.len()
                || !self.arena.is_active(*clause_idx)
                || self.arena.is_dead(*clause_idx)
                || self.arena.is_garbage_any(*clause_idx)
                || self.arena.is_learned(*clause_idx)
            {
                return false;
            }
            let current_key =
                crate::symmetry::canonical_clause_key(self.arena.literals(*clause_idx));
            if &current_key != original_key
                || self.clause_id(ClauseRef(*clause_idx as u32)) != *original_id
            {
                return false;
            }
        }

        // Suppress only committed source-clause deletion lines (#4533). The
        // external checker retains those axioms for extension-derived lemmas;
        // unrelated preprocessing deletions preserve their old behavior.
        let was_deferring = self.defer_proof_deletions;
        let deferred_len = self.deferred_proof_deletions.len();
        self.defer_proof_deletions = true;
        for (clause_idx, _, _) in &pending.consumed_clause_slots {
            self.delete_clause_checked(*clause_idx, mutate::ReasonPolicy::ClearLevel0);
        }
        self.defer_proof_deletions = was_deferring;
        self.deferred_proof_deletions.truncate(deferred_len);

        self.cold.extension_trusted_lemmas = true;
        self.num_original_clauses = self.arena.active_clause_count();
        drop(std::mem::take(&mut pending.consumed_clause_slots));
        true
    }

    pub(super) fn cancel_preprocessing_extension<E>(
        &mut self,
        pending: &PendingPreprocessingExtension<E>,
    ) {
        for var in &pending.prepared.frozen_variables {
            if var.index() < self.num_vars {
                self.melt(*var);
            }
        }
    }

    fn cancel_pending_preprocessing_extension<E>(
        &mut self,
        pending: &mut Option<PendingPreprocessingExtension<E>>,
    ) {
        if let Some(pending) = pending.take() {
            self.cancel_preprocessing_extension(&pending);
        }
    }

    /// Finish cleanup and atomically commit or cancel extension ownership.
    pub(super) fn finish_preprocessing_extension_transaction<E, F>(
        &mut self,
        pending: &mut Option<PendingPreprocessingExtension<E>>,
        preprocess_outcome: Option<PreprocessOutcome>,
        should_stop: &F,
    ) -> Result<(), SatResult>
    where
        F: Fn() -> bool + ?Sized,
    {
        if let Some(preprocess_outcome) = preprocess_outcome {
            let cleanup_unsat = self.finish_initial_preprocessing();
            let cleanup_stop =
                self.stop_reason_after_preprocess_cleanup(preprocess_outcome, should_stop);
            match preprocess_outcome {
                PreprocessOutcome::Stopped(latched_reason) => {
                    self.cancel_pending_preprocessing_extension(pending);
                    let reason = cleanup_stop.unwrap_or(latched_reason);
                    return Err(self.declare_unknown_with_reason(reason));
                }
                PreprocessOutcome::Unsat => {
                    self.cancel_pending_preprocessing_extension(pending);
                    if let Some(reason) = cleanup_stop {
                        return Err(self.declare_unknown_with_reason(reason));
                    }
                    return Err(self.declare_unsat());
                }
                PreprocessOutcome::Complete => {
                    if let Some(reason) = cleanup_stop {
                        self.cancel_pending_preprocessing_extension(pending);
                        return Err(self.declare_unknown_with_reason(reason));
                    }
                    if cleanup_unsat {
                        self.cancel_pending_preprocessing_extension(pending);
                        return Err(self.declare_unsat());
                    }
                }
            }
        }

        if let Some(reason) = self.solve_stop_reason(should_stop) {
            self.cancel_pending_preprocessing_extension(pending);
            return Err(self.declare_unknown_with_reason(reason));
        }

        if pending
            .as_mut()
            .is_some_and(|pending| !self.commit_preprocessing_extension(pending))
        {
            self.cancel_pending_preprocessing_extension(pending);
        }
        Ok(())
    }

    fn snapshot_irredundant_clauses(&self) -> (Vec<Vec<Literal>>, Vec<usize>) {
        let mut clauses = Vec::new();
        let mut clause_offsets = Vec::new();

        for clause_idx in self.arena.active_indices() {
            if self.arena.is_dead(clause_idx) || self.arena.is_learned(clause_idx) {
                continue;
            }
            clauses.push(self.arena.literals(clause_idx).to_vec());
            clause_offsets.push(clause_idx);
        }

        (clauses, clause_offsets)
    }
}
