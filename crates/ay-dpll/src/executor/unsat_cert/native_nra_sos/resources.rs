// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Caller-metered copying of an existing exact-source SOS bundle seal.

use super::*;
use ay_proof::ProofCheckError;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

fn charge(progress: Progress<'_>, work: usize) -> Result<(), ProofCheckError> {
    if progress(work, 0) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn prepay_scope(
    state: &StrictNativeNraSosBundleState,
    executor: &Executor,
    epoch: &UnsatQueryEpoch,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    let scope = &state.scope;
    // Plain-query checks exclude objectives/extensions before this function.
    // All remaining equality operands are fixed-size IDs or birth stamps.
    let lengths = [
        scope.assertions.len(),
        scope.assertion_entries.len(),
        scope.assumptions.len(),
        scope.assumption_entries.len(),
        scope.solver_assumptions.as_deref().map_or(0, <[_]>::len),
        scope
            .solver_assumption_entries
            .as_deref()
            .map_or(0, <[_]>::len),
        executor.last_assumptions.as_deref().map_or(0, <[_]>::len),
        epoch.assertions.len(),
        epoch.assertion_entries.len(),
        epoch.assumptions.as_deref().map_or(0, <[_]>::len),
        epoch.assumption_entries.as_deref().map_or(0, <[_]>::len),
        executor
            .proof_problem_assertion_provenance
            .as_ref()
            .map_or(0, |source| source.original_problem_assertions.len()),
    ];
    let count = lengths
        .into_iter()
        .try_fold(1usize, usize::checked_add)
        .and_then(|count| count.checked_mul(8))
        .ok_or(ProofCheckError::ResourceLimit)?;
    charge(progress, count)
}

impl StrictNativeNraSosBundleState {
    fn is_current_with_progress(
        &self,
        executor: &Executor,
        proof: &Proof,
        progress: Progress<'_>,
    ) -> Result<bool, ProofCheckError> {
        if !executor.plain_unsat_query_epoch_is_current_with_resource_control(progress)?
            || !self.scope.declared_extension.is_empty()
            || !self.scope.declared_extension_entries.is_empty()
            || self.scope.declared_extension_objectives.is_some()
            || self.scope.declared_extension_objective_entries.is_some()
        {
            return Ok(false);
        }
        let Some(epoch) = executor.unsat_query_epoch.as_ref() else {
            return Ok(false);
        };
        prepay_scope(self, executor, epoch, progress)?;
        if !self.scope.is_current(executor)
            || !plain_epoch_is_current(executor, &self.scope.assumptions)
            || !self
                .evidence
                .is_current_for_with_progress(
                    &executor.ctx.terms,
                    &self.scope.assertions,
                    &self.scope.assumptions,
                    progress,
                )
                .map_err(|_| ProofCheckError::ResourceLimit)?
            || !proof.named_steps.is_empty()
        {
            return Ok(false);
        }
        self.bundle.proof_steps_match_with_progress(proof, progress)
    }
}

impl Executor {
    /// A stale/refused selected SOS state never becomes generic-export authority.
    pub(crate) fn export_strict_native_nra_sos_bundle_for_proof_with_progress(
        &self,
        proof: &Proof,
        progress: Progress<'_>,
    ) -> Result<Option<SerializableProofBundle>, ProofCheckError> {
        charge(progress, 0)?;
        let Some(state) = self.last_strict_native_nra_sos_bundle.as_ref() else {
            return Ok(None);
        };
        if !state.is_current_with_progress(self, proof, progress)? {
            return Ok(None);
        }
        let copied = state.bundle.try_clone_with_progress(progress)?;
        charge(progress, 0)?;
        Ok(Some(copied))
    }
}

#[cfg(test)]
mod tests;
