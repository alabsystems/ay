// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Caller-metered export of an existing immutable BV/LIA seal.

use super::*;
use ay_core::{Constant, Sort, TermStore};
use ay_proof::ProofCheckError;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

fn charge(progress: Progress<'_>, work: usize) -> Result<(), ProofCheckError> {
    if progress(work, 0) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn prepay_source(
    state: &StrictNativeBvLiaBundleState,
    executor: &Executor,
    epoch: &UnsatQueryEpoch,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    // Only fixed-size IDs/stamps occur here. Eight passes conservatively cover
    // the repeated legacy epoch, provenance, partition and entry comparisons.
    let lengths = [
        state.exact_roots.len(),
        state.proof_roots.len(),
        state.bundle.obligation_assertions.len(),
        state.solver_assumptions.as_deref().map_or(0, <[_]>::len),
        state
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

/// Borrowed equivalent of collect_bounded_bv_lia_roots: same live-Bool checks,
/// true removal, stable first-use deduplication and existing root cap.
fn normalized_roots_match(
    terms: &TermStore,
    exact: &[TermId],
    expected: &[TermId],
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    charge(progress, 1)?;
    let mut count = 0;
    for (index, &root) in exact.iter().enumerate() {
        charge(progress, 1)?;
        if terms.entry_stamp(root).is_none() || !matches!(terms.sort(root), Sort::Bool) {
            return Ok(false);
        }
        if matches!(terms.get(root), TermData::Const(Constant::Bool(true))) {
            continue;
        }
        let mut duplicate = false;
        for &prior in &exact[..index] {
            charge(progress, 1)?;
            if prior == root {
                duplicate = true;
                break;
            }
        }
        if duplicate {
            continue;
        }
        if count == ay_proof::MAX_BV_LIA_QUERY_ROOTS || expected.get(count) != Some(&root) {
            return Ok(false);
        }
        count += 1;
    }
    charge(progress, 0)?;
    Ok(count == expected.len())
}

impl StrictNativeBvLiaBundleState {
    fn source_is_current_with_progress(
        &self,
        executor: &Executor,
        progress: Progress<'_>,
    ) -> Result<bool, ProofCheckError> {
        if !executor.plain_unsat_query_epoch_is_current_with_resource_control(progress)? {
            return Ok(false);
        }
        let Some(epoch) = executor.unsat_query_epoch.as_ref() else {
            return Ok(false);
        };
        let Some(assumptions) = epoch.assumptions.as_deref() else {
            return Ok(false);
        };
        prepay_source(self, executor, epoch, progress)?;
        Ok(self
            .authority_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.authority_epoch.is_same_epoch(&epoch.authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.source_context_stamp == epoch.source_context_stamp
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
            && plain_epoch_is_current(executor, epoch, assumptions)
            && self.solver_assumptions.as_deref() == executor.last_assumptions.as_deref()
            && match (
                self.solver_assumptions.as_deref(),
                self.solver_assumption_entries.as_deref(),
            ) {
                (Some(roots), Some(entries)) => {
                    entries.len() == roots.len()
                        && entries.iter().copied().map(Some).eq(roots
                            .iter()
                            .map(|&root| executor.ctx.terms.entry_stamp(root)))
                }
                (None, None) => true,
                _ => false,
            }
            && exact_roots_match_epoch(&self.exact_roots, epoch, assumptions))
    }

    fn proof_is_current_with_progress(
        &self,
        executor: &Executor,
        proof: &Proof,
        progress: Progress<'_>,
    ) -> Result<bool, ProofCheckError> {
        if !proof.named_steps.is_empty()
            || !self
                .bundle
                .proof_steps_match_with_progress(proof, progress)?
        {
            return Ok(false);
        }
        let Some(live) = executor.last_proof.as_ref() else {
            return Ok(false);
        };
        if !normalized_roots_match(
            &executor.ctx.terms,
            &self.exact_roots,
            &self.proof_roots,
            progress,
        )? || !self
            .bundle
            .proof_steps_match_with_progress(live, progress)?
        {
            return Ok(false);
        }
        // The canonical shape check compares all suffix clauses: at most n²
        // fixed TermIds plus linear metadata. Nested step payloads were priced
        // above; preserve the existing canonical validator verbatim.
        let n = self.proof_roots.len();
        let work = n
            .checked_mul(n)
            .and_then(|square| {
                n.checked_mul(16)
                    .and_then(|linear| square.checked_add(linear))
            })
            .and_then(|work| work.checked_add(16))
            .ok_or(ProofCheckError::ResourceLimit)?;
        charge(progress, work)?;
        if !canonical::canonical_bv_lia_proof_matches(executor, live, &self.proof_roots)
            || self.bundle.obligation_assertions != self.exact_roots.as_ref()
            || !executor
                .ctx
                .terms
                .snapshot_entries_match_with_progress(&self.bundle.term_entries, progress)
                .map_err(|_| ProofCheckError::ResourceLimit)?
        {
            return Ok(false);
        }
        Ok(
            self.bundle.true_term == Some(executor.ctx.terms.true_term())
                && self.bundle.false_term == Some(executor.ctx.terms.false_term())
                && self.bundle.var_counter == executor.ctx.terms.var_counter()
                && self.bundle.datatype_declarations.is_empty()
                && self.bundle.constructor_selectors.is_empty()
                && self.bundle.datatype_member_signatures.is_empty(),
        )
    }
}

impl Executor {
    /// Copy only the selected, still-current sealed state. None is terminal for
    /// this lane, never permission to fall back to a generic proof export.
    pub(crate) fn export_strict_native_bv_lia_bundle_for_proof_with_progress(
        &self,
        proof: &Proof,
        progress: Progress<'_>,
    ) -> Result<Option<SerializableProofBundle>, ProofCheckError> {
        charge(progress, 0)?;
        let Some(state) = self.last_strict_native_bv_lia_bundle.as_ref() else {
            return Ok(None);
        };
        if !state.source_is_current_with_progress(self, progress)?
            || !state.proof_is_current_with_progress(self, proof, progress)?
        {
            return Ok(None);
        }
        let copied = state.bundle.try_clone_with_progress(progress)?;
        charge(progress, 0)?;
        Ok(Some(copied))
    }
}

#[cfg(test)]
mod tests;
