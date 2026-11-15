// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed, metered source authentication for an exact plain-query export.

use super::*;
use ay_core::Proof;
use ay_proof::ProofCheckError;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

/// This view authenticates source membership, not proof validity. The caller
/// must still check the complete proof and its actual assumptions independently.
pub(crate) struct ExactQueryProofSource<'a> {
    proof: &'a Proof,
    sources: [&'a [TermId]; 4],
    self_check_authored: &'a [TermId],
    excluded_false: Option<TermId>,
}

#[derive(Clone, Copy)]
enum Inventory {
    ExactClosure,
    CompleteProblem,
}

impl<'a> ExactQueryProofSource<'a> {
    pub(crate) fn proof(&self) -> &'a Proof {
        self.proof
    }

    /// Preserve the legacy source closure's order and stable deduplication.
    /// Every comparison is metered; no hash table or source copy precedes its
    /// debit. A refusal drops the local output without mutating the executor.
    pub(crate) fn source_closure_with_resource_control(
        &self,
        progress: Progress<'_>,
    ) -> Result<Vec<TermId>, ProofCheckError> {
        self.collect(Inventory::ExactClosure, progress)
    }

    /// Full strict-check freshness scope, deliberately distinct from the
    /// authorization closure. Preserve initial problem-row duplicates and add
    /// self-check originals, exactly as the legacy complete-scope collector.
    /// Declared obligation extensions were excluded before minting this view.
    pub(crate) fn complete_problem_with_resource_control(
        &self,
        progress: Progress<'_>,
    ) -> Result<Vec<TermId>, ProofCheckError> {
        self.collect(Inventory::CompleteProblem, progress)
    }

    fn collect(
        &self,
        inventory: Inventory,
        progress: Progress<'_>,
    ) -> Result<Vec<TermId>, ProofCheckError> {
        charge(progress, 0, 0)?;
        let authored = match inventory {
            Inventory::ExactClosure => &[],
            Inventory::CompleteProblem => self.self_check_authored,
        };
        let sources = [
            self.sources[0],
            self.sources[1],
            self.sources[2],
            self.sources[3],
            authored,
        ];
        let count = sources
            .iter()
            .try_fold(0usize, |total, slice| total.checked_add(slice.len()));
        let count = count.ok_or(ProofCheckError::ResourceLimit)?;
        let bytes = count
            .checked_mul(std::mem::size_of::<TermId>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        charge(progress, count, bytes)?;
        let mut closure = Vec::new();
        closure
            .try_reserve_exact(count)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        for (index, source) in sources.iter().enumerate() {
            for &term in *source {
                charge(progress, 1, 0)?;
                if index < 4 && Some(term) == self.excluded_false {
                    continue;
                }
                let mut present = false;
                if index != 0 || matches!(inventory, Inventory::ExactClosure) {
                    for &previous in &closure {
                        charge(progress, 1, 0)?;
                        if previous == term {
                            present = true;
                            break;
                        }
                    }
                }
                if !present {
                    closure.push(term);
                }
            }
        }
        charge(progress, 0, 0)?;
        Ok(closure)
    }
}

impl Executor {
    /// O(1) inventory sizes, not an authority check. A caller that repeats a
    /// legacy currentness scan after the metered check can prepay that scan
    /// from the actual epoch rather than a possibly unrelated capability.
    pub(crate) fn unsat_query_epoch_inventory_lengths_for_resource_control(
        &self,
    ) -> Option<(usize, usize)> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        Some((epoch.assertions.len(), epoch.assumptions.as_ref()?.len()))
    }

    /// Meter the actual live epoch inventory before any legacy seal getter
    /// performs its own currentness check. Bound assumptions are allowed here;
    /// exact plain-query export imposes the stricter empty-assumption condition.
    pub(crate) fn plain_unsat_query_epoch_is_current_with_resource_control(
        &self,
        progress: Progress<'_>,
    ) -> Result<bool, ProofCheckError> {
        charge(progress, 0, 0)?;
        let Some(epoch) = self.unsat_query_epoch.as_ref() else {
            return Ok(false);
        };
        if !epoch.declared_extension.is_empty()
            || !epoch.declared_extension_entries.is_empty()
            || epoch.declared_extension_objectives.is_some()
            || epoch.declared_extension_objective_entries.is_some()
            || !epoch
                .authority_epoch
                .is_same_epoch(&self.query_authority_epoch)
            || epoch.source_context_stamp != self.ctx.source_context_stamp()
        {
            return Ok(false);
        }
        let (Some(assumptions), Some(assumption_entries)) = (
            epoch.assumptions.as_deref(),
            epoch.assumption_entries.as_deref(),
        ) else {
            return Ok(false);
        };
        for (roots, entries) in [
            (
                epoch.assertions.as_slice(),
                epoch.assertion_entries.as_slice(),
            ),
            (assumptions, assumption_entries),
        ] {
            if roots.len() != entries.len() {
                return Ok(false);
            }
            for (&root, &entry) in roots.iter().zip(entries) {
                charge(progress, 1, 0)?;
                if self.ctx.terms.entry_stamp(root) != Some(entry) {
                    return Ok(false);
                }
            }
        }
        charge(progress, 0, 0)?;
        Ok(true)
    }

    /// Authenticate the opaque binding and borrow its retained public proof
    /// without invoking an unmetered `last_proof` or source-scope collector.
    /// No fallback to mutable working roots is permitted without provenance.
    pub(crate) fn exact_plain_query_proof_source_with_resource_control(
        &self,
        exact_roots: &[TermId],
        source_context: &SourceContextStamp,
        progress: Progress<'_>,
    ) -> Result<Option<ExactQueryProofSource<'_>>, ProofCheckError> {
        if !self.plain_unsat_query_epoch_is_current_with_resource_control(progress)? {
            return Ok(None);
        }
        let (Some(epoch), Some(provenance), Some(proof)) = (
            self.unsat_query_epoch.as_ref(),
            self.proof_problem_assertion_provenance.as_ref(),
            self.last_proof.as_ref(),
        ) else {
            return Ok(None);
        };
        if !self.last_result_is_unsat()
            || !epoch.proof_output_requested
            || self.last_unsat_proof_reconstruction_suppressed
            || epoch.assumptions.as_deref() != Some(&[])
            || &epoch.source_context_stamp != source_context
        {
            return Ok(None);
        }
        for source in [
            epoch.assertions.as_slice(),
            self.ctx.assertions.as_slice(),
            provenance.original_problem_assertions.as_slice(),
        ] {
            if source.len() != exact_roots.len() {
                return Ok(None);
            }
            for (&actual, &expected) in source.iter().zip(exact_roots) {
                charge(progress, 1, 0)?;
                if actual != expected {
                    return Ok(None);
                }
            }
        }
        let false_term = self.ctx.terms.false_term();
        // With authenticated empty epoch assumptions, the legacy literal-false
        // assumption exception is necessarily false. Preserve compact authored
        // assertion provenance even when parsed-AST retention was disabled.
        let authored_false = self
            .ctx
            .concrete_authored_literal_false_contains_with_progress(false_term, &mut || {
                charge(progress, 1, 0)
            })?;
        let view = ExactQueryProofSource {
            proof,
            sources: [
                &provenance.problem_assertions,
                &provenance.original_problem_assertions,
                &self.last_proof_rebuild_originals,
                self.last_assumptions.as_deref().unwrap_or(&[]),
            ],
            self_check_authored: self
                .self_check_authored_assertions
                .as_deref()
                .unwrap_or(&[]),
            excluded_false: (!authored_false).then_some(false_term),
        };
        let mut nonempty = false;
        for &term in view.sources.iter().flat_map(|slice| slice.iter()) {
            charge(progress, 1, 0)?;
            if Some(term) != view.excluded_false {
                nonempty = true;
                break;
            }
        }
        charge(progress, 0, 0)?;
        Ok(nonempty.then_some(view))
    }
}

#[cfg(test)]
mod tests;
