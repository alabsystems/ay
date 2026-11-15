// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked SOS refutations of exact AST queries, not executor publication authority.
//!
//! Source binding and snapshot copies debit the supplied callback. Replay forwards
//! that SAME callback to the bounded independent SOS kernel. This is not yet an
//! all-allocation accounting contract: the existing kernel has uncharged shape/
//! polynomial scans, rational comparisons and error-string allocations. It is not
//! a substitute for the unfinished generic caller-metered bundle replay API.

use ay_core::{
    term::TermStoreSnapshotStamp, NraSosCertificate, ProofId, ProofStep, TermId, TermStore,
};
use std::mem::size_of;

use crate::checker::{validate_nra_sos_with_progress, ProofCheckError};

mod source;
#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;
type CheckResult<T> = Result<T, NraSosQueryCheckError>;

/// A refusal to check a candidate against the exact supplied AST query.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum NraSosQueryCheckError {
    /// The caller refused, a fixed resource limit fired, or allocation failed.
    #[error("SOS query checking exhausted its resource envelope")]
    ResourceLimit,
    /// The supplied proof step is not the dedicated SOS variant.
    #[error("the candidate is not an NRA SOS step")]
    NotSos,
    /// The empty conjunction cannot be refuted by this interface.
    #[error("the SOS query has no assertions or assumptions")]
    EmptyQuery,
    /// Every assertion and assumption must have exactly one conclusion slot.
    #[error("the SOS clause length does not match the exact query")]
    SourceArity,
    /// A supplied root or conclusion literal is outside the arena.
    #[error("SOS query root {root:?} is outside the term store")]
    InvalidRoot {
        /// Missing term handle.
        root: TermId,
    },
    /// A query root or conclusion literal lacks Boolean recorded sort.
    #[error("SOS query root {root:?} is not Boolean")]
    NonBooleanRoot {
        /// Mistyped term handle.
        root: TermId,
    },
    /// A clause slot is not the raw negation of its exact query root.
    #[error("SOS clause slot {position} does not negate its exact source root")]
    SourceMismatch {
        /// Zero-based position in assertions followed by assumptions.
        position: usize,
    },
    /// Independent source parsing or exact certificate replay rejected the step.
    #[error(transparent)]
    Kernel(ProofCheckError),
}

/// Move-only evidence of a refutation of one exact, ordered AST query.
///
/// This is NOT public `UNSAT` authority, an authenticated SMT problem, or an
/// exportable proof. Numeric named operators use AY's builtin interpretation;
/// the caller must separately authenticate declarations (including rejecting
/// builtin-name collisions), the source-context stamp, and the active query
/// epoch. No caller-supplied assertion becomes an authorized problem assumption
/// merely because this checker received it.
#[derive(Debug)]
pub struct CheckedNraSosQuery {
    term_snapshot: TermStoreSnapshotStamp,
    metadata_generation: u64,
    boolean_ids: (Option<TermId>, Option<TermId>),
    var_counter: u32,
    assertions: Vec<TermId>,
    assumptions: Vec<TermId>,
}

impl CheckedNraSosQuery {
    /// Test exact arena/metadata identity and both ordered source partitions.
    ///
    /// A match says nothing about frontend declarations or query ownership.
    /// Even moving a root across the assertion/assumption boundary is a mismatch.
    /// All scans and the final control poll use the supplied cumulative callback.
    pub fn is_current_for_with_progress(
        &self,
        terms: &TermStore,
        assertions: &[TermId],
        assumptions: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, NraSosQueryCheckError> {
        with_sticky_progress(progress, |progress| {
            charge(progress, 6, 0)?;
            let mut current = self.term_snapshot == terms.snapshot_stamp()
                && self.metadata_generation == terms.checker_visible_metadata_generation()
                && self.boolean_ids == terms.boolean_constant_ids()
                && self.var_counter == terms.var_counter()
                && self.assertions.len() == assertions.len()
                && self.assumptions.len() == assumptions.len();
            if current {
                for (stored, supplied) in self
                    .assertions
                    .iter()
                    .chain(&self.assumptions)
                    .zip(assertions.iter().chain(assumptions))
                {
                    charge(progress, 1, 0)?;
                    if stored != supplied {
                        current = false;
                        break;
                    }
                }
            }
            charge(progress, 0, 0)?;
            Ok(current)
        })
    }
}

/// Check an SOS candidate against assertions followed by assumptions, in order.
///
/// Each candidate clause slot must be `TermData::Not(root)` for its exact source
/// slot. Constants and duplicates remain slots; polarity is not simplified.
/// All handles refer to `terms`, including raw complement nodes already present
/// in that arena. The source/candidate are borrowed and never rewritten.
///
/// Replay uses a fresh, positional checker-only copy with the source's raw
/// optional Boolean IDs unchanged. Unused entries are copied but not asserted
/// to be well typed; no general bundle or declaration authentication is implied.
/// A returned token binds the ORIGINAL arena and its metadata, not the copy.
///
/// The callback is shared across binding, copying, replay and evidence creation;
/// a refusal is sticky and a final poll precedes success. Wrapper-owned work and
/// allocations are precharged. Existing SOS-kernel accounting is forwarded as
/// implemented: its certificate-shape and polynomial-bound scans, rational
/// comparisons, and error-string construction still have uncharged work or
/// allocations. This interface does not promise complete accounting of every
/// kernel operation or allocation, nor meter generic proof/bundle replay.
pub fn check_nra_sos_query_with_progress(
    terms: &TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    candidate: &ProofStep,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<CheckedNraSosQuery, NraSosQueryCheckError> {
    with_sticky_progress(progress, |progress| {
        charge(progress, 1, 0)?;
        let ProofStep::NraSos {
            clause,
            certificate,
        } = candidate
        else {
            return Err(NraSosQueryCheckError::NotSos);
        };
        source::validate_bindings(terms, assertions, assumptions, clause, progress)?;
        let snapshot = source::fresh_snapshot(terms, progress)?;
        validate_nra_sos_with_progress(&snapshot, ProofId(0), clause, certificate, progress)
            .map_err(|error| match error {
                ProofCheckError::ResourceLimit => NraSosQueryCheckError::ResourceLimit,
                other => NraSosQueryCheckError::Kernel(other),
            })?;
        charge(progress, 6, size_of::<CheckedNraSosQuery>())?;
        let checked = CheckedNraSosQuery {
            term_snapshot: terms.snapshot_stamp(),
            metadata_generation: terms.checker_visible_metadata_generation(),
            boolean_ids: terms.boolean_constant_ids(),
            var_counter: terms.var_counter(),
            assertions: copy_roots(assertions, progress)?,
            assumptions: copy_roots(assumptions, progress)?,
        };
        charge(progress, 0, 0)?;
        Ok(checked)
    })
}

fn copy_roots(roots: &[TermId], progress: Progress<'_>) -> CheckResult<Vec<TermId>> {
    let bytes = roots
        .len()
        .checked_mul(size_of::<TermId>())
        .ok_or(NraSosQueryCheckError::ResourceLimit)?;
    charge(progress, roots.len(), bytes)?;
    let mut copied = Vec::new();
    copied
        .try_reserve_exact(roots.len())
        .map_err(|_| NraSosQueryCheckError::ResourceLimit)?;
    copied.extend_from_slice(roots);
    Ok(copied)
}

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> CheckResult<()> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(NraSosQueryCheckError::ResourceLimit)
    }
}

fn with_sticky_progress<T>(
    progress: Progress<'_>,
    run: impl FnOnce(Progress<'_>) -> CheckResult<T>,
) -> CheckResult<T> {
    let mut refused = false;
    let outcome = run(&mut |work, bytes| {
        if refused {
            return false;
        }
        refused = !progress(work, bytes);
        !refused
    });
    if refused {
        Err(NraSosQueryCheckError::ResourceLimit)
    } else {
        outcome
    }
}
