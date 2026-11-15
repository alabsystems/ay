// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Scoped exact export/consumption on the caller's existing work adapter.

use super::{export_retained, ExactSmtlibQueryBinding, Solver};
use ay_core::{original_query::WorkBudget, time::Instant};
use ay_proof::{ProofCheckError, RetainedProofBundle};

impl Solver {
    /// Prepare, independently check and consume exact retained evidence using
    /// the SAME borrowed work/copy owner. The producer deadline only tightens
    /// the original end enforced by that owner's admission callback.
    ///
    /// Every existing actual `(work, bytes)` offer, including zero polls, is
    /// forwarded before work. Internal allocation/overflow/deadline refusals
    /// also latch this adapter, even if no offer caused them. With an adapter
    /// from OriginalAdmission::with_work, clones and later calls cannot renew
    /// that first refusal. This does not create or install a solver owner.
    ///
    /// The unit-returning consumer borrows the retained bundle and SAME work.
    /// Bundle/report scratch drops BEFORE terminal admission. Unit prevents a
    /// carrier in the normal result, not callback side-channel export; any
    /// caller-retained payload and its later disposal remain caller-owned.
    /// `Ok(None)` is missing/stale authority, not UNSAT or budget exhaustion.
    /// A newly observed stop refuses this consumption, not an earlier completed
    /// proof fact. Producer parsing/native solve and caller preparation remain
    /// outside; existing bounded payload clones/allocator/destructor intervals
    /// are priced logical copies, not fully fallible or preemptible execution.
    pub fn with_last_unsat_retained_bundle_for_exact_query_with_work<'owner>(
        &self,
        binding: &ExactSmtlibQueryBinding,
        deadline: Instant,
        work: &mut WorkBudget<'owner>,
        consume: impl FnOnce(
            &RetainedProofBundle,
            &mut WorkBudget<'owner>,
        ) -> Result<(), ProofCheckError>,
    ) -> Result<Option<()>, ProofCheckError> {
        let result = scoped(self, binding, deadline, work, consume);
        let terminal = matches!(
            &result,
            Err(ProofCheckError::ResourceLimit | ProofCheckError::Cancelled)
        );
        if terminal {
            work.refuse_exhaustion();
        }
        // The scoped operation has dropped its bundle and callback owners.
        // Preserve the original precise stop in WorkBudget, never guess it from
        // the checker's deliberately unclassified ResourceLimit result.
        if work.charge(0).is_err() && !terminal {
            return Err(ProofCheckError::ResourceLimit);
        }
        if result.is_ok() && Instant::now() >= deadline {
            // This may be a tighter producer end than the owner's end. The
            // owner cannot be renewed after that observed terminal ceiling.
            work.refuse_exhaustion();
            return Err(ProofCheckError::Cancelled);
        }
        result
    }
}

fn scoped<'owner>(
    solver: &Solver,
    binding: &ExactSmtlibQueryBinding,
    deadline: Instant,
    work: &mut WorkBudget<'owner>,
    consume: impl FnOnce(&RetainedProofBundle, &mut WorkBudget<'owner>) -> Result<(), ProofCheckError>,
) -> Result<Option<()>, ProofCheckError> {
    // Fixed stack-only adapter bookkeeping, not a replacement checker grant.
    work.charge(8).map_err(|_| ProofCheckError::ResourceLimit)?;
    let artifact = export_retained(solver, binding, deadline, &mut |units, bytes| {
        work.admit(units, bytes).is_ok()
    })?;
    let Some(artifact) = artifact else {
        return Ok(None);
    };
    work.charge(0).map_err(|_| ProofCheckError::ResourceLimit)?;
    if Instant::now() >= deadline {
        return Err(ProofCheckError::Cancelled);
    }
    let result = consume(&artifact, work);
    drop(artifact);
    result.map(|()| Some(()))
}
