// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact live-source authentication around the two opaque retained phases.

use super::{construction, resolve_roots, Control, ExactSmtlibQueryBinding, Solver};
use ay_core::time::Instant;
use ay_proof::{
    capture_strict_retained_bundle_with_resource_control, ProofCheckError, RetainedProofBundle,
};

mod work;

impl Solver {
    /// Export an owning v4 retained bundle authenticated to this live query.
    ///
    /// Unlike the unchanged v3 sibling, the first complete check captures the
    /// required retained evidence. Its immutable assumption report must bind
    /// to the live exact-query source closure before a consuming second,
    /// independent no-search replay narrows and admits the actual v4 artifact.
    /// A producer-controlled snapshot alone is never source authority.
    ///
    /// `deadline` is the original absolute producer deadline, not a new budget
    /// per phase. Source authentication, typed copies, both checks, narrowing
    /// and local-owner cleanup share the SAME caller-owned sticky callback.
    /// Later artifact encoding/replay must use that same cumulative ledger;
    /// this export does not claim to own the complete CHC or process budget.
    /// Missing/stale authority returns `Ok(None)`; a selected stale sealed
    /// route never falls through to generic construction or raw-v3 export.
    pub fn export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
        &self,
        binding: &ExactSmtlibQueryBinding,
        deadline: Instant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<RetainedProofBundle>, ProofCheckError> {
        export_retained(self, binding, deadline, progress)
    }
}

fn export_retained(
    solver: &Solver,
    binding: &ExactSmtlibQueryBinding,
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<RetainedProofBundle>, ProofCheckError> {
    let mut original_deadline = |work, bytes| {
        Instant::now() < deadline && progress(work, bytes) && Instant::now() < deadline
    };
    Control::new(&mut original_deadline)
        .run_retained(|control| export(solver, binding, deadline, control))
}

fn export(
    solver: &Solver,
    binding: &ExactSmtlibQueryBinding,
    deadline: Instant,
    control: &mut Control<'_>,
) -> Result<Option<RetainedProofBundle>, ProofCheckError> {
    let Some(roots) = resolve_roots(solver, binding, control)? else {
        return Ok(None);
    };
    let Some(source) = solver
        .executor
        .exact_plain_query_proof_source_with_resource_control(
            &roots,
            &binding.source_context,
            &mut |work, bytes| control.charge(work, bytes).is_ok(),
        )?
    else {
        return Ok(None);
    };
    let allowed = source.source_closure_with_resource_control(&mut |work, bytes| {
        control.charge(work, bytes).is_ok()
    })?;
    let Some(snapshot) = construction::bundle(
        solver,
        source.proof(),
        |progress| source.complete_problem_with_resource_control(progress),
        &mut |work, bytes| control.charge(work, bytes).is_ok(),
    )?
    else {
        return Ok(None);
    };
    let capture = capture_strict_retained_bundle_with_resource_control(
        snapshot,
        deadline,
        &mut |work, bytes| control.charge(work, bytes).is_ok(),
    )?;
    let first = capture.first_check();
    if !first.quality.is_complete()
        || first.assume_terms.is_empty()
        || !control.all_ids_in(&first.assume_terms, &allowed)?
    {
        return Ok(None);
    }
    let (artifact, second) = capture.finish_exact_with_resource_control(&mut |work, bytes| {
        control.charge(work, bytes).is_ok()
    })?;
    let assertions = artifact.obligation_assertions();
    if !second.quality.is_complete()
        || second.assume_terms.is_empty()
        || assertions.is_empty()
        || !control.all_ids_in(&second.assume_terms, assertions)?
        || !control.all_ids_in(assertions, &second.assume_terms)?
    {
        return Ok(None);
    }
    // The live source view, closure, roots and second report drop in this
    // operation before Control::run_retained's terminal publication poll.
    Ok(Some(artifact))
}

#[cfg(test)]
mod tests;
