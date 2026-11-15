// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One cumulative resource owner across exact-query export and both rechecks.

use super::{ExactSmtlibQueryBinding, Solver};
use ay_core::TermId;
use ay_proof::{
    re_check_bundle_strict_with_resource_control, ProofCheckError, SerializableProofBundle,
};

mod construction;
mod control;
mod retained;
use control::Control;

impl Solver {
    /// Export an exact-query proof under one caller-owned resource callback.
    ///
    /// This preserves the binding and two independent strict checks of
    /// [`Self::export_last_unsat_bundle_for_exact_query`]. Source authentication,
    /// retained solver term storage, declaration and bundle copies, checked assumption narrowing, and both
    /// replays debit the SAME callback. Refusal is sticky and a refusal the
    /// export observed fails it; the callback is not consulted once the export
    /// has completed, so a late stop never discards a checked bundle. A
    /// present stale sealed route never falls through to generic proof
    /// reconstruction.
    ///
    /// `Ok(None)` declines missing/stale authority; errors include independent
    /// checker rejection and `ProofCheckError::ResourceLimit`. Neither grants
    /// an UNSAT certificate. The caller retains its cumulative allowance for
    /// later consumer rechecks. This is not a complete allocator/RSS bound or
    /// hard cancellation-latency guarantee; parsing, rendering, individual
    /// arithmetic/allocation/destruction intervals remain separate work.
    pub fn export_last_unsat_bundle_for_exact_query_with_resource_control(
        &self,
        binding: &ExactSmtlibQueryBinding,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<SerializableProofBundle>, ProofCheckError> {
        Control::new(progress).run(|control| export(self, binding, control))
    }
}

fn resolve_roots(
    solver: &Solver,
    binding: &ExactSmtlibQueryBinding,
    control: &mut Control<'_>,
) -> Result<Option<Vec<TermId>>, ProofCheckError> {
    control.charge(1, 0)?;
    if !binding.solver.is_current()
        || binding.solver != solver.cache_token
        || binding.assertions.is_empty()
    {
        return Ok(None);
    }
    // The live solver survives all export/replay phases. Account its existing
    // term-store ledger before allocating export-owned storage; this is not a
    // price for SAT caches, parser buffers, or the whole process.
    control.charge(0, solver.terms().true_memory_bytes())?;
    let bytes = binding
        .assertions
        .len()
        .checked_mul(std::mem::size_of::<TermId>())
        .ok_or(ProofCheckError::ResourceLimit)?;
    control.charge(binding.assertions.len(), bytes)?;
    let mut roots = Vec::new();
    roots
        .try_reserve_exact(binding.assertions.len())
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    for &term in &binding.assertions {
        control.charge(1, 0)?;
        let Ok(root) = solver.resolve_term(
            "export_last_unsat_bundle_for_exact_query_with_resource_control",
            term,
        ) else {
            return Ok(None);
        };
        roots.push(root);
    }
    Ok(Some(roots))
}

fn export(
    solver: &Solver,
    binding: &ExactSmtlibQueryBinding,
    control: &mut Control<'_>,
) -> Result<Option<SerializableProofBundle>, ProofCheckError> {
    let Some(roots) = resolve_roots(solver, binding, control)? else {
        return Ok(None);
    };
    let Some(source) = solver
        .executor
        .exact_plain_query_proof_source_with_resource_control(
            &roots,
            &binding.source_context,
            &mut |w, b| control.charge(w, b).is_ok(),
        )?
    else {
        return Ok(None);
    };
    let allowed =
        source.source_closure_with_resource_control(&mut |w, b| control.charge(w, b).is_ok())?;
    let proof = source.proof();
    let mut progress = |w, b| control.charge(w, b).is_ok();
    let bundle = construction::bundle(
        solver,
        proof,
        |progress| source.complete_problem_with_resource_control(progress),
        &mut progress,
    )?;
    let Some(mut bundle) = bundle else {
        return Ok(None);
    };
    let checked = re_check_bundle_strict_with_resource_control(&bundle, &mut progress)?;
    if !checked.quality.is_complete()
        || checked.assume_terms.is_empty()
        || !control.all_ids_in(&checked.assume_terms, &allowed)?
    {
        return Ok(None);
    }
    bundle.obligation_assertions = control.ordered_unique_ids(&checked.assume_terms)?;
    let rebound = re_check_bundle_strict_with_resource_control(&bundle, &mut |w, b| {
        control.charge(w, b).is_ok()
    })?;
    if !rebound.quality.is_complete()
        || rebound.assume_terms.is_empty()
        || !control.all_ids_in(&rebound.assume_terms, &bundle.obligation_assertions)?
    {
        return Ok(None);
    }
    Ok(Some(bundle))
}

#[cfg(test)]
mod tests;
