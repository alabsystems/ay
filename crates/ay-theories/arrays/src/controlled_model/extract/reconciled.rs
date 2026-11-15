// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete prepared flat array DATA; no cache replay or solve authority.

use super::*;
use ay_core::term::{Constant, Symbol};
use std::mem::size_of;

mod chains;
mod compare;
mod defaults;
mod initial;
mod propagate;
mod reconcile;
mod shape;
mod storage;
#[cfg(test)]
mod tests;

impl ArraySolver<'_> {
    /// Extract the already-current flat Bool/BV1..128 builtin cohort under
    /// the SAME original ledger, including store-bearing classes and default
    /// fixpoints. Dirty/cold caches, opaque functions, nested arrays, binders
    /// and unsupported scalar domains terminally refuse, without fallback.
    ///
    /// Original newest-first rows, soft/read conflicts, ordered class winners
    /// and the optional reconciled candidate retain legacy DATA semantics.
    /// This does not prepare caches, attach an owner to a solver, certify a
    /// model, or price later caller access/clone/export/output disposal.
    pub fn try_extract_prepared_flat_model_with_budget(
        &self,
        values: &HashMap<TermId, String>,
        work: &mut WorkBudget<'_>,
    ) -> Result<ArrayModel, QueryError> {
        let result = extract(self, values, work);
        owned::finish(result, work)
    }
}

fn extract(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    work: &mut WorkBudget<'_>,
) -> Result<ArrayModel, QueryError> {
    shape::prepared(solver, work)?;
    let binding = shape::Binding::capture(solver, work)?;
    let plan = if solver.eq_adj.is_empty() {
        None
    } else {
        Some(classes::prepare_reconciled(solver, work)?)
    };
    let mut state = initial::build(solver, values, work)?;
    if let Some(plan) = &plan {
        propagate::apply(plan, solver, &mut state, work)?;
        // Replay the complete insertion log with single-entry growth. This
        // preserves the legacy clone's bucket/iteration layout without Clone.
        let mut candidate = storage::copy(&state, work)?;
        reconcile::apply(plan, solver, values, &mut candidate, work)?;
        defaults::fill(plan, solver, &mut candidate.model, work)?;
        defaults::fill(plan, solver, &mut state.model, work)?;
        if !compare::maps(
            &candidate.model.array_values,
            &state.model.array_values,
            work,
        )? {
            work.charge(16)?;
            state.model.store_chain_class_candidate =
                Some(std::mem::take(&mut candidate.model.array_values));
        }
        work.charge(candidate.order.len() + 1)?;
        drop(candidate);
    }
    if let Some(plan) = plan {
        plan.finish(work)?;
    }
    binding.verify(solver, work)?;
    work.charge(state.order.len() + 1)?;
    drop(state.order);
    drop(binding);
    work.charge(0)?;
    Ok(state.model)
}
