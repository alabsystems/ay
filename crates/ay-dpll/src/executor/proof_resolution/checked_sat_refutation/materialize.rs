// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Optional native proof reconstruction from an already authenticated RUP DAG.
//! The caller retains the checked verdict even when this bounded export declines.

use super::*;

mod rup;
mod scope;

const MAX_CLAUSES: usize = 4096;
const MAX_VARIABLES: usize = 8192;
const MAX_LITERALS: usize = 128;
const MAX_HINTS: usize = 16384;
const MAX_STEPS: usize = 32768;

fn reserve<T>(count: usize, meter: &mut CheckedRefutationMeter) -> Option<Vec<T>> {
    meter
        .charge(count, count.checked_mul(size_of::<T>())?)
        .ok()?;
    let mut result = Vec::new();
    result.try_reserve_exact(count).ok()?;
    charge_capacity_excess::<T>(result.capacity(), count, meter).ok()?;
    Some(result)
}

fn preflight(
    fragment: &ExactOriginalProofFragment,
    validated: &ValidatedPremisedClauseTraceResolution,
    meter: &mut CheckedRefutationMeter,
) -> Option<usize> {
    meter.charge(1, 0).ok()?;
    let dag = validated.dag();
    let count = dag.original_clauses.len().checked_add(dag.derived.len())?;
    if count > MAX_CLAUSES
        || dag.num_vars > MAX_VARIABLES
        || validated.unit_premises().len() > MAX_VARIABLES
        || fragment.proof().steps.len() > MAX_STEPS
        || dag.empty_clause_id != count as u64
    {
        return None;
    }
    let mut hints = 0usize;
    for (index, (id, clause)) in dag.original_clauses.iter().enumerate() {
        meter.charge(1, 0).ok()?;
        if *id != index as u64 + 1 || clause.len() > MAX_LITERALS {
            return None;
        }
    }
    for (index, row) in dag.derived.iter().enumerate() {
        meter.charge(1, 0).ok()?;
        hints = hints.checked_add(row.rup_hints.len())?;
        if row.id != (dag.original_clauses.len() + index + 1) as u64
            || row.clause.len() > MAX_LITERALS
            || hints > MAX_HINTS
        {
            return None;
        }
    }
    (fragment.proof().steps.len().checked_add(hints)? <= MAX_STEPS).then_some(hints)
}

fn cone(dag: &ResolutionDag, meter: &mut CheckedRefutationMeter) -> Option<Vec<bool>> {
    let count = dag.original_clauses.len().checked_add(dag.derived.len())?;
    let mut needed = reserve(count.checked_add(1)?, meter)?;
    needed.resize(count + 1, false);
    *needed.get_mut(dag.empty_clause_id as usize)? = true;
    for row in dag.derived.iter().rev() {
        meter.charge(1, 0).ok()?;
        if !needed[row.id as usize] {
            continue;
        }
        for &hint in &row.rup_hints {
            meter.charge(1, 0).ok()?;
            if hint == 0 || hint >= row.id {
                return None;
            }
            *needed.get_mut(usize::try_from(hint).ok()?)? = true;
        }
    }
    Some(needed)
}

/// Only the caller's successful exact composition authenticates the fragment's
/// original bindings. The result still needs a whole-proof strict scope check.
pub(super) fn materialize(
    fragment: ExactOriginalProofFragment,
    validated: &ValidatedPremisedClauseTraceResolution,
    var_to_term: &HashMap<u32, TermId>,
    terms: &mut TermStore,
    meter: &mut CheckedRefutationMeter,
) -> Option<Proof> {
    let hints = preflight(&fragment, validated, meter)?;
    let dag = validated.dag();
    let needed = cone(dag, meter)?;
    let count = needed.len();
    let mut ids = reserve(count, meter)?;
    ids.resize(count, None);
    let mut clauses = reserve(count, meter)?;
    let projected = scope::project(validated, &needed, var_to_term, meter)?;
    for clause in &projected {
        meter.charge(1, 0).ok()?;
        clauses.push(clause.as_slice());
    }
    for mapping in validated.original_mappings() {
        meter.charge(1, 0).ok()?;
        let id = usize::try_from(mapping.canonical_id()).ok()?;
        if *needed.get(id)? {
            ids[id] = Some(fragment.binding(mapping.trace_id())?.proof_id());
        }
    }
    // Move the authenticated proof instead of cloning its terms and annotations.
    let mut proof = fragment.into_proof();
    let requested = proof.steps.len().checked_add(hints)?;
    meter
        .charge(requested, requested.checked_mul(size_of::<ProofStep>())?)
        .ok()?;
    proof.steps.try_reserve_exact(hints).ok()?;
    if proof.steps.capacity() > requested {
        meter
            .charge(
                0,
                (proof.steps.capacity() - requested).checked_mul(size_of::<ProofStep>())?,
            )
            .ok()?;
    }
    for row in &dag.derived {
        meter.charge(1, 0).ok()?;
        if needed[row.id as usize] {
            ids[row.id as usize] = Some(rup::expand(
                row,
                &clauses,
                &ids,
                dag.num_vars,
                &mut proof,
                var_to_term,
                terms,
                meter,
            )?);
        }
    }
    meter.charge(1, 0).ok()?;
    let last = ids.get(dag.empty_clause_id as usize).copied().flatten()?;
    // A fragment may contain unrelated later steps. Require the actual final
    // native step to be the derived empty clause before returning the candidate.
    if last.0 as usize + 1 != proof.steps.len() {
        return None;
    }
    Some(proof)
}

#[cfg(test)]
mod tests;
