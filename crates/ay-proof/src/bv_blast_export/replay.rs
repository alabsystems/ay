// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent graph replay with cancellation-only checkpoints.

use super::*;

mod budget;
mod clauses;
mod graph;
mod resolution;
mod sets;

use budget::ReplayBudget;

#[cfg(test)]
mod tests;

pub(super) fn validate(
    proof: &BvBlastProof,
    limits: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(), BvBlastValidateError> {
    let mut budget = ReplayBudget::new(limits, keep_going);
    budget.poll_admission()?;
    validate_inner(proof, &mut budget)?;
    // The graph, clause and resolution scratch frames are gone before the
    // final admission poll; no accepted prefix is returned on refusal.
    budget.poll_admission()
}

pub(super) fn validate_cnf(
    proof: &BvBlastProof,
    limits: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<u64, BvBlastValidateError> {
    let mut budget = ReplayBudget::new(limits, keep_going);
    budget.poll_admission()?;
    preflight(proof, &budget)?;
    let defined_by = graph::definitions(proof, &mut budget)?;
    graph::equality(proof, &defined_by, &mut budget)?;
    clauses::validate(proof, &mut budget)?;
    drop(defined_by);
    budget.poll_admission()?;
    Ok(budget.work())
}

fn validate_inner(
    proof: &BvBlastProof,
    budget: &mut ReplayBudget<'_, '_>,
) -> Result<(), BvBlastValidateError> {
    preflight(proof, budget)?;
    let defined_by = graph::definitions(proof, budget)?;
    graph::equality(proof, &defined_by, budget)?;
    clauses::validate(proof, budget)?;
    resolution::validate(proof, budget)
}

fn preflight(
    proof: &BvBlastProof,
    budget: &ReplayBudget<'_, '_>,
) -> Result<(), BvBlastValidateError> {
    if proof.format_version != FORMAT_VERSION {
        return Err(BvBlastValidateError::UnsupportedFormatVersion {
            got: proof.format_version,
            expected: FORMAT_VERSION,
        });
    }
    let equality_width = proof.obligation.width;
    if equality_width == 0 || equality_width > MAX_WIDTH {
        return Err(BvBlastValidateError::MalformedBitEqLayout {
            reason: format!("equality width {equality_width} is outside 1..={MAX_WIDTH}"),
        });
    }
    let limits = budget.limits;
    budget.count("variables", proof.vars.len(), limits.max_vars)?;
    budget.count("bit lemmas", proof.bit_lemmas.len(), limits.max_bit_lemmas)?;
    budget.count("clauses", proof.clauses.len(), limits.max_clauses)?;
    budget.count(
        "resolution steps",
        proof.refutation.steps.len(),
        limits.max_resolution_steps,
    )?;
    budget.count("variables", proof.vars.len(), u32::MAX as usize)?;
    budget.count("clauses", proof.clauses.len(), u32::MAX as usize)
}

fn check_var(proof: &BvBlastProof, var: u32) -> Result<(), BvBlastValidateError> {
    if (var as usize) < proof.vars.len() {
        Ok(())
    } else {
        Err(BvBlastValidateError::UndefinedVar(var))
    }
}

fn is_input_role(role: &VarRole) -> bool {
    matches!(
        role,
        VarRole::InputA { .. } | VarRole::InputB { .. } | VarRole::InputLeaf { .. }
    )
}
