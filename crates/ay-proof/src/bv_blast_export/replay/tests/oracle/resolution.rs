// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

pub(super) fn validate(
    proof: &BvBlastProof,
    budget: &mut ReplayBudget<'_>,
) -> Result<(), BvBlastValidateError> {
    let limits = budget.limits;
    // 3. Resolution chain. Premise id space: [0, clauses.len()) are clauses,
    //    [clauses.len(), ...) are steps in order.
    let nclauses = proof.clauses.len() as u32;
    if proof.refutation.steps.is_empty() {
        return Err(BvBlastValidateError::EmptyRefutation);
    }
    let lookup = |id: u32, upto_step: usize| -> Option<&[Lit]> {
        if id < nclauses {
            return Some(proof.clauses[id as usize].lits.as_slice());
        }
        let step_idx = (id - nclauses) as usize;
        if step_idx < upto_step {
            Some(proof.refutation.steps[step_idx].clause.as_slice())
        } else {
            None
        }
    };

    let mut derived_literals = 0_usize;
    for (i, step) in proof.refutation.steps.iter().enumerate() {
        budget.deadline()?;
        let expected_id = nclauses.saturating_add(u32::try_from(i).unwrap_or(u32::MAX));
        if step.id != expected_id {
            return Err(BvBlastValidateError::NonCanonicalResolutionStepId {
                index: i,
                id: step.id,
                expected: expected_id,
            });
        }
        derived_literals = derived_literals.saturating_add(step.clause.len());
        budget.count(
            "derived literals",
            derived_literals,
            limits.max_derived_literals,
        )?;
        let Some(a) = lookup(step.premises[0], i) else {
            return Err(BvBlastValidateError::UnknownPremise {
                step: step.id,
                premise: step.premises[0],
            });
        };
        let Some(b) = lookup(step.premises[1], i) else {
            return Err(BvBlastValidateError::UnknownPremise {
                step: step.id,
                premise: step.premises[1],
            });
        };
        let local_work = a
            .len()
            .saturating_add(b.len())
            .saturating_add(step.clause.len())
            .saturating_mul(4)
            .saturating_add(1);
        budget.add_work(local_work)?;
        check_var(proof, step.pivot)?;
        for literal in &step.clause {
            check_var(proof, literal.var)?;
        }
        let got = resolve(a, b, step.pivot);
        match got {
            Some(resolvent) if clause_set_eq(&resolvent, &step.clause) => {}
            _ => return Err(BvBlastValidateError::ResolutionMismatch { step: step.id }),
        }
    }

    let last = proof
        .refutation
        .steps
        .last()
        .expect("non-empty checked above");
    if !last.clause.is_empty() {
        return Err(BvBlastValidateError::NotEmptyClause(last.clause.len()));
    }

    Ok(())
}
