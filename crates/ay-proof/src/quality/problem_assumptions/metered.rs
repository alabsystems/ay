// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-assumption closure with caller-priced containers and ITE matching.

use std::collections::BTreeSet;

use super::*;

#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;
type AuthoredIte = (TermId, TermId, TermId);

fn lookup(entries: usize, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    let levels = checked_add_usize(entries.bit_width() as usize, 1)?;
    let comparisons = checked_add_usize(entries, 1)?.min(checked_mul_usize(levels, 12)?);
    charge_progress(progress, comparisons, 0)
}

fn insert_allowed(
    allowed: &mut BTreeSet<TermId>,
    term: TermId,
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    lookup(allowed.len(), progress)?;
    if allowed.contains(&term) {
        return Ok(false);
    }
    // BTree insert searches again and may split one node per level plus a
    // root. alloc's B=6 nodes have 11 keys/12 edges; fixed-width TermIds carry
    // no recursive comparison or hash payload. No new cardinality cap.
    lookup(allowed.len(), progress)?;
    let nodes = checked_add_usize(allowed.len().bit_width() as usize, 2)?;
    let slots = checked_mul_usize(nodes, 32)?;
    charge_progress(
        progress,
        slots,
        checked_mul_usize(
            slots,
            checked_add_usize(size_of::<TermId>(), size_of::<usize>())?,
        )?,
    )?;
    Ok(allowed.insert(term))
}

fn push<T>(values: &mut Vec<T>, value: T, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    checked_add_usize(values.len(), 1)?;
    if values.len() == values.capacity() {
        let capacity = checked_mul_usize(values.capacity().max(2), 2)?;
        let bytes = checked_mul_usize(capacity, size_of::<T>())?;
        charge_progress(progress, checked_add_usize(bytes, 1)?, bytes)?;
        values
            .try_reserve_exact(capacity - values.len())
            .map_err(|_| ProofCheckError::ResourceLimit)?;
    }
    values.push(value);
    Ok(())
}

fn term<'a>(
    terms: &'a TermStore,
    id: TermId,
    progress: Progress<'_>,
) -> Result<&'a TermData, ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    if id.index() >= terms.len() {
        const MESSAGE: &str = "problem assumption closure references term outside the term store";
        charge_progress(
            progress,
            checked_add_usize(MESSAGE.len(), 1)?,
            MESSAGE.len(),
        )?;
        return Err(ProofCheckError::MalformedProofBundle {
            reason: MESSAGE.to_owned(),
        });
    }
    Ok(terms.get(id))
}

fn closure(
    terms: &TermStore,
    assertions: &[TermId],
    progress: Progress<'_>,
) -> Result<(BTreeSet<TermId>, Vec<AuthoredIte>), ProofCheckError> {
    let mut allowed = BTreeSet::new();
    let mut stack = Vec::new();
    for &assertion in assertions {
        charge_progress(progress, 1, 0)?;
        if insert_allowed(&mut allowed, assertion, progress)? {
            push(&mut stack, assertion, progress)?;
        }
    }
    let mut authored_bool_ites = Vec::new();
    while let Some(current) = stack.pop() {
        match term(terms, current, progress)? {
            TermData::Ite(condition, then_term, else_term) => {
                push(
                    &mut authored_bool_ites,
                    (*condition, *then_term, *else_term),
                    progress,
                )?;
            }
            TermData::App(Symbol::Named(name), args) => {
                charge_progress(progress, checked_add_usize(name.len().min(3), 1)?, 0)?;
                if name != "and" {
                    continue;
                }
                for &arg in args {
                    charge_progress(progress, 1, 0)?;
                    if insert_allowed(&mut allowed, arg, progress)? {
                        push(&mut stack, arg, progress)?;
                    }
                }
            }
            _ => {}
        }
    }
    charge_progress(progress, 0, 0)?;
    Ok((allowed, authored_bool_ites))
}

pub(in crate::quality) fn validate_problem_assumptions_with_progress(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    charge_progress(progress, 0, 0)?;
    let (allowed, authored_bool_ites) = closure(terms, problem_assertions, progress)?;
    for (index, step) in proof.steps.iter().enumerate() {
        charge_progress(progress, 1, 0)?;
        let proof_id = ProofId(u32::try_from(index).map_err(|_| ProofCheckError::ResourceLimit)?);
        if let ProofStep::Assume(assumed) = step {
            term(terms, *assumed, progress)?;
            lookup(allowed.len(), progress)?;
            if allowed.contains(assumed) {
                continue;
            }
            if !crate::checker::assumed_is_authored_bool_ite_consequence_with_progress(
                terms,
                *assumed,
                &authored_bool_ites,
                progress,
            )? {
                return Err(ProofCheckError::UnauthorizedAssumption {
                    step: proof_id,
                    term: *assumed,
                });
            }
        }
    }
    charge_progress(progress, 0, 0)
}
