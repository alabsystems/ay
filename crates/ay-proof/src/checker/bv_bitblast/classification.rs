// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cancellation-only structural BV census; never a semantic proof producer.

use std::convert::Infallible;

use super::super::closed_bv_evaluate;
use super::*;

mod closed_bv_lia;
mod credits;
pub(crate) use closed_bv_lia::CLOSED_BV_LIA_CLASSIFIER_WORK;
pub(crate) use credits::{ExpensiveBvCreditPlan, PrepaidBvCredits};

#[cfg(test)]
mod tests;

type Poll<'a, E> = &'a mut dyn FnMut() -> Result<(), E>;
type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

fn infallible<T>(operation: impl FnOnce(Poll<'_, Infallible>) -> Result<T, Infallible>) -> T {
    match operation(&mut || Ok(())) {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

fn controlled<T>(
    progress: Progress<'_>,
    operation: impl FnOnce(Poll<'_, ProofCheckError>) -> Result<T, ProofCheckError>,
) -> Result<T, ProofCheckError> {
    let mut refused = false;
    let mut poll = || {
        if refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        // A callback panic caught below must not enable a retry/publication.
        refused = true;
        if progress(0, 0) {
            refused = false;
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    };
    poll()?;
    let result = operation(&mut poll);
    // The census/collector frame and its private scratch have been destroyed.
    poll()?;
    result
}

pub(super) fn requires_proof_producer(terms: &TermStore, clause: &[TermId]) -> bool {
    infallible(|poll| classify(terms, clause, poll))
}

#[cfg(test)]
pub(super) fn clause_mentions_bv(terms: &TermStore, clause: &[TermId]) -> bool {
    infallible(|poll| mentions_bv(terms, clause, poll))
}

#[cfg(test)]
pub(super) fn collect_bounded_vars(terms: &TermStore, clause: &[TermId]) -> Option<Vec<EvalVar>> {
    infallible(|poll| bounded_vars(terms, clause, poll))
}

/// A classification, never proof authority. Zero-cost polls share the caller's
/// control; unsupported bounded syntax still means a possibly expensive check.
/// Individual hashing, allocation and scalar operations remain opaque. This
/// does not provide complete work/byte metering or a hard latency bound.
#[cfg(test)]
pub(crate) fn bv_bitblast_requires_proof_producer_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    controlled(progress, |poll| classify(terms, clause, poll))
}

/// Preserve the whole-proof cap and worst fees, except the complete closed
/// Boolean BV/LIA source bound. Census eligibility is never proof authority.
pub(crate) fn validate_expensive_bv_budget_with_progress(
    proof: &Proof,
    terms: &TermStore,
    progress: Progress<'_>,
) -> Result<ExpensiveBvAggregateCharge, ProofCheckError> {
    controlled(progress, |poll| census(proof, terms, poll)).map(|plan| plan.aggregate_charge())
}

/// Collect the same census as legacy validation, retaining bounded borrowed
/// source entries. This does not debit the aggregate or establish proof validity.
pub(crate) fn plan_expensive_bv_credits_with_progress<'a>(
    proof: &'a Proof,
    terms: &'a TermStore,
    progress: Progress<'_>,
) -> Result<ExpensiveBvCreditPlan<'a>, ProofCheckError> {
    controlled(progress, |poll| census(proof, terms, poll))
}

fn classify<E>(terms: &TermStore, clause: &[TermId], poll: Poll<'_, E>) -> Result<bool, E> {
    poll()?;
    if !mentions_bv(terms, clause, poll)? {
        return Ok(false);
    }
    poll()?;
    // A wiring identity is accepted symbolically before either semantic
    // checker runs (`semantic_decision.rs`), so it never needs the producer.
    if wiring::holds_by_wiring(terms, clause) {
        return Ok(false);
    }
    let Some(vars) = bounded_vars(terms, clause, poll)? else {
        return Ok(true);
    };
    let mut bits = 0u32;
    for var in vars {
        poll()?;
        let Some(total) = bits.checked_add(var.bits) else {
            return Ok(true);
        };
        bits = total;
    }
    Ok(bits > MAX_BOUNDED_ASSIGNMENT_BITS)
}

fn census<'a>(
    proof: &'a Proof,
    terms: &'a TermStore,
    poll: Poll<'_, ProofCheckError>,
) -> Result<ExpensiveBvCreditPlan<'a>, ProofCheckError> {
    let (mut count, mut work, mut bytes) = (0usize, 0usize, 0usize);
    let mut plan = ExpensiveBvCreditPlan::new(terms);
    for (index, step) in proof.steps.iter().enumerate() {
        poll()?;
        let charge = step_charge(step, terms, poll)?;
        poll()?;
        let Some((step_work, step_bytes)) = charge else {
            continue;
        };
        count = count.checked_add(1).ok_or(ProofCheckError::ResourceLimit)?;
        if count > MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: ProofId(index as u32),
                reason: format!(
                    "proof contains more than {MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF} expensive BV \
                     steps; the proof-producing BV checker, BV/LIA checker, and closed-BV \
                     evaluator share this whole-proof cap"
                ),
            });
        }
        work = work
            .checked_add(step_work)
            .ok_or(ProofCheckError::ResourceLimit)?;
        bytes = bytes
            .checked_add(step_bytes)
            .ok_or(ProofCheckError::ResourceLimit)?;
        plan.record(count - 1, index, step, step_work, step_bytes);
    }
    plan.set_aggregate(ExpensiveBvAggregateCharge { work, bytes });
    Ok(plan)
}

fn step_charge(
    step: &ProofStep,
    terms: &TermStore,
    poll: Poll<'_, ProofCheckError>,
) -> Result<Option<(usize, usize)>, ProofCheckError> {
    let charge = match step {
        ProofStep::TheoryLemma {
            clause,
            kind,
            farkas,
            lia,
            ..
        } => match kind {
            TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. }
                if classify(terms, clause, poll)? =>
            {
                Some((
                    usize::try_from(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA)
                        .map_err(|_| ProofCheckError::ResourceLimit)?,
                    MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
                ))
            }
            TheoryLemmaKind::BvLiaTautology => {
                if farkas.is_none()
                    && lia.is_none()
                    && closed_bv_lia::eligible(terms, clause, poll)?
                {
                    Some(closed_bv_lia::CHARGE)
                } else {
                    Some((
                        usize::try_from(MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA)
                            .map_err(|_| ProofCheckError::ResourceLimit)?,
                        MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA,
                    ))
                }
            }
            TheoryLemmaKind::SeqExtensionalCompanionContradiction => Some((
                usize::try_from(MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA)
                    .map_err(|_| ProofCheckError::ResourceLimit)?,
                MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA,
            )),
            _ => None,
        },
        ProofStep::Step {
            rule: ay_core::AletheRule::Evaluate,
            clause,
            premises,
            args,
        } if closed_bv_evaluate::requires_expensive_budget(terms, clause, premises.len(), args) => {
            Some((
                usize::try_from(closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA)
                    .map_err(|_| ProofCheckError::ResourceLimit)?,
                closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_BYTES_PER_LEMMA,
            ))
        }
        _ => None,
    };
    Ok(charge)
}

fn push<E>(pending: &mut Vec<TermId>, term: TermId, poll: Poll<'_, E>) -> Result<(), E> {
    poll()?;
    pending.push(term);
    Ok(())
}

pub(super) fn mentions_bv<E>(
    terms: &TermStore,
    clause: &[TermId],
    poll: Poll<'_, E>,
) -> Result<bool, E> {
    poll()?;
    let mut visited = HashSet::new();
    let mut pending = Vec::with_capacity(clause.len());
    for &root in clause {
        push(&mut pending, root, poll)?;
    }
    while let Some(term) = pending.pop() {
        poll()?;
        let fresh = visited.insert(term);
        poll()?;
        if !fresh {
            continue;
        }
        if matches!(terms.sort(term), Sort::BitVec(_)) {
            return Ok(true);
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                poll()?;
                pending.reserve(args.len());
                for &arg in args {
                    push(&mut pending, arg, poll)?;
                }
            }
            TermData::Let(bindings, body) => {
                poll()?;
                pending.reserve(bindings.len());
                for (_, value) in bindings {
                    push(&mut pending, *value, poll)?;
                }
                push(&mut pending, *body, poll)?;
            }
            TermData::Not(inner) => push(&mut pending, *inner, poll)?,
            TermData::Ite(condition, then_branch, else_branch) => {
                poll()?;
                pending.reserve(3);
                push(&mut pending, *condition, poll)?;
                push(&mut pending, *then_branch, poll)?;
                push(&mut pending, *else_branch, poll)?;
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                push(&mut pending, *body, poll)?;
                for trigger in triggers {
                    poll()?;
                    for &term in trigger {
                        push(&mut pending, term, poll)?;
                    }
                }
            }
            _ => {}
        }
    }
    Ok(false)
}

pub(super) fn bounded_vars<E>(
    terms: &TermStore,
    clause: &[TermId],
    poll: Poll<'_, E>,
) -> Result<Option<Vec<EvalVar>>, E> {
    poll()?;
    let mut vars = Vec::new();
    let mut visited = HashSet::new();
    for &lit in clause {
        poll()?;
        if !bounded_term(terms, lit, &mut vars, &mut visited, &mut Vec::new(), poll)? {
            return Ok(None);
        }
    }
    Ok(Some(vars))
}

fn bounded_term<E>(
    terms: &TermStore,
    term: TermId,
    vars: &mut Vec<EvalVar>,
    visited: &mut HashSet<TermId>,
    stack: &mut Vec<TermId>,
    poll: Poll<'_, E>,
) -> Result<bool, E> {
    poll()?;
    // Keep these checks BEFORE visited, including for duplicate deep edges.
    if stack.len() > 512 {
        return Ok(false);
    }
    if matches!(terms.sort(term), Sort::BitVec(bv) if bv.width > MAX_EVALUATED_BV_WIDTH) {
        return Ok(false);
    }
    // These operations used to be excluded only by serialized-bundle
    // preflight. Enforce the evaluator's actual safety envelope here too,
    // before both direct checking and the proof-producing fallback.
    if let TermData::App(symbol, args) = terms.get(term) {
        let name = symbol.name();
        if matches!(
            name,
            "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "bvsdiv" | "bvsrem" | "bvsmod" | "repeat"
        ) {
            let Some(&operand) = args.first() else {
                return Ok(false);
            };
            if !matches!(terms.sort(operand), Sort::BitVec(bv) if bv.width < u64::BITS) {
                return Ok(false);
            }
        }
    }
    let fresh = visited.insert(term);
    poll()?;
    if !fresh {
        return Ok(true);
    }
    push(stack, term, poll)?;
    let result = match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => true,
        TermData::Const(Constant::BitVec { width, .. }) if *width <= MAX_EVALUATED_BV_WIDTH => true,
        TermData::Const(_) => false,
        TermData::Var(_, _) => {
            let (kind, bits) = match terms.sort(term) {
                Sort::Bool => (EvalVarKind::Bool, 1),
                Sort::BitVec(bv) if bv.width <= MAX_BOUNDED_BV_WIDTH => {
                    (EvalVarKind::BitVec, bv.width)
                }
                _ => return Ok(false),
            };
            poll()?;
            vars.push(EvalVar { term, kind, bits });
            true
        }
        TermData::App(sym, args) if supports_bounded_app(sym.name()) => {
            for &arg in args {
                if !bounded_term(terms, arg, vars, visited, stack, poll)? {
                    return Ok(false);
                }
            }
            true
        }
        TermData::Not(inner) => bounded_term(terms, *inner, vars, visited, stack, poll)?,
        TermData::Ite(c, t, e) => {
            if !bounded_term(terms, *c, vars, visited, stack, poll)? {
                return Ok(false);
            }
            if !bounded_term(terms, *t, vars, visited, stack, poll)? {
                return Ok(false);
            }
            bounded_term(terms, *e, vars, visited, stack, poll)?
        }
        _ => false,
    };
    stack.pop();
    Ok(result)
}
