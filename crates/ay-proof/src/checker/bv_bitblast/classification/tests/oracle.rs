// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

//! Frozen unpolled classification and aggregate census; never invokes a solver.

use super::*;

pub(super) fn classify(terms: &TermStore, clause: &[TermId]) -> bool {
    if !mentions_bv(terms, clause) {
        return false;
    }
    match bounded_vars(terms, clause) {
        Some(vars) => vars
            .iter()
            .try_fold(0u32, |total, var| total.checked_add(var.bits))
            .is_none_or(|total| total > MAX_BOUNDED_ASSIGNMENT_BITS),
        None => true,
    }
}

pub(super) fn mentions_bv(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut visited = HashSet::new();
    let mut pending = clause.to_vec();
    while let Some(term) = pending.pop() {
        if !visited.insert(term) {
            continue;
        }
        if matches!(terms.sort(term), Sort::BitVec(_)) {
            return true;
        }
        match terms.get(term) {
            TermData::App(_, args) => pending.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(c, t, e) => pending.extend([*c, *t, *e]),
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                pending.push(*body);
                pending.extend(triggers.iter().flatten().copied());
            }
            _ => {}
        }
    }
    false
}

pub(super) fn bounded_vars(terms: &TermStore, clause: &[TermId]) -> Option<Vec<EvalVar>> {
    let mut vars = Vec::new();
    let mut visited = HashSet::new();
    for &lit in clause {
        bounded_term(terms, lit, &mut vars, &mut visited, &mut Vec::new())?;
    }
    Some(vars)
}

fn bounded_term(
    terms: &TermStore,
    term: TermId,
    vars: &mut Vec<EvalVar>,
    visited: &mut HashSet<TermId>,
    stack: &mut Vec<TermId>,
) -> Option<()> {
    if stack.len() > 512 {
        return None;
    }
    if matches!(terms.sort(term), Sort::BitVec(bv) if bv.width > MAX_EVALUATED_BV_WIDTH) {
        return None;
    }
    if !visited.insert(term) {
        return Some(());
    }
    stack.push(term);
    let result = match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => Some(()),
        TermData::Const(Constant::BitVec { width, .. }) if *width <= MAX_EVALUATED_BV_WIDTH => {
            Some(())
        }
        TermData::Const(_) => None,
        TermData::Var(_, _) => {
            let (kind, bits) = match terms.sort(term) {
                Sort::Bool => (EvalVarKind::Bool, 1),
                Sort::BitVec(bv) if bv.width <= MAX_BOUNDED_BV_WIDTH => {
                    (EvalVarKind::BitVec, bv.width)
                }
                _ => return None,
            };
            vars.push(EvalVar { term, kind, bits });
            Some(())
        }
        TermData::App(sym, args) if supports_bounded_app(sym.name()) => {
            for &arg in args {
                bounded_term(terms, arg, vars, visited, stack)?;
            }
            Some(())
        }
        TermData::Not(inner) => bounded_term(terms, *inner, vars, visited, stack),
        TermData::Ite(c, t, e) => {
            bounded_term(terms, *c, vars, visited, stack)?;
            bounded_term(terms, *t, vars, visited, stack)?;
            bounded_term(terms, *e, vars, visited, stack)
        }
        _ => None,
    };
    stack.pop();
    result
}

pub(super) fn census(
    proof: &Proof,
    terms: &TermStore,
) -> Result<ExpensiveBvAggregateCharge, ProofCheckError> {
    let (mut count, mut work, mut bytes) = (0usize, 0usize, 0usize);
    for (index, step) in proof.steps.iter().enumerate() {
        let charge = match step {
            ProofStep::TheoryLemma { clause, kind, .. } => match kind {
                TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. }
                    if classify(terms, clause) =>
                {
                    Some((
                        usize::try_from(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA)
                            .map_err(|_| ProofCheckError::ResourceLimit)?,
                        MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
                    ))
                }
                TheoryLemmaKind::BvLiaTautology
                | TheoryLemmaKind::SeqExtensionalCompanionContradiction => Some((
                    usize::try_from(MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA)
                        .map_err(|_| ProofCheckError::ResourceLimit)?,
                    MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA,
                )),
                _ => None,
            },
            ProofStep::Step {
                rule: AletheRule::Evaluate,
                clause,
                premises,
                args,
            } if closed_bv_evaluate::requires_expensive_budget(
                terms,
                clause,
                premises.len(),
                args,
            ) =>
            {
                Some((
                    usize::try_from(closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA)
                        .map_err(|_| ProofCheckError::ResourceLimit)?,
                    closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_BYTES_PER_LEMMA,
                ))
            }
            _ => None,
        };
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
    }
    Ok(ExpensiveBvAggregateCharge { work, bytes })
}
