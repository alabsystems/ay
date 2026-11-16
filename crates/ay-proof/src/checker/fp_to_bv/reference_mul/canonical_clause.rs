// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact source-operation/unit binding around canonical refutation search.

use super::super::ProofCheckError;
use super::{canonical, ReferenceError};
use ay_core::{TermId, TermStore};

pub(super) fn validate(
    terms: &TermStore,
    step: ay_core::ProofId,
    clause: &[TermId],
    operation: ay_core::FpOp,
    limits: &ay_sat::ResolutionProofLimits,
    work: &mut ay_core::original_query::WorkBudget<'_>,
) -> Result<(), ProofCheckError> {
    let message = "complete live FP clause has no canonical source-bound refutation";
    work.admit(message.len(), message.len())
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    let mut reason = String::new();
    reason.try_reserve_exact(message.len()).map_err(|_| {
        work.refuse_exhaustion();
        ProofCheckError::ResourceLimit
    })?;
    reason.push_str(message);
    let result = (|| {
        if !canonical_unit_matches_operation(terms, clause, operation, work)? {
            return Err(canonical::Error::Source);
        }
        let mut checked = canonical::capture_clause(terms, clause, limits, work)?;
        checked.replay()
    })();
    if result.is_ok() {
        drop(reason);
        return work.charge(0).map_err(|_| ProofCheckError::ResourceLimit);
    }
    // Original semantic failures survive a later owner refusal, but that
    // refusal is still observed and remains latched in the SAME owner.
    let _ = work.charge(0);
    match result {
        Ok(()) => Ok(()),
        Err(
            canonical::Error::Owner(_)
            | canonical::Error::Reference(ReferenceError::Resource | ReferenceError::Allocation),
        ) => Err(ProofCheckError::ResourceLimit),
        Err(canonical::Error::Search(error))
            if !matches!(error, ay_sat::ResolutionProofError::Satisfiable) =>
        {
            work.refuse_exhaustion();
            Err(ProofCheckError::ResourceLimit)
        }
        Err(canonical::Error::Replay(error))
            if !matches!(error, ay_sat::ResolutionValidationError::Invalid(_)) =>
        {
            work.refuse_exhaustion();
            Err(ProofCheckError::ResourceLimit)
        }
        Err(_) => Err(ProofCheckError::InvalidTheoryLemma { step, reason }),
    }
}

/// A canonical proof cannot relabel a valid theorem as another operation or
/// weaken a lowering certificate with extra literals. All source details are
/// subsequently checked by the independent complete source compiler.
fn canonical_unit_matches_operation(
    terms: &TermStore,
    clause: &[TermId],
    operation: ay_core::FpOp,
    work: &mut ay_core::original_query::WorkBudget<'_>,
) -> Result<bool, canonical::Error> {
    let name = match operation {
        ay_core::FpOp::Add => "fp.add",
        ay_core::FpOp::Sub => "fp.sub",
        ay_core::FpOp::Mul => "fp.mul",
        _ => return Ok(false),
    };
    work.charge(1)?;
    let [root] = clause else {
        return Ok(false);
    };
    if terms.entry_stamp(*root).is_none() {
        return Ok(false);
    }
    let ay_core::TermData::App(ay_core::Symbol::Named(equal), args) = terms.get(*root) else {
        return Ok(false);
    };
    if equal.len() != 1
        || equal.as_str() != "="
        || terms.is_declared_function(equal)
        || args.len() != 2
        || !matches!(terms.sort(*root), ay_core::Sort::Bool)
    {
        return Ok(false);
    }
    work.charge(2)?;
    let [left, right] = args.as_slice() else {
        return Ok(false);
    };
    if terms.entry_stamp(*left).is_none() || terms.entry_stamp(*right).is_none() {
        return Ok(false);
    }
    if !matches!(terms.sort(*left), ay_core::Sort::FloatingPoint(_, _))
        || terms.sort(*left) != terms.sort(*right)
    {
        return Ok(false);
    }
    for side in [*left, *right] {
        work.charge(1)?;
        if let ay_core::TermData::App(ay_core::Symbol::Named(actual), operands) = terms.get(side) {
            if actual.len() == name.len()
                && actual.as_str() == name
                && operands.len() == 3
                && !terms.is_declared_function(actual)
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}
