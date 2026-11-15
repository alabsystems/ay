// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent exact FP constructor and FULL arithmetic WORD schemas.
//! Complete unit equalities bind actual source terms, formats, rounding mode
//! and every lowered word field. Native circuit tags/finite enumeration are
//! not certificates. Raw native CNF, source Rust NaNs and input journals still
//! require independently checked producer/export/original-source bridges.

use ay_core::{FpOp, ProofId, TermId, TermStore};

use super::ProofCheckError;

mod constructor;
mod reference_mul;

pub(crate) fn validate_fp_to_bv(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    operation: FpOp,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let arithmetic = match operation {
        FpOp::Mul => Some(reference_mul::Arithmetic::Mul),
        FpOp::Add => Some(reference_mul::Arithmetic::Add),
        FpOp::Sub => Some(reference_mul::Arithmetic::Sub),
        _ => None,
    };
    let accepted = if let Some(arithmetic) = arithmetic {
        match reference_mul::recognizes_arithmetic(terms, clause, arithmetic, progress) {
            Ok(matched) => matched,
            Err(
                reference_mul::ReferenceError::Resource | reference_mul::ReferenceError::Allocation,
            ) => {
                return Err(ProofCheckError::ResourceLimit);
            }
            Err(_) => false,
        }
    } else {
        constructor::recognizes(terms, step_id, clause, operation, progress)?
    };
    if accepted {
        return Ok(());
    }
    // Normal nonmatch and successful word replay observe the original owner
    // after temporary programs are dropped; no source scan is repeated here.
    let reason = "fp_to_bv clause lacks an accepted exact semantic lowering schema";
    if !progress(reason.len(), reason.len()) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let refused = ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: reason.to_owned(),
    };
    if !progress(0, 0) {
        return Err(ProofCheckError::ResourceLimit);
    }
    Err(refused)
}

pub(crate) fn validate_canonical_clause_with_owner(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    operation: FpOp,
    limits: &ay_sat::ResolutionProofLimits,
    work: &mut ay_core::original_query::WorkBudget<'_>,
) -> Result<(), ProofCheckError> {
    reference_mul::validate_canonical_clause(terms, step, clause, operation, limits, work)
}
