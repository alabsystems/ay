// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One complete strict walk with canonical FP clause search on the SAME owner.
//! The immutable source snapshot is not an authenticated original script:
//! external source/declaration/RM correspondence and wire export remain separate.
//! Callback-only entries retain their exact schema-only semantics.

use super::*;
use ay_core::original_query::WorkBudget;
use ay_core::time::Instant;
use ay_sat::ResolutionProofLimits;

/// Borrowed native snapshot inputs, NOT a credential or source-query permit.
/// Callers must independently bind the complete original declaration namespace
/// and source-to-term journal. In particular a named RoundingMode carrier does
/// not itself authenticate the reserved five-value SMT theory.
pub struct NativeFpProofContext<'a> {
    pub terms: &'a TermStore,
    pub datatype_declarations: Option<&'a [(String, Vec<String>)]>,
    pub constructor_selectors: Option<&'a [(String, Vec<String>)]>,
    pub datatype_member_signatures: &'a [DatatypeMemberSignature],
    pub problem_assertions: &'a [TermId],
}

/// Opaque diagnostics for one validated source-snapshot refutation.
/// This is deliberately NOT ProofQuality, a native certificate, an exported
/// proof, or an original-input credential, and has no conversion to those.
#[derive(Debug)]
pub struct NativeFpSnapshotQuality {
    quality: ProofQuality,
}

impl NativeFpSnapshotQuality {
    /// Number of steps in the complete snapshot proof that was checked.
    #[must_use]
    pub fn total_steps(&self) -> u32 {
        self.quality.total_steps
    }
}

impl<'a> From<NativeFpProofContext<'a>> for StrictProofContext<'a> {
    fn from(context: NativeFpProofContext<'a>) -> Self {
        Self {
            terms: context.terms,
            dt_decls: context.datatype_declarations,
            ctor_selectors: context.constructor_selectors,
            datatype_member_signatures: Some(context.datatype_member_signatures),
            problem_assertions: Some(context.problem_assertions),
        }
    }
}

/// Strict whole-proof validation using a single existing remaining owner and
/// preexisting absolute search limits. Every actual FpToBv clause is checked as
/// a WHOLE disjunction: all ordered literals are negated as canonical roots.
/// Its tag must match the actual top-level arithmetic source of an exact unit
/// equality; a tag or caller-supplied lowering graph alone grants no authority.
///
/// Canonical total-definition search and independent RUP replay precede the
/// shared strict step pass. All original assumptions, registries, other theory
/// rules, semantic precharges and terminal-empty obligations remain required.
/// No grant/refund or per-lemma WorkBudget adapter is created. Returned quality
/// authenticates source-SNAPSHOT proof semantics only, not external original
/// input, Rust raw NaNs, native producer CNF, public verdict or exported wire.
///
/// # Errors
/// Unsupported/false FP clauses, any ordinary strict proof error, or original
/// owner/deadline refusal fail closed with no partly validated inventory.
pub fn check_proof_strict_with_native_fp_context(
    proof: &Proof,
    context: NativeFpProofContext<'_>,
    limits: &ResolutionProofLimits,
    work: &mut WorkBudget<'_>,
) -> Result<NativeFpSnapshotQuality, ProofCheckError> {
    let limits = limits.clone();
    clock(&limits, work)?;
    let result = check_inner(proof, context.into(), &limits, work);
    let terminal = clock(&limits, work);
    match result {
        Err(error) => Err(error),
        Ok(quality) => match terminal {
            Ok(()) => Ok(NativeFpSnapshotQuality { quality }),
            Err(error) => {
                drop(quality);
                Err(error)
            }
        },
    }
}

fn check_inner(
    proof: &Proof,
    context: StrictProofContext<'_>,
    limits: &ResolutionProofLimits,
    work: &mut WorkBudget<'_>,
) -> Result<ProofQuality, ProofCheckError> {
    let accepted = ValidatedSteps::prepare(proof, context.terms, &limits, work)?;
    let result = (|| {
        let mut progress =
            |units, bytes| clock(limits, work).is_ok() && work.admit(units, bytes).is_ok();
        let ((quality, clauses, deferred), retained_output) = validate_strict_steps_with_evidence(
            proof,
            context,
            GenericTheoryDeferral::Reject,
            None,
            Some(&accepted),
            &mut progress,
        )?;
        debug_assert!(deferred.is_empty());
        debug_assert!(retained_output.is_empty());
        ensure_terminal_empty_clause(&clauses)?;
        // Temporary derived clauses/registries drop before the outer observation.
        Ok(quality)
    })();
    drop(accepted);
    result
}

fn clock(limits: &ResolutionProofLimits, work: &mut WorkBudget<'_>) -> Result<(), ProofCheckError> {
    work.charge(0).map_err(|_| ProofCheckError::ResourceLimit)?;
    if limits.deadline.is_none_or(|end| Instant::now() >= end) {
        work.refuse_exhaustion();
        return Err(ProofCheckError::ResourceLimit);
    }
    Ok(())
}

/// Private results tied to one actual immutable proof/store pair. No public
/// constructor/accessor or wire representation can install a passed step.
pub(super) struct ValidatedSteps<'proof> {
    proof: &'proof Proof,
    terms: &'proof TermStore,
    ids: Vec<ProofId>,
}

impl<'proof> ValidatedSteps<'proof> {
    fn prepare(
        proof: &'proof Proof,
        terms: &'proof TermStore,
        limits: &ResolutionProofLimits,
        work: &mut WorkBudget<'_>,
    ) -> Result<Self, ProofCheckError> {
        clock(limits, work)?;
        work.charge(proof.steps.len())
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        let count = proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::FpToBv { .. },
                        ..
                    }
                )
            })
            .count();
        let bytes = count
            .checked_mul(size_of::<ProofId>())
            .ok_or_else(|| work.refuse_exhaustion())
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        work.admit(count, bytes)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        let mut ids = Vec::new();
        ids.try_reserve_exact(count).map_err(|_| {
            work.refuse_exhaustion();
            ProofCheckError::ResourceLimit
        })?;
        for (index, step) in proof.steps.iter().enumerate() {
            clock(limits, work)?;
            let ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::FpToBv { operation },
                clause,
                ..
            } = step
            else {
                continue;
            };
            if !matches!(
                operation,
                ay_core::FpOp::Add | ay_core::FpOp::Sub | ay_core::FpOp::Mul
            ) {
                continue;
            }
            let id = u32::try_from(index).map(ProofId).map_err(|_| {
                work.refuse_exhaustion();
                ProofCheckError::ResourceLimit
            })?;
            crate::checker::validate_canonical_clause_with_owner(
                terms, id, clause, *operation, limits, work,
            )?;
            ids.push(id);
        }
        clock(limits, work)?;
        Ok(Self { proof, terms, ids })
    }

    pub(super) fn clause(
        &self,
        id: ProofId,
        step: &ProofStep,
        terms: &TermStore,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Option<&'proof [TermId]>, ProofCheckError> {
        if !progress(
            self.ids
                .len()
                .checked_ilog2()
                .unwrap_or(0)
                .saturating_add(2) as usize,
            0,
        ) {
            return Err(ProofCheckError::ResourceLimit);
        }
        if self.ids.binary_search(&id).is_err() {
            return Ok(None);
        }
        if !std::ptr::eq(self.terms, terms)
            || !self
                .proof
                .steps
                .get(id.0 as usize)
                .is_some_and(|actual| std::ptr::eq(actual, step))
        {
            return Err(ProofCheckError::ResourceLimit);
        }
        match &self.proof.steps[id.0 as usize] {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::FpToBv { .. },
                clause,
                ..
            } => Ok(Some(clause.as_slice())),
            _ => Err(ProofCheckError::ResourceLimit),
        }
    }
}

#[cfg(test)]
mod tests;
