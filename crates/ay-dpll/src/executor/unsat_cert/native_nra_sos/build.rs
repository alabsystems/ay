// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-clause SOS construction, not executor query/declaration authority.
//!
//! The caller supplies one sticky resource/cancellation control. Builder-owned
//! vectors and the existing candidate, query and bundle-copy APIs debit it.
//! Raw-term interning and individual allocation/arithmetic operations remain
//! opaque; offline bundle replay currently forwards cancellation, not its work
//! and byte charges. This is not a complete heap or hard latency bound.

use std::mem::size_of;

use ay_core::{
    NraSosCertificate, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
};
use ay_proof::{
    check_nra_sos_query_with_progress, re_check_bundle_strict_with_cancellation,
    CheckedNraSosQuery, NraSosQueryCheckError, ProofCheckError, ProofQuality,
    SerializableProofBundle,
};

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

pub(super) struct BuiltSosProof {
    pub(super) candidate: Proof,
    pub(super) bundle: SerializableProofBundle,
    pub(super) evidence: CheckedNraSosQuery,
    pub(super) quality: ProofQuality,
}

#[derive(Debug, thiserror::Error)]
pub(super) enum BuildError {
    #[error("native SOS construction exhausted its resource or cancellation envelope")]
    ResourceLimit,
    #[error("native SOS query binding failed: {0}")]
    Query(NraSosQueryCheckError),
    #[error("native SOS independent proof replay failed: {0}")]
    Replay(ProofCheckError),
    #[error("native SOS construction did not retain its complete exact proof shape")]
    InvalidProof,
}

impl From<NraSosQueryCheckError> for BuildError {
    fn from(error: NraSosQueryCheckError) -> Self {
        match error {
            NraSosQueryCheckError::ResourceLimit
            | NraSosQueryCheckError::Kernel(ProofCheckError::Cancelled) => Self::ResourceLimit,
            other => Self::Query(other),
        }
    }
}

impl From<ProofCheckError> for BuildError {
    fn from(error: ProofCheckError) -> Self {
        match error {
            ProofCheckError::ResourceLimit | ProofCheckError::Cancelled => Self::ResourceLimit,
            other => Self::Replay(other),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Parity {
    atom: TermId,
    negative: bool,
}

struct Source {
    roots: Vec<TermId>,
    clause: Vec<TermId>,
    parities: Vec<Parity>,
}

/// Cheap read-only routing gate before the executor's declaration inventory.
/// This authenticates only comparison shells, not their polynomial contents;
/// the actual builder and independent checker repeat their complete checks.
pub(super) fn supports_source(
    terms: &TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    progress: Progress<'_>,
) -> Result<bool, BuildError> {
    charge(progress, 0, 0)?;
    let count = assertions
        .len()
        .checked_add(assumptions.len())
        .ok_or(BuildError::ResourceLimit)?;
    if count == 0 || count > NraSosCertificate::MAX_CLAUSE_SLOTS {
        return Ok(false);
    }
    for &root in assertions.iter().chain(assumptions) {
        if comparison_parity(terms, root, progress)?.is_none() {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Build only against these exact ordered partitions. No source root is
/// normalized, removed or promoted to an executor-authored assertion here.
pub(super) fn build(
    terms: &mut TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    progress: Progress<'_>,
) -> Result<Option<BuiltSosProof>, BuildError> {
    charge(progress, 0, 0)?;
    let outcome = build_inner(terms, assertions, assumptions, progress)?;
    // All worker scratch and temporary checker state have been destroyed.
    charge(progress, 0, 0)?;
    Ok(outcome)
}

fn build_inner(
    terms: &mut TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    progress: Progress<'_>,
) -> Result<Option<BuiltSosProof>, BuildError> {
    let Some(source) = source(terms, assertions, assumptions, progress)? else {
        return Ok(None);
    };
    let Some(lemma) = ay_nra::find_sos_refutation_candidate(terms, &source.clause, progress)
        .map_err(|_| BuildError::ResourceLimit)?
    else {
        return Ok(None);
    };
    // Raw complements have ALL been interned before this whole-arena token.
    let evidence =
        check_nra_sos_query_with_progress(terms, assertions, assumptions, &lemma, progress)?;
    let candidate = complete_proof(lemma, &source, progress)?;
    let bundle = SerializableProofBundle::from_proof_with_progress(
        &candidate,
        terms,
        &source.roots,
        progress,
    )?;
    let checked = re_check_bundle_strict_with_cancellation(&bundle, &mut || progress(0, 0))?;
    charge(progress, source.roots.len(), 0)?;
    if !checked.quality.is_complete()
        || checked.assume_terms != source.roots
        || !matches!(candidate.steps.last(), Some(ProofStep::Resolution { clause, .. }) if clause.is_empty())
        || !evidence.is_current_for_with_progress(terms, assertions, assumptions, progress)?
    {
        return Err(BuildError::InvalidProof);
    }
    Ok(Some(BuiltSosProof {
        candidate,
        bundle,
        evidence,
        quality: checked.quality,
    }))
}

fn source(
    terms: &mut TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    progress: Progress<'_>,
) -> Result<Option<Source>, BuildError> {
    let count = assertions
        .len()
        .checked_add(assumptions.len())
        .ok_or(BuildError::ResourceLimit)?;
    if count == 0 || count > NraSosCertificate::MAX_CLAUSE_SLOTS {
        return Ok(None);
    }
    let mut roots = vector(count, progress)?;
    let mut parities = vector(count, progress)?;
    for &root in assertions.iter().chain(assumptions) {
        let Some(parity) = comparison_parity(terms, root, progress)? else {
            return Ok(None);
        };
        roots.push(root);
        parities.push(parity);
    }
    // TermStore's ordinary intern path casts the next ID to u32. Admit its
    // complete possible suffix before constructing any new complement.
    if terms
        .len()
        .checked_add(count)
        .is_none_or(|end| end > u32::MAX as usize)
    {
        return Err(BuildError::ResourceLimit);
    }
    let mut clause = vector(count, progress)?;
    for &root in &roots {
        charge(progress, 1, size_of::<(TermData, Sort)>() + 64)?;
        // Unlike mk_not this preserves constants, duplicates and double not.
        clause.push(terms.mk_not_raw(root));
    }
    Ok(Some(Source {
        roots,
        clause,
        parities,
    }))
}

/// Identify only the direct comparison shell. The generator and independent
/// kernel separately authenticate the entire numeric expression underneath it.
fn comparison_parity(
    terms: &TermStore,
    root: TermId,
    progress: Progress<'_>,
) -> Result<Option<Parity>, BuildError> {
    let mut atom = root;
    let mut negative = false;
    // Valid arena DAGs cannot traverse more entries than the arena contains.
    // Also terminate on raw cyclic snapshots without inventing source meaning.
    for _ in 0..terms.len() {
        charge(progress, 1, 0)?;
        if terms.entry_stamp(atom).is_none() || !matches!(terms.sort(atom), Sort::Bool) {
            return Ok(None);
        }
        match terms.get(atom) {
            TermData::Not(inner) => {
                atom = *inner;
                negative = !negative;
            }
            TermData::App(Symbol::Named(name), args) => {
                charge(progress, name.len(), 0)?;
                let admitted =
                    args.len() == 2 && matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=");
                if !admitted {
                    return Ok(None);
                }
                charge(progress, 2, 0)?;
                if args.iter().any(|&arg| terms.entry_stamp(arg).is_none())
                    || !matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                    || terms.sort(args[0]) != terms.sort(args[1])
                {
                    return Ok(None);
                }
                return Ok(Some(Parity { atom, negative }));
            }
            _ => return Ok(None),
        }
    }
    Ok(None)
}

fn complete_proof(
    lemma: ProofStep,
    source: &Source,
    progress: Progress<'_>,
) -> Result<Proof, BuildError> {
    let count = source.roots.len();
    let maximum_steps = count
        .checked_mul(2)
        .and_then(|steps| steps.checked_add(1))
        .ok_or(BuildError::ResourceLimit)?;
    let mut candidate = Proof::from_steps(vector(maximum_steps, progress)?);
    for &root in &source.roots {
        charge(progress, 1, 0)?;
        candidate.add_assume(root, None);
    }
    let mut current = candidate.add_step(lemma);
    let mut remaining = vector(count, progress)?;
    remaining.extend(0..count);
    for (index, &root) in source.roots.iter().enumerate() {
        charge(progress, remaining.len(), 0)?;
        let pivot = source.parities[index];
        if !remaining.iter().any(|&slot| source.parities[slot] == pivot) {
            continue;
        }
        // Native Resolution normalizes leading-not parity and treats clauses
        // as sets. Remove every occurrence of this parity, not just one slot;
        // the original SOS clause and all Assume slots remain untouched.
        charge(progress, remaining.len(), 0)?;
        remaining.retain(|&slot| source.parities[slot] != pivot);
        let mut residual = vector(remaining.len(), progress)?;
        residual.extend(remaining.iter().map(|&slot| source.clause[slot]));
        let assume = ProofId(u32::try_from(index).map_err(|_| BuildError::ResourceLimit)?);
        current = candidate.add_resolution(residual, root, current, assume);
    }
    if !remaining.is_empty() {
        return Err(BuildError::InvalidProof);
    }
    Ok(candidate)
}

fn vector<T>(count: usize, progress: Progress<'_>) -> Result<Vec<T>, BuildError> {
    let bytes = count
        .checked_mul(size_of::<T>())
        .ok_or(BuildError::ResourceLimit)?;
    charge(progress, count, bytes)?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(count)
        .map_err(|_| BuildError::ResourceLimit)?;
    Ok(output)
}

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), BuildError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(BuildError::ResourceLimit)
    }
}

#[cfg(test)]
mod tests;
