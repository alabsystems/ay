// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-metered copying, not semantic authentication or a publication permit.

use std::mem::size_of;

use super::*;

mod cloning;
mod comparison;
mod payload;
#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

impl SerializableProofBundle {
    /// Copy a proof and its complete positional term snapshot under a shared
    /// caller-owned work/byte budget and cancellation callback.
    ///
    /// The callback receives incremental charges BEFORE the corresponding work
    /// or allocation. Returning false aborts with `ResourceLimit`, including at
    /// the final zero-cost cancellation poll. No source input is mutated.
    /// Successful copying grants no proof authority: independent strict replay
    /// and external problem binding remain mandatory. JSON decoding and the
    /// existing unmetered replay convenience function are outside this envelope.
    pub fn from_proof_with_progress(
        proof: &Proof,
        terms: &TermStore,
        obligation_assertions: &[TermId],
        progress: Progress<'_>,
    ) -> Result<Self, ProofCheckError> {
        Self::from_proof_with_typed_context_and_progress(
            proof,
            terms,
            obligation_assertions,
            &[],
            &[],
            &[],
            progress,
        )
    }

    /// Borrow and copy the full typed declaration context under the SAME
    /// callback as the proof and snapshot. No caller-side context clones are
    /// needed. Even unused snapshot entries and nested declaration sorts are
    /// charged; checker-only stores' intentionally empty heap ledgers are not
    /// used as a price. Excessively deep sorts and unknown future owning proof
    /// variants fail closed because their copies cannot be safely priced.
    ///
    /// This only constructs untrusted certificate data. It does not validate
    /// datatype declarations, restore Skolem authority, or certify UNSAT.
    pub fn from_proof_with_typed_context_and_progress(
        proof: &Proof,
        terms: &TermStore,
        obligation_assertions: &[TermId],
        datatype_declarations: &[(String, Vec<String>)],
        constructor_selectors: &[(String, Vec<String>)],
        datatype_member_signatures: &[DatatypeMemberSignature],
        progress: Progress<'_>,
    ) -> Result<Self, ProofCheckError> {
        charge(progress, 0, 0)?;
        charge(
            progress,
            PROOF_BUNDLE_SCHEMA.len(),
            PROOF_BUNDLE_SCHEMA.len(),
        )?;
        let schema = PROOF_BUNDLE_SCHEMA.to_owned();
        let term_entries = terms
            .entries_snapshot_with_progress(progress)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        let steps = copy_steps(&proof.steps, progress)?;
        let obligation_assertions = copy_slice(obligation_assertions, progress)?;
        let datatype_declarations = copy_names(datatype_declarations, progress)?;
        let constructor_selectors = copy_names(constructor_selectors, progress)?;
        let datatype_member_signatures = copy_signatures(datatype_member_signatures, progress)?;
        let mut declared_function_identities =
            vector(terms.declared_function_identities().len(), progress)?;
        for identity in terms.declared_function_identities() {
            declared_function_identities.push(copy_string(identity, progress)?);
        }
        let (true_term, false_term) = terms.boolean_constant_ids();
        let bundle = Self {
            schema,
            steps,
            term_entries,
            true_term,
            false_term,
            var_counter: terms.var_counter(),
            obligation_assertions,
            datatype_declarations,
            constructor_selectors,
            datatype_member_signatures,
            declared_function_identities,
        };
        charge(progress, 0, 0)?;
        Ok(bundle)
    }
}

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn product(count: usize, width: usize) -> Result<usize, ProofCheckError> {
    count
        .checked_mul(width)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn vector<T>(len: usize, progress: Progress<'_>) -> Result<Vec<T>, ProofCheckError> {
    charge(progress, len, product(len, size_of::<T>())?)?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(len)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    Ok(output)
}

fn copy_slice<T: Copy>(input: &[T], progress: Progress<'_>) -> Result<Vec<T>, ProofCheckError> {
    let mut output = vector(input.len(), progress)?;
    output.extend_from_slice(input);
    Ok(output)
}

fn copy_string(input: &str, progress: Progress<'_>) -> Result<String, ProofCheckError> {
    charge(progress, input.len(), input.len())?;
    Ok(input.to_owned())
}

fn copy_names(
    input: &[(String, Vec<String>)],
    progress: Progress<'_>,
) -> Result<Vec<(String, Vec<String>)>, ProofCheckError> {
    let mut output = vector(input.len(), progress)?;
    for (name, members) in input {
        let name = copy_string(name, progress)?;
        let mut copied_members = vector(members.len(), progress)?;
        for member in members {
            copied_members.push(copy_string(member, progress)?);
        }
        output.push((name, copied_members));
    }
    Ok(output)
}

fn copy_signatures(
    input: &[DatatypeMemberSignature],
    progress: Progress<'_>,
) -> Result<Vec<DatatypeMemberSignature>, ProofCheckError> {
    let mut output = vector(input.len(), progress)?;
    for signature in input {
        let identity = copy_string(&signature.identity, progress)?;
        let mut argument_sorts = vector(signature.argument_sorts.len(), progress)?;
        for sort in &signature.argument_sorts {
            payload::sort(sort, progress, 0)?;
            argument_sorts.push(sort.clone());
        }
        payload::sort(&signature.result_sort, progress, 0)?;
        output.push(DatatypeMemberSignature {
            identity,
            argument_sorts,
            result_sort: signature.result_sort.clone(),
            nullary_term: signature.nullary_term,
        });
    }
    Ok(output)
}

pub(super) fn copy_steps(
    input: &[ProofStep],
    progress: Progress<'_>,
) -> Result<Vec<ProofStep>, ProofCheckError> {
    let mut output = vector(input.len(), progress)?;
    for step in input {
        payload::step(step, progress)?;
        // The borrowed step cannot change between pricing and cloning.
        charge(progress, 0, 0)?;
        output.push(step.clone());
    }
    Ok(output)
}
