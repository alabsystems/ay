// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

//! Frozen pre-cancellation reader orchestration, for live-path/error parity.

use super::*;

pub(super) fn recheck(bundle: &SerializableProofBundle) -> Result<BundleReCheck, ProofCheckError> {
    if bundle.schema != PROOF_BUNDLE_SCHEMA {
        return Err(ProofCheckError::BundleSchemaMismatch {
            expected: PROOF_BUNDLE_SCHEMA.to_string(),
            found: bundle.schema.clone(),
        });
    }
    let declaration_term_symbols = preflight_bundle(bundle)?;
    let terms = TermStore::from_entries_with_progress(
        &bundle.term_entries,
        bundle.true_term,
        bundle.false_term,
        bundle.var_counter,
        &mut |_, _| true,
    )
    .map_err(|_| ProofCheckError::ResourceLimit)?;
    let datatype_declarations = (!bundle.datatype_declarations.is_empty())
        .then_some(bundle.datatype_declarations.as_slice());
    let constructor_selectors = (!bundle.constructor_selectors.is_empty())
        .then_some(bundle.constructor_selectors.as_slice());
    crate::checker::validate_datatype_signature_context(
        &terms,
        datatype_declarations,
        constructor_selectors,
        &bundle.datatype_member_signatures,
    )?;
    let proof = Proof::from_steps(bundle.steps.clone());
    let names = crate::checker::quantifier::authenticate_bundle_skolems(
        &proof,
        &terms,
        &bundle.obligation_assertions,
        &declaration_term_symbols,
    )?;
    let terms = terms
        .with_skolem_symbols_with_progress(names, &mut |_, _| true)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    let quality = crate::check_proof_strict_with_typed_context(
        &proof,
        &terms,
        datatype_declarations,
        constructor_selectors,
        &bundle.datatype_member_signatures,
        Some(&bundle.obligation_assertions),
    )?;
    let assume_terms = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    Ok(BundleReCheck {
        quality,
        assume_terms,
    })
}
