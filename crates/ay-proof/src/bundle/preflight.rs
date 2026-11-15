// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compositional, borrowed bundle-shape validation under one caller envelope.
//!
//! Shape acceptance is not proof validity, typed declaration authority, or external
//! problem binding. Schema-tag checks belong to that separate replay layer.

use super::preflight_declarations::{
    validate_declaration_context_with_progress, validate_declared_constructor_terms_with_progress,
};
use super::preflight_proof::validate_proof_snapshot_with_progress;
use super::preflight_sort::validate_sort_with_progress;
use super::preflight_term::validate_term_snapshot_with_progress;
use super::*;

#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn invalid<T>(message: &'static str, progress: Progress<'_>) -> Result<T, ProofCheckError> {
    let work = message
        .len()
        .checked_add(1)
        .ok_or(ProofCheckError::ResourceLimit)?;
    charge(progress, work, message.len())?;
    Err(malformed_bundle(message))
}

fn validate_signatures(
    bundle: &SerializableProofBundle,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    for (index, signature) in bundle.datatype_member_signatures.iter().enumerate() {
        charge(progress, 1, 0)?;
        for sort in &signature.argument_sorts {
            charge(progress, 1, 0)?;
            validate_sort_with_progress(
                sort,
                index,
                "datatype member signature argument sort",
                0,
                progress,
            )?;
        }
        // Static roles avoid eagerly formatting/cloning untrusted identity
        // strings. The later typed-context checker owns identity/nullary-term
        // authentication; preflight only validates the complete owning sorts.
        validate_sort_with_progress(
            &signature.result_sort,
            index,
            "datatype member signature result sort",
            0,
            progress,
        )?;
    }
    charge(progress, 0, 0)
}

fn validate_bool_constant_id(
    entries: &[(TermData, Sort)],
    id: Option<TermId>,
    expected: bool,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    charge(progress, 1, 0)?;
    let Some(id) = id else {
        return invalid(
            if expected {
                "bundle is missing true_term"
            } else {
                "bundle is missing false_term"
            },
            progress,
        );
    };
    let Some((data, sort)) = entries.get(id.index()) else {
        return invalid(
            if expected {
                "true_term references term outside the snapshot"
            } else {
                "false_term references term outside the snapshot"
            },
            progress,
        );
    };
    if !matches!(sort, Sort::Bool)
        || !matches!(data, TermData::Const(Constant::Bool(value)) if *value == expected)
    {
        return invalid(
            if expected {
                "true_term is not the expected Boolean constant"
            } else {
                "false_term is not the expected Boolean constant"
            },
            progress,
        );
    }
    Ok(())
}

fn validate_obligations(
    bundle: &SerializableProofBundle,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    for assertion in &bundle.obligation_assertions {
        charge(progress, 1, 0)?;
        let Some((_, sort)) = bundle.term_entries.get(assertion.index()) else {
            return invalid(
                "obligation assertion references term outside the snapshot",
                progress,
            );
        };
        if !matches!(sort, Sort::Bool) {
            return invalid("obligation assertion must have sort Bool", progress);
        }
    }
    charge(progress, 0, 0)
}

pub(super) fn preflight_bundle_with_progress(
    bundle: &SerializableProofBundle,
    progress: Progress<'_>,
) -> Result<HashMap<String, &'static str>, ProofCheckError> {
    charge(progress, 0, 0)?;
    validate_term_snapshot_with_progress(&bundle.term_entries, progress)?;
    validate_signatures(bundle, progress)?;
    validate_bool_constant_id(&bundle.term_entries, bundle.true_term, true, progress)?;
    validate_bool_constant_id(&bundle.term_entries, bundle.false_term, false, progress)?;
    validate_obligations(bundle, progress)?;
    let declaration_term_symbols = validate_declaration_context_with_progress(bundle, progress)?;
    validate_declared_constructor_terms_with_progress(bundle, progress)?;
    validate_proof_snapshot_with_progress(&bundle.steps, &bundle.term_entries, progress)?;
    // Neither a checked prefix nor a partially built declaration namespace
    // escapes if a later phase or this final cancellation poll refuses.
    charge(progress, 0, 0)?;
    Ok(declaration_term_symbols)
}
