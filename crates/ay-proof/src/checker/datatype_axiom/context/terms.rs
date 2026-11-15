// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Global member occurrences, including unreachable and malformed raw nodes.

use ay_core::{Symbol, TermData, TermId};

use super::{
    ContextMeter, DatatypeMemberSignature, DatatypeSignatureMap, ProofCheckError, Sort, TermStore,
};

pub(super) fn checked_sort<'a>(
    terms: &'a TermStore,
    term: TermId,
    identity: &str,
    meter: &mut ContextMeter<'_>,
) -> Result<&'a Sort, ProofCheckError> {
    meter.charge(1, 0)?;
    if term.index() >= terms.len() {
        return meter.invalid("datatype member references a missing term", &[identity]);
    }
    Ok(terms.sort(term))
}

pub(super) fn validate_occurrences(
    terms: &TermStore,
    signatures: &DatatypeSignatureMap<'_>,
    meter: &mut ContextMeter<'_>,
) -> Result<(), ProofCheckError> {
    // Every rejection below is keyed on a node naming a registered member, so
    // with no member signatures no node can fail: skip the O(|terms|) walk
    // (and its metering, see `meter_authentication_payload`) instead of
    // charging a whole session term store to prove nothing.
    if signatures.is_empty() {
        return Ok(());
    }
    for node_index in 0..terms.len() {
        meter.charge(1, 0)?;
        let Ok(raw) = u32::try_from(node_index) else {
            return meter.invalid(
                "term-store index does not fit the TermId representation",
                &[],
            );
        };
        let term = TermId::new(raw);
        match terms.get(term) {
            TermData::Var(identity, _) => {
                meter.lookup(identity, signatures.len())?;
                if let Some(signature) = signatures.get(identity.as_str()) {
                    validate_variable(terms, term, identity, signature, meter)?;
                }
            }
            TermData::App(Symbol::Named(identity), arguments) => {
                meter.lookup(identity, signatures.len())?;
                if let Some(signature) = signatures.get(identity.as_str()) {
                    validate_application(terms, term, identity, arguments, signature, meter)?;
                }
            }
            TermData::App(Symbol::Indexed(identity, _), _) => {
                meter.lookup(identity, signatures.len())?;
                if signatures.contains_key(identity.as_str()) {
                    return meter
                        .invalid("datatype member term uses an indexed symbol", &[identity]);
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_variable(
    terms: &TermStore,
    term: TermId,
    identity: &str,
    signature: &DatatypeMemberSignature,
    meter: &mut ContextMeter<'_>,
) -> Result<(), ProofCheckError> {
    if signature.nullary_term != Some(term) {
        return meter.invalid(
            "datatype member variable is not its declaration's exact nullary constructor binding",
            &[identity],
        );
    }
    if !meter.equal_sorts(terms.sort(term), &signature.result_sort)? {
        return meter.invalid(
            "datatype member variable has an incorrect result sort",
            &[identity],
        );
    }
    Ok(())
}

fn validate_application(
    terms: &TermStore,
    term: TermId,
    identity: &str,
    arguments: &[TermId],
    signature: &DatatypeMemberSignature,
    meter: &mut ContextMeter<'_>,
) -> Result<(), ProofCheckError> {
    // Keep BOTH exact nullary representations: the pinned Var above, and a
    // zero-argument App of the authenticated constructor identity here.
    if arguments.len() != signature.argument_sorts.len() {
        return meter.invalid(
            "datatype member application has an incorrect arity",
            &[identity],
        );
    }
    for (&argument, expected_sort) in arguments.iter().zip(&signature.argument_sorts) {
        let actual_sort = checked_sort(terms, argument, identity, meter)?;
        if !meter.equal_sorts(actual_sort, expected_sort)? {
            return meter.invalid(
                "datatype member application has an incorrect argument sort",
                &[identity],
            );
        }
    }
    if !meter.equal_sorts(terms.sort(term), &signature.result_sort)? {
        return meter.invalid(
            "datatype member application has an incorrect result sort",
            &[identity],
        );
    }
    Ok(())
}
