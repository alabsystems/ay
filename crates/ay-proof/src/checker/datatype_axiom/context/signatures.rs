// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructor, tester and selector signatures retain their exact authority.

use ay_core::TermData;

use super::{
    BTreeMap, ContextMeter, DatatypeMemberSignature, DatatypeSignatureMap, ProofCheckError, Sort,
    TermStore,
};

pub(super) fn validate_declared(
    terms: &TermStore,
    signatures: &DatatypeSignatureMap<'_>,
    carriers: &BTreeMap<&str, &str>,
    selectors: &BTreeMap<&str, &[String]>,
    meter: &mut ContextMeter<'_>,
) -> Result<(), ProofCheckError> {
    meter.iterate(carriers.len())?;
    for (&constructor, &datatype) in carriers {
        meter.lookup(constructor, selectors.len())?;
        let Some(&fields) = selectors.get(constructor) else {
            return meter.invalid(
                "constructor is missing its complete selector declaration",
                &[constructor],
            );
        };
        let signature =
            validate_constructor(terms, signatures, constructor, datatype, fields, meter)?;
        validate_tester(signatures, constructor, signature, meter)?;
        for (selector, expected_sort) in fields.iter().zip(&signature.argument_sorts) {
            let selected = lookup(signatures, selector, meter)?;
            if !unary_matches(selected, &signature.result_sort, expected_sort, meter)? {
                return meter.invalid(
                    "selector does not have its exact declared field signature",
                    &[selector],
                );
            }
            if selected.nullary_term.is_some() {
                return meter.invalid(
                    "selector unexpectedly carries a nullary constructor binding",
                    &[selector],
                );
            }
        }
    }
    Ok(())
}

fn lookup<'a>(
    signatures: &DatatypeSignatureMap<'a>,
    identity: &str,
    meter: &mut ContextMeter<'_>,
) -> Result<&'a DatatypeMemberSignature, ProofCheckError> {
    meter.lookup(identity, signatures.len())?;
    match signatures.get(identity).copied() {
        Some(signature) => Ok(signature),
        None => meter.invalid(
            "datatype member is missing its exact typed signature",
            &[identity],
        ),
    }
}

fn validate_constructor<'a>(
    terms: &TermStore,
    signatures: &DatatypeSignatureMap<'a>,
    constructor: &str,
    datatype: &str,
    fields: &[String],
    meter: &mut ContextMeter<'_>,
) -> Result<&'a DatatypeMemberSignature, ProofCheckError> {
    let signature = lookup(signatures, constructor, meter)?;
    let carrier = match &signature.result_sort {
        Sort::Uninterpreted(name) => Some(name.as_str()),
        Sort::Datatype(definition) => Some(definition.name.as_str()),
        _ => None,
    };
    let carrier_matches = match carrier {
        Some(carrier) => meter.equal_names(carrier, datatype)?,
        None => false,
    };
    if !carrier_matches {
        return meter.invalid(
            "constructor result sort does not match its datatype",
            &[constructor, datatype],
        );
    }
    if signature.argument_sorts.len() != fields.len() {
        return meter.invalid(
            "constructor typed arity disagrees with declared selectors",
            &[constructor],
        );
    }
    match (signature.argument_sorts.is_empty(), signature.nullary_term) {
        (true, Some(term)) => {
            let actual_sort = super::terms::checked_sort(terms, term, constructor, meter)?;
            let same_name = match terms.get(term) {
                TermData::Var(identity, _) => meter.equal_names(identity, constructor)?,
                _ => false,
            };
            if !same_name || !meter.equal_sorts(actual_sort, &signature.result_sort)? {
                return meter.invalid("nullary constructor does not bind its exact same-name variable and result sort", &[constructor]);
            }
        }
        (true, None) => {
            return meter.invalid(
                "nullary constructor is missing its exact bound term",
                &[constructor],
            )
        }
        (false, Some(_)) => {
            return meter.invalid(
                "non-nullary constructor unexpectedly binds a nullary term",
                &[constructor],
            )
        }
        (false, None) => {}
    }
    Ok(signature)
}

fn unary_matches(
    signature: &DatatypeMemberSignature,
    input: &Sort,
    output: &Sort,
    meter: &mut ContextMeter<'_>,
) -> Result<bool, ProofCheckError> {
    let [actual_input] = signature.argument_sorts.as_slice() else {
        return Ok(false);
    };
    Ok(meter.equal_sorts(actual_input, input)?
        && meter.equal_sorts(&signature.result_sort, output)?)
}

fn validate_tester(
    signatures: &DatatypeSignatureMap<'_>,
    constructor: &str,
    constructor_signature: &DatatypeMemberSignature,
    meter: &mut ContextMeter<'_>,
) -> Result<(), ProofCheckError> {
    let tester = meter.tester(constructor)?;
    let signature = lookup(signatures, &tester, meter)?;
    if !unary_matches(
        signature,
        &constructor_signature.result_sort,
        &Sort::Bool,
        meter,
    )? {
        return meter.invalid(
            "tester does not have the exact constructor-carrier to Bool signature",
            &[&tester],
        );
    }
    if signature.nullary_term.is_some() {
        return meter.invalid(
            "tester unexpectedly carries a nullary constructor binding",
            &[&tester],
        );
    }
    Ok(())
}
