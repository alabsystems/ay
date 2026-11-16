// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact declaration namespaces; every owning insertion is charged first.
//!
//! An identity is the raw SMT-LIB symbol text, so the empty text of the quoted
//! symbol `||` is an identity like any other: no check here tests a name for
//! emptiness. The name-based refusals here are a duplicate signature, datatype
//! or constructor name (`collect_signatures`, `collect_constructors`); a
//! selector list for an undeclared or already listed constructor
//! (`collect_selectors`); a cross-role ambiguity between constructors, derived
//! `is-<constructor>` testers and selectors (`insert_expected`); and a member
//! table that differs from the declarations (`validate_exact_members`).
//! Outside this module, `signatures::validate_declared` and
//! `terms::validate_occurrences` hold every member, the empty one included, to
//! its exact typed signature.

use super::{
    BTreeMap, BTreeSet, ContextMeter, DatatypeDecls, DatatypeMemberSignature, DatatypeSignatureMap,
    ProofCheckError, SelectorDecls,
};

pub(super) fn collect_signatures<'a>(
    source: &'a [DatatypeMemberSignature],
    meter: &mut ContextMeter<'_>,
) -> Result<DatatypeSignatureMap<'a>, ProofCheckError> {
    let mut signatures = BTreeMap::new();
    for signature in source {
        meter.charge(1, 0)?;
        // Even an unused signature belongs to the authority surface. Reject
        // excessive depth before later recursive sort equality can inspect it.
        for sort in &signature.argument_sorts {
            meter.sort(sort, 0)?;
        }
        meter.sort(&signature.result_sort, 0)?;
        meter.insert::<&str, &DatatypeMemberSignature>(&signature.identity, signatures.len())?;
        if signatures
            .insert(signature.identity.as_str(), signature)
            .is_some()
        {
            return meter.invalid(
                "datatype member signature is duplicated",
                &[&signature.identity],
            );
        }
    }
    Ok(signatures)
}

fn insert_expected(
    name: &str,
    expected: &mut BTreeSet<String>,
    meter: &mut ContextMeter<'_>,
) -> Result<(), ProofCheckError> {
    meter.insert::<String, ()>(name, expected.len())?;
    let owned = meter.copy_name(name)?;
    if !expected.insert(owned) {
        return meter.invalid("datatype member identity is ambiguous", &[name]);
    }
    Ok(())
}

pub(super) fn collect_constructors<'a>(
    declarations: DatatypeDecls<'a>,
    expected: &mut BTreeSet<String>,
    meter: &mut ContextMeter<'_>,
) -> Result<BTreeMap<&'a str, &'a str>, ProofCheckError> {
    let mut datatypes = BTreeSet::new();
    let mut carriers = BTreeMap::new();
    for (datatype, constructors) in declarations {
        meter.insert::<&str, ()>(datatype, datatypes.len())?;
        if !datatypes.insert(datatype.as_str()) {
            return meter.invalid("datatype declaration name is duplicated", &[datatype]);
        }
        if constructors.is_empty() {
            return meter.invalid("datatype has no constructors", &[datatype]);
        }
        for constructor in constructors {
            meter.insert::<&str, &str>(constructor, carriers.len())?;
            if carriers
                .insert(constructor.as_str(), datatype.as_str())
                .is_some()
            {
                return meter.invalid("constructor declaration name is duplicated", &[constructor]);
            }
            insert_expected(constructor, expected, meter)?;
            let tester = meter.tester(constructor)?;
            insert_expected(&tester, expected, meter)?;
        }
    }
    Ok(carriers)
}

pub(super) fn collect_selectors<'a>(
    selectors: SelectorDecls<'a>,
    carriers: &BTreeMap<&str, &str>,
    expected: &mut BTreeSet<String>,
    meter: &mut ContextMeter<'_>,
) -> Result<BTreeMap<&'a str, &'a [String]>, ProofCheckError> {
    let mut lists = BTreeMap::new();
    for (constructor, fields) in selectors {
        meter.lookup(constructor, carriers.len())?;
        if !carriers.contains_key(constructor.as_str()) {
            return meter.invalid(
                "selector declaration references unknown constructor",
                &[constructor],
            );
        }
        meter.insert::<&str, &[String]>(constructor, lists.len())?;
        if lists
            .insert(constructor.as_str(), fields.as_slice())
            .is_some()
        {
            return meter.invalid(
                "selector declaration for constructor is duplicated",
                &[constructor],
            );
        }
        for selector in fields {
            insert_expected(selector, expected, meter)?;
        }
    }
    Ok(lists)
}

pub(super) fn validate_exact_members(
    signatures: &DatatypeSignatureMap<'_>,
    expected: &BTreeSet<String>,
    meter: &mut ContextMeter<'_>,
) -> Result<(), ProofCheckError> {
    // A borrowed ordered merge replaces two redundant allocated name sets.
    meter.iterate(signatures.len())?;
    meter.iterate(expected.len())?;
    let mut actual_names = signatures.keys();
    let mut expected_names = expected.iter();
    loop {
        // The whole linear iterator walk was charged before construction;
        // poll on each pair so a large registry remains interruptible.
        meter.charge(1, 0)?;
        match (actual_names.next(), expected_names.next()) {
            (None, None) => return Ok(()),
            (Some(actual), Some(wanted)) => {
                if !meter.equal_names(actual, wanted)? {
                    return meter.invalid(
                        "typed datatype member table is not exact (actual, expected)",
                        &[actual, wanted],
                    );
                }
            }
            (Some(extra), None) => {
                return meter.invalid("typed datatype member table has an extra member", &[extra]);
            }
            (None, Some(missing)) => {
                return meter.invalid(
                    "typed datatype member table has a missing member",
                    &[missing],
                );
            }
        }
    }
}
