// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticate datatype-owned names and constructor uses before reconstruction.

use super::*;

mod meter;
#[cfg(test)]
mod tests;

use meter::DeclarationMeter;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

#[cfg(test)]
pub(super) fn validate_declaration_context(
    bundle: &SerializableProofBundle,
) -> Result<HashMap<String, &'static str>, ProofCheckError> {
    validate_declaration_context_with_progress(bundle, &mut |_, _| true)
}

/// Constructors, selectors, and exact `is-<constructor>` testers share one
/// case-sensitive term namespace. Datatype names occupy a separate namespace.
pub(super) fn validate_declaration_context_with_progress(
    bundle: &SerializableProofBundle,
    progress: Progress<'_>,
) -> Result<HashMap<String, &'static str>, ProofCheckError> {
    let mut meter = DeclarationMeter::new(progress);
    meter.charge(0, 0)?;
    let mut datatype_names = HashSet::default();
    let mut constructor_names = HashSet::default();
    let mut term_symbols = HashMap::default();
    for (datatype, constructors) in &bundle.datatype_declarations {
        meter.charge(1, 0)?;
        if datatype.is_empty() || !meter.insert_name(&mut datatype_names, datatype)? {
            meter.diagnostic(&[datatype])?;
            return Err(malformed_bundle(format!(
                "datatype declaration name {datatype:?} is empty or duplicated"
            )));
        }
        if constructors.is_empty() {
            meter.diagnostic(&[datatype])?;
            return Err(malformed_bundle(format!(
                "datatype {datatype:?} has no constructors"
            )));
        }
        for constructor in constructors {
            meter.charge(1, 0)?;
            if constructor.is_empty() || !meter.insert_name(&mut constructor_names, constructor)? {
                meter.diagnostic(&[constructor])?;
                return Err(malformed_bundle(format!(
                    "constructor declaration name {constructor:?} is empty or duplicated"
                )));
            }
            insert_declaration_term_symbol(
                &mut term_symbols,
                constructor,
                "a constructor",
                &mut meter,
            )?;
            let tester = meter.prefixed_name("is-", constructor)?;
            insert_declaration_term_symbol(
                &mut term_symbols,
                &tester,
                "a derived tester",
                &mut meter,
            )?;
        }
    }
    let mut selector_entries = HashSet::default();
    for (constructor, selectors) in &bundle.constructor_selectors {
        meter.charge(1, 0)?;
        meter.lookup(constructor, constructor_names.len())?;
        if !constructor_names.contains(constructor) {
            meter.diagnostic(&[constructor])?;
            return Err(malformed_bundle(format!(
                "selector declaration references unknown constructor {constructor:?}"
            )));
        }
        if !meter.insert_name(&mut selector_entries, constructor)? {
            meter.diagnostic(&[constructor])?;
            return Err(malformed_bundle(format!(
                "selector declaration for constructor {constructor:?} is duplicated"
            )));
        }
        for selector in selectors {
            meter.charge(1, 0)?;
            if selector.is_empty() {
                meter.diagnostic(&[selector, constructor])?;
                return Err(malformed_bundle(format!(
                    "selector name {selector:?} for constructor {constructor:?} is empty"
                )));
            }
            insert_declaration_term_symbol(&mut term_symbols, selector, "a selector", &mut meter)?;
        }
    }
    meter.charge(0, 0)?;
    Ok(term_symbols)
}

fn insert_declaration_term_symbol(
    symbols: &mut HashMap<String, &'static str>,
    name: &str,
    role: &'static str,
    meter: &mut DeclarationMeter<'_>,
) -> Result<(), ProofCheckError> {
    meter.name_map_entry(symbols, name)?;
    let owned = meter.prefixed_name("", name)?;
    symbols
        .try_reserve(1)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    if let Some(prior_role) = symbols.insert(owned, role) {
        meter.diagnostic(&[name, prior_role, role])?;
        return Err(malformed_bundle(format!(
            "datatype declaration term symbol {name:?} is ambiguous: declared as both {prior_role} and {role}"
        )));
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn validate_declared_constructor_terms(
    bundle: &SerializableProofBundle,
) -> Result<(), ProofCheckError> {
    validate_declared_constructor_terms_with_progress(bundle, &mut |_, _| true)
}

pub(super) fn validate_declared_constructor_terms_with_progress(
    bundle: &SerializableProofBundle,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    let mut meter = DeclarationMeter::new(progress);
    meter.charge(0, 0)?;
    for (node_index, (data, sort)) in bundle.term_entries.iter().enumerate() {
        meter.charge(1, 0)?;
        let (name, arity) = match data {
            TermData::Var(name, _) => (name.as_str(), 0),
            TermData::App(Symbol::Named(name), args) => (name.as_str(), args.len()),
            _ => continue,
        };
        let Some(datatype) = constructor_datatype(bundle, name, &mut meter)? else {
            continue;
        };
        let sort_matches = match sort {
            Sort::Uninterpreted(carrier) => meter.names_equal(carrier, datatype)?,
            Sort::Datatype(definition) => meter.names_equal(&definition.name, datatype)?,
            _ => false,
        };
        if !sort_matches {
            meter.diagnostic(&[name, datatype])?;
            return Err(malformed_bundle(format!(
                "declared constructor term t{node_index} `{name}` has a result sort outside datatype `{datatype}`"
            )));
        }
        if let Some(selectors) = constructor_selectors(bundle, name, &mut meter)? {
            if arity != selectors.len() {
                meter.diagnostic(&[name])?;
                return Err(malformed_bundle(format!(
                    "declared constructor term t{node_index} `{name}` has arity {arity}, expected {}",
                    selectors.len()
                )));
            }
        }
    }
    meter.charge(0, 0)?;
    Ok(())
}

fn constructor_datatype<'a>(
    bundle: &'a SerializableProofBundle,
    name: &str,
    meter: &mut DeclarationMeter<'_>,
) -> Result<Option<&'a str>, ProofCheckError> {
    // Keep forward first-match semantics, including for independently tested
    // malformed contexts. Namespace validation rejects duplicates separately.
    for (datatype, constructors) in &bundle.datatype_declarations {
        meter.charge(1, 0)?;
        for constructor in constructors {
            if meter.names_equal(constructor, name)? {
                return Ok(Some(datatype));
            }
        }
    }
    Ok(None)
}

fn constructor_selectors<'a>(
    bundle: &'a SerializableProofBundle,
    name: &str,
    meter: &mut DeclarationMeter<'_>,
) -> Result<Option<&'a [String]>, ProofCheckError> {
    // Missing selector entries intentionally leave arity unchecked here. The
    // later typed-context checker remains the signature authority.
    for (constructor, selectors) in &bundle.constructor_selectors {
        if meter.names_equal(constructor, name)? {
            return Ok(Some(selectors));
        }
    }
    Ok(None)
}
