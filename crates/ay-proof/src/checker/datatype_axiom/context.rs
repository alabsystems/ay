// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact datatype authority, with caller-owned incremental resource control.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    DatatypeDecls, DatatypeMemberSignature, ProofCheckError, SelectorDecls, Sort, TermStore,
};

mod meter;
mod registry;
mod signatures;
mod terms;
#[cfg(test)]
mod tests;

use meter::ContextMeter;
type DatatypeSignatureMap<'a> = BTreeMap<&'a str, &'a DatatypeMemberSignature>;

/// Compatibility entry point retaining exact, whole-store datatype authority.
pub(crate) fn validate_datatype_signature_context(
    terms: &TermStore,
    dt_decls: Option<DatatypeDecls<'_>>,
    ctor_selectors: Option<SelectorDecls<'_>>,
    member_signatures: &[DatatypeMemberSignature],
) -> Result<(), ProofCheckError> {
    validate_datatype_signature_context_with_progress(
        terms,
        dt_decls,
        ctor_selectors,
        member_signatures,
        &mut |_, _| true,
    )
}

/// Authenticate the exact declaration table and EVERY member occurrence,
/// including unused terms. Charges precede allocation and bounded operations;
/// a refusal or overdeep sort returns ResourceLimit, never datatype authority.
/// The callback retains the same allowance across the surrounding proof check.
pub(crate) fn validate_datatype_signature_context_with_progress(
    terms: &TermStore,
    dt_decls: Option<DatatypeDecls<'_>>,
    ctor_selectors: Option<SelectorDecls<'_>>,
    member_signatures: &[DatatypeMemberSignature],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut meter = ContextMeter::new(progress);
    meter.charge(1, 0)?;
    let signatures = registry::collect_signatures(member_signatures, &mut meter)?;
    let mut expected_members = BTreeSet::new();
    let carriers =
        registry::collect_constructors(dt_decls.unwrap_or(&[]), &mut expected_members, &mut meter)?;
    let selectors = registry::collect_selectors(
        ctor_selectors.unwrap_or(&[]),
        &carriers,
        &mut expected_members,
        &mut meter,
    )?;
    signatures::validate_declared(terms, &signatures, &carriers, &selectors, &mut meter)?;
    registry::validate_exact_members(&signatures, &expected_members, &mut meter)?;
    terms::validate_occurrences(terms, &signatures, &mut meter)?;
    meter.charge(0, 0)
}
