// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, TermData};

pub(super) fn validate_bindings(
    terms: &TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    clause: &[TermId],
    progress: Progress<'_>,
) -> CheckResult<()> {
    charge(progress, 3, 0)?;
    let count = assertions
        .len()
        .checked_add(assumptions.len())
        .filter(|&count| count <= NraSosCertificate::MAX_CLAUSE_SLOTS)
        .ok_or(NraSosQueryCheckError::ResourceLimit)?;
    if count == 0 {
        return Err(NraSosQueryCheckError::EmptyQuery);
    }
    if clause.len() != count {
        return Err(NraSosQueryCheckError::SourceArity);
    }
    for (position, (&root, &literal)) in
        assertions.iter().chain(assumptions).zip(clause).enumerate()
    {
        charge(progress, 5, 0)?;
        for id in [root, literal] {
            if id.index() >= terms.len() {
                return Err(NraSosQueryCheckError::InvalidRoot { root: id });
            }
            if !matches!(terms.sort(id), Sort::Bool) {
                return Err(NraSosQueryCheckError::NonBooleanRoot { root: id });
            }
        }
        if !matches!(terms.get(literal), TermData::Not(inner) if *inner == root) {
            return Err(NraSosQueryCheckError::SourceMismatch { position });
        }
    }
    charge(progress, 0, 0)
}

pub(super) fn fresh_snapshot(terms: &TermStore, progress: Progress<'_>) -> CheckResult<TermStore> {
    charge(progress, 3, 0)?;
    let entries = terms
        .entries_snapshot_with_progress(progress)
        .map_err(|_| NraSosQueryCheckError::ResourceLimit)?;
    let (true_term, false_term) = terms.boolean_constant_ids();
    TermStore::from_entries_with_progress(
        &entries,
        true_term,
        false_term,
        terms.var_counter(),
        progress,
    )
    .map_err(|_| NraSosQueryCheckError::ResourceLimit)
}
