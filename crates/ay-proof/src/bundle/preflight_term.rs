// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed positional term validation; never interns or repairs the snapshot.

use std::collections::BTreeSet;
use std::mem::size_of;

use super::*;

mod shape;
#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

fn add(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn invalid<T>(
    index: usize,
    message: &'static str,
    progress: Progress<'_>,
) -> Result<T, ProofCheckError> {
    let bound = mul(add(message.len(), 64)?, 4)?;
    charge(progress, bound, bound)?;
    Err(malformed_bundle(format!("term t{index} {message}")))
}

fn prior_sort<'a>(
    entries: &'a [(TermData, Sort)],
    index: usize,
    child: TermId,
    progress: Progress<'_>,
) -> Result<&'a Sort, ProofCheckError> {
    charge(progress, 1, 0)?;
    if child.index() >= index {
        return invalid(index, "references non-prior term", progress);
    }
    match entries.get(child.index()) {
        Some((_, sort)) => Ok(sort),
        None => invalid(index, "references missing term", progress),
    }
}

fn equal_sorts(
    left: &Sort,
    right: &Sort,
    index: usize,
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    // Both complete trees are inspected before derived Eq. Sort validation
    // debits two units per node and each retained name's length; its ordered
    // namespace operations are separately charged. That covers this following
    // comparison, including matching datatype names/fields and deep children.
    validate_sort_with_progress(left, index, "compared sort", 0, progress)?;
    validate_sort_with_progress(right, index, "compared sort", 0, progress)?;
    charge(progress, 0, 0)?;
    Ok(left == right)
}

fn unique_name<'a>(
    names: &mut BTreeSet<&'a str>,
    name: &'a str,
    index: usize,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    let levels = add(names.len().bit_width() as usize, 1)?;
    let comparisons = add(names.len(), 1)?.min(mul(levels, 12)?);
    charge(progress, mul(comparisons, add(name.len(), 1)?)?, 0)?;
    let slots = mul(add(levels, 1)?, 32)?;
    charge(
        progress,
        slots,
        mul(slots, add(size_of::<&str>(), size_of::<usize>())?)?,
    )?;
    if !names.insert(name) {
        return invalid(index, "repeats binding name", progress);
    }
    Ok(())
}

pub(super) fn validate_term_snapshot_with_progress(
    entries: &[(TermData, Sort)],
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    charge(progress, 1, 0)?;
    if entries.len() > u32::MAX as usize {
        return invalid(0, "snapshot exceeds TermId capacity", progress);
    }
    let mut canonical = preflight_canonical::CanonicalEntries::new();
    for (index, (data, sort)) in entries.iter().enumerate() {
        charge(progress, 1, 0)?;
        validate_sort_with_progress(sort, index, "recorded sort", 0, progress)?;
        shape::validate(entries, index, data, sort, progress)?;
        // Only complete shape-validated keys may enter hashing or equality.
        // The rational index never calls Ratio::cmp or trusts raw hashes for
        // equivalent nonreduced/negative-denominator values.
        if !canonical.insert(data, sort, progress)? {
            return invalid(
                index,
                "duplicates an earlier canonical term entry",
                progress,
            );
        }
    }
    charge(progress, 0, 0)
}
