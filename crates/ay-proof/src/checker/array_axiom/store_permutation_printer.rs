// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact clause extraction for checked Alethe store-permutation lowering.

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermId, TermStore};

use super::{
    equality_sides, parse_store_chain, ArrayStorePermutationPrinterTerms,
    MAX_STORE_PERMUTATION_CHAIN,
};

/// Return the exact primitive terms of a strict-checkable store permutation.
pub(crate) fn array_store_permutation_printer_terms(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ArrayStorePermutationPrinterTerms> {
    if clause.len() < 2
        || clause
            .iter()
            .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return None;
    }

    let mut found = None;
    for (row_position, &row) in clause.iter().enumerate() {
        let Some(candidate) = permutation_candidate(terms, clause, row_position, row) else {
            continue;
        };
        // An ambiguous clause carrying two permutation equalities is refused:
        // the printer must not pick which of them to derive.
        if found.is_some() {
            return None;
        }
        found = Some(candidate);
    }
    found
}

fn permutation_candidate(
    terms: &TermStore,
    clause: &[TermId],
    row_position: usize,
    row: TermId,
) -> Option<ArrayStorePermutationPrinterTerms> {
    let (left_array, right_array) = equality_sides(terms, row)?;
    if !matches!(terms.sort(left_array), Sort::Array(_))
        || terms.sort(left_array) != terms.sort(right_array)
    {
        return None;
    }
    let Sort::Array(array_sort) = terms.sort(left_array) else {
        return None;
    };
    let index_sort = array_sort.index_sort.clone();
    let left = parse_store_chain(terms, left_array)?;
    let right = parse_store_chain(terms, right_array)?;
    if left.base != right.base || left.entries.len() != right.entries.len() {
        return None;
    }
    let chain_len = left.entries.len();
    if !(2..=MAX_STORE_PERMUTATION_CHAIN).contains(&chain_len) {
        return None;
    }

    let indices: Vec<TermId> = left.entries.iter().map(|&(index, _)| index).collect();
    let distinct: DetHashSet<TermId> = indices.iter().copied().collect();
    if distinct.len() != chain_len || !same_entry_multiset(&left.entries, &right.entries) {
        return None;
    }
    let index_equalities = collect_index_equalities(terms, clause, row_position, &indices)?;
    Some(ArrayStorePermutationPrinterTerms {
        row,
        row_position,
        left_array,
        right_array,
        base: left.base,
        left: left.entries,
        right: right.entries,
        index_equalities,
        index_sort,
    })
}

fn same_entry_multiset(left: &[(TermId, TermId)], right: &[(TermId, TermId)]) -> bool {
    let mut left = left.to_vec();
    let mut right = right.to_vec();
    left.sort_unstable();
    right.sort_unstable();
    left == right
}

fn collect_index_equalities(
    terms: &TermStore,
    clause: &[TermId],
    row_position: usize,
    indices: &[TermId],
) -> Option<Vec<(TermId, usize, TermId, TermId)>> {
    let mut equalities = Vec::new();
    for (position, &first) in indices.iter().enumerate() {
        for &second in &indices[position + 1..] {
            let carried = clause.iter().enumerate().find_map(|(at, &literal)| {
                // The permutation equality must never double as its own side
                // condition, however the sorts happen to line up.
                if at == row_position {
                    return None;
                }
                let (lhs, rhs) = equality_sides(terms, literal)?;
                ((lhs, rhs) == (first, second) || (lhs, rhs) == (second, first))
                    .then_some((literal, at, lhs, rhs))
            })?;
            equalities.push(carried);
        }
    }
    Some(equalities)
}
