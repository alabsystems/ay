// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exclude vacuous literal-index FC pairs before reserving candidate space.

use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::{BigInt, Sign};

/// A positive result proves that the FC antecedent is false independently of
/// the SAT assignment. All other pairs retain their existing priority/budget.
///
/// Raw interning need not normalize literals, so authenticate native scalar
/// metadata and canonical unsigned range before comparing borrowed payloads.
/// No payload is copied or reduced modulo its width. This does not bound the
/// caller's quadratic pair scan; comparison visits at most the existing literal
/// payloads, while width/range checks allocate nothing.
pub(super) fn provably_distinct_literal_indices(
    terms: &TermStore,
    array: TermId,
    left: TermId,
    right: TermId,
) -> bool {
    let Sort::Array(array_sort) = terms.sort(array) else {
        return false;
    };
    let Sort::BitVec(index_sort) = &array_sort.index_sort else {
        return false;
    };
    if index_sort.width == 0 {
        return false;
    }
    match (
        canonical_literal(terms, left, index_sort.width),
        canonical_literal(terms, right, index_sort.width),
    ) {
        (Some(left), Some(right)) => left != right,
        _ => false,
    }
}

fn canonical_literal(terms: &TermStore, index: TermId, width: u32) -> Option<&BigInt> {
    let Sort::BitVec(sort) = terms.sort(index) else {
        return None;
    };
    let TermData::Const(Constant::BitVec {
        value,
        width: literal_width,
    }) = terms.get(index)
    else {
        return None;
    };
    (sort.width == width
        && *literal_width == width
        && value.sign() != Sign::Minus
        && value.bits() <= u64::from(width))
    .then_some(value)
}

#[cfg(test)]
mod tests;
