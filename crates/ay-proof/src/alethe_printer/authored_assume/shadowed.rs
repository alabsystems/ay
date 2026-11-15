// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact canonical assumption spellings for bounded shadowed store chains.
//!
//! This path checks textual identity only. It never bridges different source
//! spellings, and it retains the ordinary node, payload and aggregate bounds.
//! The separate store-spine allowance does not widen equivalence recursion.

use super::bounds::{canonical_term_is_bounded_with_depth, CanonicalRenderBound};
use super::{MAX_EQUIVALENCE_BYTES, MAX_EQUIVALENCE_DEPTH};
use crate::checker::shadowed_stores::{shadowed_stores, MAX_SHADOWED_STORES};
use ay_core::{TermData, TermId, TermStore};

pub(super) fn exact_input_bytes(terms: &TermStore, term: TermId, surface: &str) -> Option<usize> {
    if surface.len() > MAX_EQUIVALENCE_BYTES {
        return None;
    }
    let TermData::Not(equality) = terms.get(term) else {
        return None;
    };
    shadowed_stores(terms, &[*equality])?;
    if canonical_term_is_bounded_with_depth(
        terms,
        term,
        MAX_EQUIVALENCE_DEPTH + MAX_SHADOWED_STORES,
    ) != CanonicalRenderBound::Bounded
    {
        return None;
    }
    let canonical = crate::render_term_canonical(terms, term);
    let input_bytes = surface.len().checked_add(canonical.len())?;
    (canonical == surface && input_bytes <= MAX_EQUIVALENCE_BYTES).then_some(input_bytes)
}

#[cfg(test)]
#[path = "shadowed_tests.rs"]
mod tests;
