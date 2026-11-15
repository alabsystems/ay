// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact ordered conjunction introduction, shared by validation and pricing.
//!
//! This path reads immediate IDs only. All other spellings retain the existing
//! recursive De Morgan matcher and its tree-sensitive charge.

use super::boolean::{decode_app, strip_not};
use ay_core::{Sort, TermId, TermStore};

pub(crate) fn and_neg_is_emitted_identity_shape(
    terms: &TermStore,
    clause: &[TermId],
    source_term: Option<TermId>,
) -> bool {
    let Some(source) = source_term else {
        return false;
    };
    if clause.first() != Some(&source)
        || terms.entry_stamp(source).is_none()
        || terms.sort(source) != &Sort::Bool
    {
        return false;
    }
    let Some(args) = decode_app(terms, source, "and") else {
        return false;
    };
    if args.is_empty() || args.len().checked_add(1) != Some(clause.len()) {
        return false;
    }
    clause[1..].iter().zip(args).all(|(&literal, &arg)| {
        terms.entry_stamp(literal).is_some()
            && terms.entry_stamp(arg).is_some()
            && terms.sort(literal) == &Sort::Bool
            && terms.sort(arg) == &Sort::Bool
            && strip_not(terms, literal) == Some(arg)
    })
}
