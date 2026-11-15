// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The deterministic prefix of an argument-free n-ary resolution chain,
//! folded incrementally.
//!
//! WHY. The bounded search in `validate_chain_resolution_rule` rebuilds the
//! sorted accumulator at every link, so a chain of `k` links over an
//! accumulator of `k` literals costs `Θ(k²)` even when no link is ambiguous —
//! the shape every n-ary `th_resolution` AY emits for a projection fan
//! (`or_pos` against one `or_neg` per disjunct, `and_neg` against one
//! `and_pos` per conjunct). Here the accumulator is one hash set: each link
//! finds its complementary pair by probing the set with the NEXT premise's
//! literals, removes the pivot and inserts the rest, so the fold costs the
//! total size of the premises.
//!
//! SAME SEMANTICS AS THE SEARCH. A link whose premise holds exactly one
//! literal complementary to the accumulator has exactly one resolvent, the
//! one the search would build: the accumulator without the pivot, united with
//! the premise without the pivot's complement, duplicates merged (both are
//! sets). A link with no complementary pair is where the search, too, finds
//! no resolvent on its single path, so the chain is invalid. The first link
//! with two or more pairs is handed back with the accumulator before it, and
//! the caller's bounded search continues from there exactly as before.

use super::{decode_literal, literal_set_bytes, SignedLiteral};
use ay_core::kani_compat::{det_hash_set_with_capacity, DetHashSet as HashSet};
use ay_core::{TermId, TermStore};

/// How far the incremental fold got.
pub(super) enum ChainFold {
    /// Every link resolved on exactly one complementary pair: the final
    /// accumulator.
    Complete(HashSet<SignedLiteral>),
    /// A link with no complementary pair against the accumulator.
    Stuck,
    /// The first link (`index` into the premises) with two or more
    /// complementary pairs, and the accumulator before it.
    Ambiguous {
        index: usize,
        accumulator: HashSet<SignedLiteral>,
    },
    /// The caller's meter refused the work.
    Refused,
}

/// Fold `premise_clauses[1..]` into `premise_clauses[0]` while every link is
/// unambiguous. `premise_clauses` must hold at least two clauses.
pub(super) fn fold_unambiguous_prefix(
    terms: &TermStore,
    premise_clauses: &[&[TermId]],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> ChainFold {
    let Some((first, links)) = premise_clauses.split_first() else {
        return ChainFold::Stuck;
    };
    let mut accumulator = det_hash_set_with_capacity(first.len());
    for &literal in *first {
        accumulator.insert(decode_literal(terms, literal));
    }
    for (offset, next) in links.iter().enumerate() {
        if !progress(next.len().saturating_add(1), literal_set_bytes(next.len())) {
            return ChainFold::Refused;
        }
        // The premise's literal whose complement the accumulator holds. A
        // repeated literal names the same pair; a second distinct one makes
        // the link ambiguous.
        let mut resolved: Option<SignedLiteral> = None;
        for &literal in *next {
            let literal = decode_literal(terms, literal);
            if !accumulator.contains(&literal.negated()) || resolved == Some(literal) {
                continue;
            }
            if resolved.is_some() {
                return ChainFold::Ambiguous {
                    index: offset + 1,
                    accumulator,
                };
            }
            resolved = Some(literal);
        }
        let Some(resolved) = resolved else {
            return ChainFold::Stuck;
        };
        accumulator.remove(&resolved.negated());
        for &literal in *next {
            let literal = decode_literal(terms, literal);
            if literal != resolved {
                accumulator.insert(literal);
            }
        }
    }
    ChainFold::Complete(accumulator)
}

#[cfg(test)]
#[path = "resolution_chain_fold_tests.rs"]
mod tests;
