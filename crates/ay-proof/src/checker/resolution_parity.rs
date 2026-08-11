// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Leading-`not` parity operations for argument-free resolution and RUP-style
//! pivot inference.

use ay_core::{TermId, TermStore};

use super::{decode_literal, SignedLiteral};

/// Decode a clause into a sorted, deduplicated parity-literal set.
///
/// #proof-tax: sorted `Vec`s avoid the three hash-table allocations that used
/// to dominate resolution-heavy checker profiles.
pub(super) fn clause_as_set(terms: &TermStore, clause: &[TermId]) -> Vec<SignedLiteral> {
    let mut set: Vec<SignedLiteral> = clause
        .iter()
        .map(|literal| decode_literal(terms, *literal))
        .collect();
    set.sort_unstable();
    set.dedup();
    set
}

#[inline]
fn set_contains(set: &[SignedLiteral], lit: SignedLiteral) -> bool {
    set.binary_search(&lit).is_ok()
}

pub(super) fn resolves_to(
    left: &[SignedLiteral],
    right: &[SignedLiteral],
    pivot: SignedLiteral,
    expected: &[SignedLiteral],
) -> bool {
    let neg_pivot = pivot.negated();
    if !set_contains(left, pivot) || !set_contains(right, neg_pivot) {
        return false;
    }

    // Check the sorted-set union after removing the pivot pair, without
    // allocating the resolvent on this hot binary path.
    let mut i = 0usize;
    let mut j = 0usize;
    let mut k = 0usize;
    loop {
        if i < left.len() && left[i] == pivot {
            i += 1;
            continue;
        }
        if j < right.len() && right[j] == neg_pivot {
            j += 1;
            continue;
        }
        let next = match (left.get(i), right.get(j)) {
            (None, None) => break,
            (Some(&left), None) => {
                i += 1;
                left
            }
            (None, Some(&right)) => {
                j += 1;
                right
            }
            (Some(&left), Some(&right)) => match left.cmp(&right) {
                std::cmp::Ordering::Less => {
                    i += 1;
                    left
                }
                std::cmp::Ordering::Greater => {
                    j += 1;
                    right
                }
                std::cmp::Ordering::Equal => {
                    i += 1;
                    j += 1;
                    left
                }
            },
        };
        if expected.get(k) != Some(&next) {
            return false;
        }
        k += 1;
    }
    k == expected.len()
}

fn resolve_clause(
    left: &[SignedLiteral],
    right: &[SignedLiteral],
    pivot: SignedLiteral,
) -> Option<Vec<SignedLiteral>> {
    let neg_pivot = pivot.negated();
    if !set_contains(left, pivot) || !set_contains(right, neg_pivot) {
        return None;
    }
    let mut resolvent: Vec<SignedLiteral> = left
        .iter()
        .copied()
        .filter(|literal| *literal != pivot)
        .chain(
            right
                .iter()
                .copied()
                .filter(|literal| *literal != neg_pivot),
        )
        .collect();
    resolvent.sort_unstable();
    resolvent.dedup();
    Some(resolvent)
}

pub(super) fn chain_resolve_candidates(
    acc: &[SignedLiteral],
    next: &[SignedLiteral],
    max_pairs: usize,
) -> Vec<Vec<SignedLiteral>> {
    let mut pivots: Vec<SignedLiteral> = Vec::new();
    for &left in acc {
        if !set_contains(next, left.negated()) {
            continue;
        }
        pivots.push(left);
        if pivots.len() > max_pairs {
            return Vec::new();
        }
    }

    pivots
        .into_iter()
        .filter_map(|pivot| resolve_clause(acc, next, pivot))
        .collect()
}
