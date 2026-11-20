// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Leading-`not` parity operations for argument-free resolution and RUP-style
//! pivot inference.

use ay_core::{TermId, TermStore};

use super::{decode_literal, SignedLiteral};

/// Compare a binary resolution with its authored pivot by recording the two
/// polarities of each normalized atom in each of the three clauses. This is
/// the same set comparison as `resolves_to`, independent of order and repeated
/// occurrences. Keep the normal sorted representation for sparse atom ranges.
pub(super) fn dense_pivot_resolution(
    terms: &TermStore,
    left: &[TermId],
    right: &[TermId],
    expected: &[TermId],
    pivot: TermId,
) -> Option<bool> {
    let total = left
        .len()
        .checked_add(right.len())?
        .checked_add(expected.len())?;
    if total < 24 {
        return None;
    }
    let pivot = decode_literal(terms, pivot).atom;
    let mut literals = Vec::with_capacity(total);
    let max_width = total.saturating_mul(16).min(65_536);
    let mut low = usize::MAX;
    let mut high = 0;
    for &term in left.iter().chain(right).chain(expected) {
        let literal = decode_literal(terms, term);
        low = low.min(literal.atom.index());
        high = high.max(literal.atom.index());
        // The observed span can only grow as we decode further literals.
        if high - low >= max_width {
            return None;
        }
        literals.push(literal);
    }
    if !(low..=high).contains(&pivot.index()) {
        return Some(false);
    }
    let width = high.checked_sub(low)?.checked_add(1)?;
    // One byte per atom: two bits for each premise and for the conclusion.
    let mut membership = vec![0u8; width];
    let (left, rest) = literals.split_at(left.len());
    let (right, expected) = rest.split_at(right.len());
    for (clause, offset) in [(left, 0), (right, 2), (expected, 4)] {
        for literal in clause {
            let sign = if literal.positive { 1 } else { 2 };
            membership[literal.atom.index() - low] |= sign << offset;
        }
    }
    let pivot_flags = &mut membership[pivot.index() - low];
    let left = *pivot_flags & 3;
    let right = (*pivot_flags >> 2) & 3;
    let expected = *pivot_flags >> 4;
    let resolves = |remove_left, remove_right| {
        left & remove_left != 0
            && right & remove_right != 0
            && ((left & !remove_left) | (right & !remove_right)) == expected
    };
    if !resolves(1u8, 2u8) && !resolves(2u8, 1u8) {
        return Some(false);
    }
    *pivot_flags = 0;
    Some(
        membership
            .iter()
            .all(|&flags| ((flags | flags >> 2) & 3) == flags >> 4),
    )
}

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

#[cfg(test)]
mod dense_tests {
    use super::*;
    use ay_core::Sort;

    #[test]
    fn sparse_atom_numbers_keep_the_existing_resolution_check() {
        let mut terms = TermStore::new();
        let pivot = terms.mk_var("p", Sort::Bool);
        let negative = terms.mk_not_raw(pivot);
        for i in 0..1_024 {
            terms.mk_var(&format!("pad{i}"), Sort::Bool);
        }
        let high = terms.mk_var("high", Sort::Bool);
        let mut left = vec![high; 24];
        left.push(pivot);
        assert_eq!(
            dense_pivot_resolution(&terms, &left, &[negative], &[high], pivot),
            None
        );
        assert!(super::super::is_valid_binary_resolution(
            &terms,
            &left,
            &[negative],
            &[high],
            Some(pivot)
        ));
        assert!(!super::super::is_valid_binary_resolution(
            &terms,
            &left,
            &[negative],
            &[],
            Some(pivot)
        ));
    }

    #[test]
    fn dense_pivots_agree_with_the_sorted_resolution_on_both_polarities() {
        let mut terms = TermStore::new();
        let pivot = terms.mk_var("p", Sort::Bool);
        let other = terms.mk_var("q", Sort::Bool);
        let padding = terms.mk_var("pad", Sort::Bool);
        let not_other = terms.mk_not_raw(other);
        let positive = terms.mk_not_raw(not_other);
        let negated = terms.mk_not_raw(pivot);
        let negative = terms.mk_not_raw(other);
        let values = [pivot, negated, positive, negative];
        for mask in 0..4096u16 {
            let clause = |offset: u16| {
                let mut result = vec![padding; 8];
                for (i, &value) in values.iter().enumerate() {
                    if mask & (1 << (offset + i as u16)) != 0 {
                        result.extend([value, value]);
                    }
                }
                result
            };
            let (left, right, mut expected) = (clause(0), clause(4), clause(8));
            expected.reverse();
            let l = clause_as_set(&terms, &left);
            let r = clause_as_set(&terms, &right);
            let c = clause_as_set(&terms, &expected);
            let p = decode_literal(&terms, pivot);
            let oracle = resolves_to(&l, &r, p, &c) || resolves_to(&l, &r, p.negated(), &c);
            assert_eq!(
                dense_pivot_resolution(&terms, &left, &right, &expected, negated),
                Some(oracle),
                "mask {mask}"
            );
        }
    }
}
