// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-syntax literal operations for pivot-directed Alethe resolution.

use ay_core::{TermData, TermId, TermStore};

/// A resolution literal with its exact number of authored leading `not`s.
///
/// Argument-free resolution and RUP normalize arbitrary leading-`not` parity.
/// The explicit `(pivot, polarity)` form instead removes one syntactic outer
/// negation and preserves every untouched literal in the resolvent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct ResolutionLiteral {
    atom: TermId,
    negation_depth: usize,
}

impl ResolutionLiteral {
    pub(super) fn with_outer_not(self) -> Option<Self> {
        Some(Self {
            atom: self.atom,
            negation_depth: self.negation_depth.checked_add(1)?,
        })
    }

    fn is_complement_of(self, other: Self) -> bool {
        self.atom == other.atom && self.negation_depth.abs_diff(other.negation_depth) == 1
    }
}

pub(super) fn decode_literal(terms: &TermStore, literal: TermId) -> ResolutionLiteral {
    let mut atom = literal;
    let mut negation_depth = 0usize;
    while let TermData::Not(inner) = terms.get(atom) {
        atom = *inner;
        negation_depth += 1;
    }
    ResolutionLiteral {
        atom,
        negation_depth,
    }
}

/// Decode a clause into a sorted exact-literal set, rejecting duplicate
/// occurrences.
///
/// #proof-tax: this used to build a `DetHashSet` per clause per resolution
/// step — three hash-table allocations + rehashes for every checked step,
/// which dominated the checker's profile on resolution-heavy proofs. A sorted
/// `Vec` has the same lookup cost profile at a fraction of the cost for typical
/// conflict-analysis clauses. The explicit-argument Alethe rule is
/// occurrence-sensitive, though: its checker consumes one directed pivot, so
/// silently deduplicating here would accept a conclusion that omitted a
/// remaining duplicate literal.
pub(super) fn clause_as_unique_set(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<Vec<ResolutionLiteral>> {
    let mut set: Vec<ResolutionLiteral> = clause
        .iter()
        .map(|literal| decode_literal(terms, *literal))
        .collect();
    set.sort_unstable();
    (!set.windows(2).any(|pair| pair[0] == pair[1])).then_some(set)
}

#[inline]
fn set_contains(set: &[ResolutionLiteral], lit: ResolutionLiteral) -> bool {
    set.binary_search(&lit).is_ok()
}

pub(super) fn resolve_clause(
    left: &[ResolutionLiteral],
    right: &[ResolutionLiteral],
    left_pivot: ResolutionLiteral,
    right_pivot: ResolutionLiteral,
) -> Option<Vec<ResolutionLiteral>> {
    if !left_pivot.is_complement_of(right_pivot)
        || !set_contains(left, left_pivot)
        || !set_contains(right, right_pivot)
    {
        return None;
    }

    let mut resolvent: Vec<ResolutionLiteral> = left
        .iter()
        .copied()
        .filter(|literal| *literal != left_pivot)
        .chain(
            right
                .iter()
                .copied()
                .filter(|literal| *literal != right_pivot),
        )
        .collect();
    resolvent.sort_unstable();
    // A literal shared by the two residual clauses would occur twice in the
    // exact Alethe resolvent. This checker intentionally supports only the
    // duplicate-free directed subset; rejecting is safer than collapsing the
    // two occurrences and accepting an externally different conclusion.
    (!resolvent.windows(2).any(|pair| pair[0] == pair[1])).then_some(resolvent)
}
