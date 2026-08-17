// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Read-through permutation and same-index store-chain extensions.

use super::*;

/// Exact select-congruence and same-index shapes lowered through the general
/// under-array-equality printer machinery.
pub(super) fn under_array_eq_printer_terms(
    terms: &TermStore,
    literals: &[TermId],
    packed_or: Option<TermId>,
) -> Option<ArrayRowChainPrinterTerms> {
    // Sub-schema (D): exact select congruence. Keep this syntactically
    // separate from (B): accepting two unreduced endpoints in the general
    // ROW matcher would silently broaden all of its guarded-chain shapes.
    if let Some(congruence) = exact_array_read_congruence_terms(terms, literals) {
        let base_path = |root| RowChainPath {
            root,
            skips: Vec::new(),
            end: RowChainEnd::Base { base: root },
        };
        return Some(ArrayRowChainPrinterTerms::UnderArrayEq {
            conclusion: congruence.conclusion,
            array_eq_lit: congruence.array_eq_lit,
            eq_term: congruence.eq_term,
            left_target: congruence.left_read,
            right_target: congruence.right_read,
            read_index: congruence.read_index,
            left: base_path(congruence.left),
            right: base_path(congruence.right),
            packed_or,
        });
    }

    // Sub-schema (I). Lowered through the (B) machinery, exactly as (D) is:
    // reading both premise sides at their SHARED write index is a chain walk
    // that terminates immediately on the outermost entry, so each side's path
    // is a zero-skip `Value` end and the derivation the printer emits is the
    // `arrays_idx` / `cong` / `trans` argument the soundness note states.
    let same_index = same_index_store_value_equality_terms(terms, literals)?;
    Some(ArrayRowChainPrinterTerms::UnderArrayEq {
        conclusion: same_index.conclusion,
        array_eq_lit: same_index.array_eq_lit,
        eq_term: same_index.eq_term,
        left_target: same_index.left_value,
        right_target: same_index.right_value,
        read_index: same_index.write_index,
        left: RowChainPath {
            root: same_index.left_store,
            skips: Vec::new(),
            end: RowChainEnd::Value {
                outer: same_index.left_store,
                value: same_index.left_value,
            },
        },
        right: RowChainPath {
            root: same_index.right_store,
            skips: Vec::new(),
            end: RowChainEnd::Value {
                outer: same_index.right_store,
                value: same_index.right_value,
            },
        },
        packed_or,
    })
}

/// The two ARRAY terms a positive conclusion literal compares, for the two
/// accepted conclusion forms of the store-permutation schema:
///
/// * DIRECT — `(= L R)` with `L`, `R` of one array sort: the arrays themselves.
/// * READ-THROUGH — `(= (select L k) (select R k))`: the arrays underneath two
///   well-sorted reads taken at the SAME index term `k`.
///
/// The read-through form is a congruence corollary of the direct one and never
/// widens the schema: conditions (1)-(5) still have to hold of `L` and `R`, and
/// `L = R` entails `select(L,k) = select(R,k)` for every `k`. Requiring one
/// shared `k` term is what makes that entailment purely congruence; two
/// syntactically different index terms would need a premise this checker is not
/// given, so they fail closed here.
pub(super) fn permutation_conclusion_arrays(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, TermId)> {
    if matches!(terms.sort(lhs), Sort::Array(_)) && terms.sort(lhs) == terms.sort(rhs) {
        return Some((lhs, rhs));
    }
    let (left_array, left_index) = well_sorted_select_parts(terms, lhs)?;
    let (right_array, right_index) = well_sorted_select_parts(terms, rhs)?;
    if left_index != right_index || terms.sort(left_array) != terms.sort(right_array) {
        return None;
    }
    Some((left_array, right_array))
}

/// Conditions (1)-(5) of [`validate_array_store_permutation`], re-derived from
/// `terms` and the clause's own literals for the array pair `(lhs, rhs)`.
pub(super) fn chains_are_validated_permutation(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
    literals: &[TermId],
    pairs: &mut Option<PositiveEqPairs>,
) -> bool {
    if !matches!(terms.sort(lhs), Sort::Array(_)) || terms.sort(lhs) != terms.sort(rhs) {
        return false;
    }
    let (Some(left), Some(right)) = (parse_store_chain(terms, lhs), parse_store_chain(terms, rhs))
    else {
        return false;
    };
    // (1) same base array, (2) same chain length >= 2.
    if left.base != right.base || left.entries.len() != right.entries.len() {
        return false;
    }
    let n = left.entries.len();
    if n < 2 {
        return false;
    }
    // (3) pairwise distinct index TERMS on the left chain. Combined with
    // (4) this makes the right chain's indices distinct as well.
    let mut indices: Vec<TermId> = left.entries.iter().map(|&(i, _)| i).collect();
    let distinct: DetHashSet<TermId> = indices.iter().copied().collect();
    if distinct.len() != n {
        return false;
    }
    // (4) the two chains write the same multiset of (index, value) pairs.
    let mut left_pairs = left.entries.clone();
    let mut right_pairs = right.entries.clone();
    left_pairs.sort_unstable();
    right_pairs.sort_unstable();
    if left_pairs != right_pairs {
        return false;
    }
    // (5) one `(= i_p i_q)` literal per unordered index pair.
    let eqs = pairs.get_or_insert_with(|| PositiveEqPairs::collect(terms, literals));
    indices.sort_unstable();
    indices
        .iter()
        .enumerate()
        .all(|(p, &ip)| indices[p + 1..].iter().all(|&iq| eqs.contains(ip, iq)))
}

/// The primitive terms of a sub-schema (I) clause.
pub(super) struct SameIndexStoreValueTerms {
    /// The `(= v w)` conclusion literal.
    conclusion: TermId,
    /// The `(not (= L R))` clause literal.
    array_eq_lit: TermId,
    /// The `(= L R)` term inside it.
    eq_term: TermId,
    /// `L = (store X i v)` and `R = (store Y i w)`.
    left_store: TermId,
    right_store: TermId,
    /// The shared write index `i`.
    write_index: TermId,
    /// The written values `v` and `w`.
    left_value: TermId,
    right_value: TermId,
}

/// Sub-schema (I): exact same-index store equality forces the written values
/// equal — `not (= (store X i v) (store Y i w)) OR (= v w)`.
///
/// Only the OUTERMOST `store` of each side is peeled, and only when both sides
/// write at the SAME index term. `X` and `Y` are arbitrary array terms of the
/// common sort and are never inspected: the argument does not depend on them.
///
/// Note what makes this a legitimate SPECIALIZATION of sub-schema (B) rather
/// than a relaxation of it. (B) refuses a conclusion carrying no top-level
/// `select` because it will not GUESS the read index. Here nothing is guessed:
/// the witness index is `i`, forced by the premise's own two `store` terms
/// being written at one shared index. That is exactly why the shared-index
/// condition is not negotiable.
///
/// The two literals are matched positionally in both orders and each equality
/// in both orientations, so no clause ordering convention is assumed. Anything
/// else — a different index term on the two sides, a non-`store` side, a
/// mismatched array sort, a conclusion that is not exactly `(= v w)`, or any
/// literal count other than two — fails closed.
pub(super) fn same_index_store_value_equality_terms(
    terms: &TermStore,
    literals: &[TermId],
) -> Option<SameIndexStoreValueTerms> {
    if literals.len() != 2 {
        return None;
    }
    for premise_position in 0..2 {
        let array_eq_lit = literals[premise_position];
        let Some((left, right)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        if !matches!(terms.sort(left), Sort::Array(_)) || terms.sort(left) != terms.sort(right) {
            continue;
        }
        // `well_sorted_store_parts` re-establishes every sort relation of the
        // application, so the peeled value really is element-sorted.
        let (Some((_, left_index, left_value)), Some((_, right_index, right_value))) = (
            well_sorted_store_parts(terms, left),
            well_sorted_store_parts(terms, right),
        ) else {
            continue;
        };
        if left_index != right_index {
            continue;
        }
        let conclusion = literals[1 - premise_position];
        if !matches_equality_pair(terms, conclusion, left_value, right_value) {
            continue;
        }
        let TermData::Not(eq_term) = terms.get(array_eq_lit) else {
            continue;
        };
        return Some(SameIndexStoreValueTerms {
            conclusion,
            array_eq_lit,
            eq_term: *eq_term,
            left_store: left,
            right_store: right,
            write_index: left_index,
            left_value,
            right_value,
        });
    }
    None
}
