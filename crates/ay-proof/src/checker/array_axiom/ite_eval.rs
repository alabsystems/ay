// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sub-schema (K) of `ArrayRowChain`: the ITE-FOLDED evaluation of a `store`
//! chain, under an array equality.
//!
//! # The shape, and where it comes from
//!
//! `ay_core::TermStore::expand_select_store` rewrites `select(store(a, i, v), j)`
//! to `ite((= i j), v, select(a, j))` at preprocessing time and recurses into
//! the else branch, so a read of a whole `store` chain at a symbolic index
//! becomes a nested `ite` terminating either at a const-array default or at a
//! read of the chain's base. The CHC engine then states the connection between
//! an array variable and its defining chain as
//!
//! ```text
//! (cl (or (not (= E C)) (= (select E j) V)))
//! ```
//!
//! where `C` is the chain and `V` is that folded evaluation.
//!
//! Sub-schema (B) [`super::matches_row_chain_under_array_eq`] walks exactly the
//! same chain, and even terminates on a const-array base, but it can only SKIP a
//! `store` entry when the CLAUSE carries a positive `(= j i)` guard literal.
//! These clauses carry the case split INSIDE the `ite` instead, so (B)'s
//! `eval_chain_at` stops on the first entry and the schema declines. (K) is (B)
//! with the case split read out of the TERM instead of out of the clause —
//! which is why it consumes no guard literal at all.
//!
//! # The folds this has to see through
//!
//! `mk_ite` does not always leave an `Ite` node behind: when the element sort is
//! `Bool` it rewrites the node into propositional structure.
//! [`decode_ite_fold`] decodes the two such rewrites the measured population
//! needs, each a propositional IDENTITY with `ite(c, then, else)`:
//!
//! ```text
//! (ite c true false) = c          (ite c false true) = (not c)
//! ```
//!
//! `mk_ite`'s remaining Bool rewrites (`(or c x)`, `(and c x)`, …) are
//! deliberately NOT decoded: they need a Bool-element chain of length ≥ 2, which
//! the corpus does not contain, and each would add an argument-order search to a
//! walk whose whole value is that it is one deterministic pass. A leaf in that
//! shape DECLINES and keeps its byte-identical `trust` step.
//!
//! The two Boolean constants a fold erases are carried as
//! [`FoldedValue::BoolConst`] rather than as a `TermId`: the strict checker
//! holds an IMMUTABLE `TermStore` and cannot intern `true`/`false` to compare.
//!
//! # Soundness
//!
//! Assume the clause false. The negative literal being false gives `E = C`, so
//! by congruence `select(E, j) = select(C, j)`. [`ite_eval_denotes`] establishes
//! `V = select(C, j)` by induction on the chain, using only ground validities of
//! the theory of arrays and the two identities above:
//!
//! * an entry whose index IS `j` gives `v` by read-over-write-positive;
//! * any other entry contributes `ite((= i j), v, rest)`, which IS
//!   `select(store(_, i, v), j)` UNCONDITIONALLY — the McCarthy read-over-write
//!   identity stated without a case split, so no disequality is assumed and no
//!   clause literal is consumed to discharge one;
//! * the chain's base contributes `fill` when it is `const-array(fill)`, and the
//!   exact term `(select base j)` otherwise.
//!
//! So `V = select(C, j) = select(E, j)`, contradicting the assumed-false
//! conclusion. That the walk NEVER assumes a disequality is what distinguishes
//! (K) from (A)/(B), and it is why (K) needs no guard literal — not a
//! relaxation of (B)'s side condition but the absence of any.
//!
//! # What this schema does NOT accept
//!
//! The mirror clause `(cl (or (= E C) (not (= (select E j) V))))` is NOT a
//! tautology and is refused: it says two arrays that agree at `j` are equal,
//! which holds only because `j` is a Skolem extensionality WITNESS minted for
//! that exact pair. That is authority
//! (`super::validate_array_extensionality`'s `ExtDiffRegistry`), not shape, and
//! `the_extensionality_direction_is_refutable_and_declined` pins both the
//! decline and a falsifying assignment.

use super::*;

/// What the folded evaluation denotes at one point of the walk: an exact term of
/// the clause, or one of the two Boolean constants a `mk_ite` fold erased.
///
/// The strict checker's `TermStore` is immutable, so `true`/`false` cannot be
/// interned for comparison; a `BoolConst` is compared against a candidate term
/// by decoding that term instead.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FoldedValue {
    Node(TermId),
    BoolConst(bool),
}

impl FoldedValue {
    /// Whether this denotation IS the exact term `term`.
    fn denotes(self, terms: &TermStore, term: TermId) -> bool {
        match self {
            Self::Node(id) => id == term,
            Self::BoolConst(value) => {
                matches!(terms.get(term), TermData::Const(ay_core::Constant::Bool(b)) if *b == value)
            }
        }
    }
}

/// Decode `folded` as `ite((= entry_index index), then, else)` under the folds
/// `mk_ite` performs, returning the two branches.
///
/// DETERMINISTIC: at most one reading is returned for any term and no
/// alternative is retried on failure. The three arms are mutually exclusive by
/// term head (`Ite`, `=`, `not`), so there is nothing to backtrack over — which
/// is what keeps [`ite_eval_denotes`] one linear pass instead of a search whose
/// worst case is exponential in the chain length on an adversarial bundle.
fn decode_ite_fold(
    terms: &TermStore,
    folded: TermId,
    entry_index: TermId,
    index: TermId,
) -> Option<(FoldedValue, FoldedValue)> {
    if let TermData::Ite(cond, then_branch, else_branch) = terms.get(folded) {
        return matches_equality_pair(terms, *cond, entry_index, index).then_some((
            FoldedValue::Node(*then_branch),
            FoldedValue::Node(*else_branch),
        ));
    }
    // Both remaining forms are Bool-sorted rewrites `mk_ite` performs only when
    // the branches are Bool constants, so the element sort must be Bool here.
    if !matches!(terms.sort(folded), Sort::Bool) {
        return None;
    }
    // `(ite c true false) = c`
    if matches_equality_pair(terms, folded, entry_index, index) {
        return Some((FoldedValue::BoolConst(true), FoldedValue::BoolConst(false)));
    }
    // `(ite c false true) = (not c)`
    if let TermData::Not(inner) = terms.get(folded) {
        if matches_equality_pair(terms, *inner, entry_index, index) {
            return Some((FoldedValue::BoolConst(false), FoldedValue::BoolConst(true)));
        }
    }
    None
}

/// Whether `value` is the folded symbolic evaluation of `chain` at `index`.
///
/// ONE pass over the chain, `O(1)` per entry. See the module soundness note for
/// what each case contributes.
fn ite_eval_denotes(terms: &TermStore, chain: &StoreChain, index: TermId, value: TermId) -> bool {
    let mut current = FoldedValue::Node(value);
    for &(entry_index, entry_value) in &chain.entries {
        if entry_index == index {
            return current.denotes(terms, entry_value);
        }
        let FoldedValue::Node(folded) = current else {
            // A Boolean constant cannot be an `ite` over a further entry: the
            // walk ran out of structure before the chain ran out of stores.
            return false;
        };
        let Some((then_branch, else_branch)) = decode_ite_fold(terms, folded, entry_index, index)
        else {
            return false;
        };
        if !then_branch.denotes(terms, entry_value) {
            return false;
        }
        current = else_branch;
    }
    if let Some(fill) = terms.get_const_array(chain.base) {
        let Sort::Array(base_sort) = terms.sort(chain.base) else {
            return false;
        };
        return terms.sort(fill) == &base_sort.element_sort && current.denotes(terms, fill);
    }
    let FoldedValue::Node(folded) = current else {
        return false;
    };
    well_sorted_select_parts(terms, folded) == Some((chain.base, index))
}

/// See [`super::validate_array_row_chain`] for the schema and its soundness
/// argument; sub-schema (K) is stated there.
pub(super) fn matches_ite_folded_chain_eval_under_array_eq(
    terms: &TermStore,
    literals: &[TermId],
) -> bool {
    let [first, second] = literals else {
        return false;
    };
    for (premise_lit, conclusion_lit) in [(*first, *second), (*second, *first)] {
        let Some((left, right)) = negated_equality_sides(terms, premise_lit) else {
            continue;
        };
        let Sort::Array(array_sort) = terms.sort(left) else {
            continue;
        };
        if terms.sort(right) != terms.sort(left) {
            continue;
        }
        let Some((lhs, rhs)) = equality_sides(terms, conclusion_lit) else {
            continue;
        };
        if terms.sort(lhs) != terms.sort(rhs) || terms.sort(lhs) != &array_sort.element_sort {
            continue;
        }
        for (root, chain_term) in [(left, right), (right, left)] {
            let Some(chain) = parse_store_chain(terms, chain_term) else {
                continue;
            };
            // A depth-0 "chain" would make the conclusion plain congruence,
            // which is sub-schema (D)'s and the EUF lane's, not a ROW step.
            if chain.entries.is_empty() {
                continue;
            }
            for (select_side, value_side) in [(lhs, rhs), (rhs, lhs)] {
                let Some((array, read_index)) = well_sorted_select_parts(terms, select_side) else {
                    continue;
                };
                if array != root || terms.sort(read_index) != &array_sort.index_sort {
                    continue;
                }
                if ite_eval_denotes(terms, &chain, read_index, value_side) {
                    return true;
                }
            }
        }
    }
    false
}

/// Whether `clause` is exactly `ArrayRowChain` sub-schema (K).
///
/// This is the admission test the `ay-dpll` intrinsic-tautology battery uses to
/// relabel a premiseless `trust` leaf: the producer names no rule the checker
/// does not immediately re-run, because
/// [`super::validate_array_row_chain`] re-decides this very predicate as one of
/// its sub-schemas. A clause it declines keeps its byte-identical `trust` step.
#[must_use]
pub fn recognize_array_row_chain_ite_eval(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty()
        || clause
            .iter()
            .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    let literals = flatten_clause_literals(terms, clause);
    if literals
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    matches_ite_folded_chain_eval_under_array_eq(terms, &literals)
}

#[cfg(test)]
#[path = "ite_eval_fixture.rs"]
mod ite_eval_fixture;

#[cfg(test)]
#[path = "ite_eval_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "ite_eval_negative_tests.rs"]
mod negative_tests;

#[cfg(test)]
#[path = "ite_eval_guard_tests.rs"]
mod guard_tests;
