// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Array axioms in the term store's canonical (folded) spelling.
//!
//! The array axiom sites build equality conclusions — `(= (select A x) v)`,
//! `(= v w)`, `(= (default A) v)` — and `TermStore::mk_eq` folds an equality
//! with a Boolean constant into the literal itself: `(= P true)` becomes the
//! atom `P` and `(= P false)` becomes `(not P)`. Over a `Bool` element sort such
//! an axiom therefore reaches the proof WITHOUT the equality literal the
//! `ArrayRowChain` schemas match. The recognizer answered `None`, the producer
//! recorded the axiom as `Generic`, and mandatory strict certification refused
//! a correct refutation (`step t0 uses unsupported theory lemma kind Generic in
//! strict mode`).
//!
//! Each matcher here reads the folded literal back as the equality it is — `P`
//! as `(= P true)`, `(not P)` as `(= P false)` — and then demands EXACTLY what
//! the corresponding equality schema demands of that equality:
//!
//! * folded read under an array equality — sub-schema (B). Sites
//!   `store_value_cong`, `store_base_cong`, `store_other_side_cong`,
//!   `array_cong_select`.
//! * folded chain evaluation — sub-schema (A). Sites `row2_clause` over a
//!   constant base, `ext_row_seed`, `witness_row2`.
//! * folded conditional ROW1 — `ArraySelectStore { index_eq: true }`. Sites
//!   `row1_clause`, `ext_row_seed`, `witness_row1`.
//! * folded same-index store value — sub-schema (I). Site `store_value_cong`
//!   over a store/store equality.
//!
//! Nothing else is relaxed: the constant side is re-derived by the same chain
//! walk (`eval_chain_at`), every skipped `store` still needs its clause guard
//! or two distinct interpreted indices, and the literal's polarity must agree
//! with the constant it denotes.
//!
//! The folded `ArrayDefaultConst` spelling (`(or (not (= A F)) (default A))`,
//! from `array_default_congruence`) is deliberately NOT accepted here. No
//! refutation needs it alone: the default reasoning that follows it is the
//! store peel `default(store(B, i, v)) = default(B)`, which stays `Generic` (a
//! finite carrier refuses it by design, and no unit schema exists for an
//! infinite one). Certifying only that step would replace the export's
//! undeclared-symbol refusal (`does not declare ... (default)`) with an
//! `InvalidArrayStep`, and turn an explicit `--proof FILE` on a `default`-using
//! Bool query from `unknown` into a failed required publication.

use super::*;

/// A literal that denotes `(= atom value)` over `Bool`: the bare atom for
/// `value == true`, its single negation for `value == false`. `atom` must be a
/// Bool-sorted non-equality, non-negation term; equalities already have their
/// own schemas and a double negation is not the canonical folded form.
pub(super) fn bool_read_literal(terms: &TermStore, literal: TermId) -> Option<(TermId, bool)> {
    let (atom, value) = match terms.get(literal) {
        TermData::Not(inner) => (*inner, false),
        _ => (literal, true),
    };
    if !matches!(terms.sort(atom), Sort::Bool)
        || matches!(terms.get(atom), TermData::Not(_))
        || equality_sides(terms, atom).is_some()
    {
        return None;
    }
    Some((atom, value))
}

/// Sub-schema (M) of [`validate_array_row_chain`]: the folded `ArrayRowChain`
/// spellings, grouped so [`matches_row_chain`] names this module once. Shared
/// by the validator and the recognizer, so the producer's classification and
/// the strict checker cannot drift.
pub(super) fn matches_folded_row_subschema(
    terms: &TermStore,
    literals: &[TermId],
    eqs: &PositiveEqPairs,
) -> bool {
    matches_bool_read_under_array_eq(terms, literals, eqs)
        || matches_folded_row_chain_eval(terms, literals, eqs)
        || matches_folded_row1(terms, literals)
        || folded_same_index_store_value(terms, literals).is_some()
}

/// Folded sub-schema (B): a Bool-element read under an array equality,
/// written as the folded literal.
///
/// The clause carries a negative `(not (= L R))` over `Array(I, Bool)`, a
/// literal `P` or `(not P)` whose atom is a well-sorted `(select X x)` of that
/// array sort, and any number of positive `(= x i)` guards. It is accepted when,
/// for one orientation `(S, T)` of the premise, `P` is `eval(S, x)` or the root
/// read `(select S x)`, and `eval(T, x)` is the Boolean CONSTANT the literal's
/// polarity names (`true` for `P`, `false` for `(not P)`).
///
/// SOUNDNESS. Assume the clause false: `L = R`, every guard `eval` consumed is
/// false (`x != i`), and `P` has the value opposite to the literal's polarity.
/// Read-over-write gives `select(S, x) = P` and `select(T, x) = b` with `b` the
/// polarity, and `L = R` gives `select(L, x) = select(R, x)` by congruence, so
/// `P = b` — contradicting the assumed value of `P`. This is sub-schema (B)
/// with its conclusion `(= P b)` spelled the way the term store folds it; the
/// constant side always performs a genuine reduction (a taken `store` entry or
/// a constant-array fill), so plain congruence never passes through here.
fn matches_bool_read_under_array_eq(
    terms: &TermStore,
    literals: &[TermId],
    eqs: &PositiveEqPairs,
) -> bool {
    let premises: Vec<(TermId, TermId)> = literals
        .iter()
        .filter_map(|&lit| negated_equality_sides(terms, lit))
        .filter(|&(l, r)| matches!(terms.sort(l), Sort::Array(_)) && terms.sort(l) == terms.sort(r))
        .collect();
    if premises.is_empty() {
        return false;
    }
    for &literal in literals {
        let Some((atom, value)) = bool_read_literal(terms, literal) else {
            continue;
        };
        let Some((read_array, read_index)) = well_sorted_select_parts(terms, atom) else {
            continue;
        };
        for &(left, right) in &premises {
            if terms.sort(read_array) != terms.sort(left) {
                continue;
            }
            for (read_side, constant_side) in [(left, right), (right, left)] {
                let read_denotes = is_select_of(terms, atom, read_side, read_index)
                    || eval_chain_at(terms, read_side, read_index, eqs)
                        .is_some_and(|eval| eval.denotes(terms, atom));
                if read_denotes
                    && evaluates_to_bool_constant(terms, constant_side, read_index, eqs, value)
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Folded sub-schema (A): a literal `P` / `(not P)` whose atom is a
/// well-sorted `(select C x)` over a NON-EMPTY store chain `C`, where
/// `eval(C, x)` — under exactly (A)'s guards — is the Boolean constant the
/// literal's polarity names. `row2_clause` builds
/// `(or (= i k) (= (select (store K i v) k) (select K k)))`; with
/// `K = (const true)` the base read folds to `true` and the equality to the
/// atom.
///
/// SOUNDNESS. Assume the clause false. Every guard `eval` consumed is false, so
/// each skipped `store` is transparent at `x` and read-over-write (plus the
/// const-array read when the walk exhausts at one) gives
/// `select(C, x) = eval(C, x) = b`, while the false literal says
/// `select(C, x)` is `not b`. As in (A), a depth-0 chain is refused: the step
/// must perform a genuine read-over-write reduction.
fn matches_folded_row_chain_eval(
    terms: &TermStore,
    literals: &[TermId],
    eqs: &PositiveEqPairs,
) -> bool {
    literals.iter().any(|&literal| {
        let Some((atom, value)) = bool_read_literal(terms, literal) else {
            return false;
        };
        let Some((array, read_index)) = well_sorted_select_parts(terms, atom) else {
            return false;
        };
        parse_store_chain(terms, array).is_some_and(|chain| !chain.entries.is_empty())
            && evaluates_to_bool_constant(terms, array, read_index, eqs, value)
    })
}

/// Folded conditional ROW1: exactly two literals, `(not (= i k))` (either
/// orientation) and `P` / `(not P)`, where `P` is the well-sorted
/// `(select (store A i b) k)` and `b` is the Boolean constant the literal's
/// polarity names. `row1_clause` builds
/// `(or (not (= i k)) (= (select (store A i v) k) v))`; with `v` a Boolean
/// constant the equality folds to the atom or its negation.
///
/// Labelled `ArrayRowChain`, not `ArraySelectStore { index_eq: true }`: that
/// kind's printer refuses (`InvalidArrayStep`) a shape it cannot spell, which
/// would decline the whole document, whereas an unlowered `ArrayRowChain`
/// keeps an honest `hole` over its own clause.
///
/// SOUNDNESS. Assume the clause false: `i = k`, so
/// `select(store(A, i, b), k) = select(store(A, i, b), i) = b` by
/// read-over-write-positive, while the false literal says `not b`.
fn matches_folded_row1(terms: &TermStore, literals: &[TermId]) -> bool {
    let [first, second] = literals else {
        return false;
    };
    [(*first, *second), (*second, *first)]
        .into_iter()
        .any(|(guard, conclusion)| {
            let Some((atom, value)) = bool_read_literal(terms, conclusion) else {
                return false;
            };
            let Some((_, store_index, store_value, select_index)) = select_store_parts(terms, atom)
            else {
                return false;
            };
            terms.is_bool_const(store_value) == Some(value)
                && matches_not_equality_pair(terms, guard, store_index, select_index)
        })
}

/// The primitive terms of a folded sub-schema (I) clause.
pub(super) struct FoldedSameIndexStoreValue {
    /// The folded `P` / `(not P)` conclusion literal.
    conclusion: TermId,
    /// The `(not (= L R))` clause literal and the `(= L R)` term inside it.
    array_eq_lit: TermId,
    eq_term: TermId,
    /// `L = (store X i v)` and `R = (store Y i w)`.
    left_store: TermId,
    right_store: TermId,
    /// The shared write index `i`.
    write_index: TermId,
    /// The written values `v` and `w`: one is the atom, the other the constant.
    left_value: TermId,
    right_value: TermId,
}

/// Folded sub-schema (I): exactly two literals,
/// `(not (= (store X i v) (store Y i w)))` and `P` / `(not P)`, where one of
/// `v`, `w` IS the atom `P` and the other is the Boolean constant the literal's
/// polarity names. `store_value_cong` builds
/// `(or (not (= (store X i v) T)) (= v (select T i)))`; with
/// `T = (store Y i true)` the read folds to `true` and the equality to `v`.
///
/// Only the outermost `store` of each side is peeled and both must write at
/// the SAME index term, exactly as in (I); `X` and `Y` are never inspected.
///
/// SOUNDNESS. Assume the clause false: the two stores are equal, so reading
/// both at the shared index `i` gives `v = w` by read-over-write-positive
/// twice — the (I) argument — while the false literal gives the atom (one of
/// `v`, `w`) the value opposite to the constant (the other).
pub(super) fn folded_same_index_store_value(
    terms: &TermStore,
    literals: &[TermId],
) -> Option<FoldedSameIndexStoreValue> {
    let [first, second] = literals else {
        return None;
    };
    for (array_eq_lit, conclusion) in [(*first, *second), (*second, *first)] {
        let Some((left, right)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        if !matches!(terms.sort(left), Sort::Array(_)) || terms.sort(left) != terms.sort(right) {
            continue;
        }
        let (Some((_, left_index, left_value)), Some((_, right_index, right_value))) = (
            well_sorted_store_parts(terms, left),
            well_sorted_store_parts(terms, right),
        ) else {
            continue;
        };
        if left_index != right_index {
            continue;
        }
        let Some((atom, value)) = bool_read_literal(terms, conclusion) else {
            continue;
        };
        let names = |atom_side: TermId, constant_side: TermId| {
            atom_side == atom && terms.is_bool_const(constant_side) == Some(value)
        };
        if !names(left_value, right_value) && !names(right_value, left_value) {
            continue;
        }
        let TermData::Not(eq_term) = terms.get(array_eq_lit) else {
            continue;
        };
        return Some(FoldedSameIndexStoreValue {
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

/// Whether `eval(array, index)` is the Boolean constant `value`.
fn evaluates_to_bool_constant(
    terms: &TermStore,
    array: TermId,
    index: TermId,
    eqs: &PositiveEqPairs,
    value: bool,
) -> bool {
    matches!(
        eval_chain_at(terms, array, index, eqs),
        Some(ChainValue::Value(result)) if terms.is_bool_const(result) == Some(value)
    )
}

/// Printer terms for the folded `ArrayRowChain` shapes the `UnderArrayEq`
/// lowering can replay: folded (B) and folded (I). `left_target` /
/// `right_target` are the folded atom and the Boolean constant the other
/// side's walk ends on; the printer closes the derived `(= P b)` into the
/// clause's literal with `equiv_simplify`.
///
/// For folded (B) this is exactly the guard-carried subset of
/// [`matches_bool_read_under_array_eq`]: every skipped `store` needs its clause
/// guard (`row_chain_path_at`), and the clause may carry no literal the
/// derivation does not consume. Folded ROW1 and folded (A) have no shape here
/// and keep an honest `hole`.
pub(super) fn under_array_eq_printer_terms(
    terms: &TermStore,
    literals: &[TermId],
    packed_or: Option<TermId>,
) -> Option<ArrayRowChainPrinterTerms> {
    if let Some(shape) = bool_read_printer_terms(terms, literals, packed_or) {
        return Some(shape);
    }
    let same_index = folded_same_index_store_value(terms, literals)?;
    let value_end = |store: TermId, value: TermId| RowChainPath {
        root: store,
        skips: Vec::new(),
        end: RowChainEnd::Value {
            outer: store,
            value,
        },
    };
    Some(ArrayRowChainPrinterTerms::UnderArrayEq {
        conclusion: same_index.conclusion,
        array_eq_lit: same_index.array_eq_lit,
        eq_term: same_index.eq_term,
        left_target: same_index.left_value,
        right_target: same_index.right_value,
        read_index: same_index.write_index,
        left: value_end(same_index.left_store, same_index.left_value),
        right: value_end(same_index.right_store, same_index.right_value),
        packed_or,
    })
}

/// The folded (B) half of [`under_array_eq_printer_terms`].
fn bool_read_printer_terms(
    terms: &TermStore,
    literals: &[TermId],
    packed_or: Option<TermId>,
) -> Option<ArrayRowChainPrinterTerms> {
    for &array_eq_lit in literals {
        let Some((left, right)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        let TermData::Not(eq_term) = terms.get(array_eq_lit) else {
            continue;
        };
        if !matches!(terms.sort(left), Sort::Array(_)) || terms.sort(left) != terms.sort(right) {
            continue;
        }
        for &conclusion in literals {
            let Some((atom, value)) = bool_read_literal(terms, conclusion) else {
                continue;
            };
            let Some((read_array, read_index)) = well_sorted_select_parts(terms, atom) else {
                continue;
            };
            if terms.sort(read_array) != terms.sort(left) {
                continue;
            }
            for (read_side, constant_side, read_is_left) in
                [(left, right, true), (right, left, false)]
            {
                let Some((read_path, _)) =
                    row_chain_path_to_target(terms, read_side, read_index, literals, atom)
                else {
                    continue;
                };
                let Some(constant_path) =
                    row_chain_path_at(terms, constant_side, read_index, literals)
                else {
                    continue;
                };
                let constant = match constant_path.end {
                    RowChainEnd::Value { value: end, .. }
                    | RowChainEnd::Const { value: end, .. } => end,
                    RowChainEnd::Base { .. } => continue,
                };
                if terms.is_bool_const(constant) != Some(value) {
                    continue;
                }
                let mut used: Vec<TermId> = read_path
                    .skips
                    .iter()
                    .chain(constant_path.skips.iter())
                    .map(|skip| skip.guard)
                    .collect();
                used.extend([conclusion, array_eq_lit]);
                if !consumes_every_literal(literals, &used) {
                    continue;
                }
                let (left_target, right_target, left_path, right_path) = if read_is_left {
                    (atom, constant, read_path, constant_path)
                } else {
                    (constant, atom, constant_path, read_path)
                };
                return Some(ArrayRowChainPrinterTerms::UnderArrayEq {
                    conclusion,
                    array_eq_lit,
                    eq_term: *eq_term,
                    left_target,
                    right_target,
                    read_index,
                    left: left_path,
                    right: right_path,
                    packed_or,
                });
            }
        }
    }
    None
}
