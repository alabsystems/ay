// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for the array `TheoryLemmaKind`s:
//! `ArraySelectStore`, `ArrayStorePermutation`, `ArrayRowChain`,
//! `ArrayDefaultConst`, `ArrayExtensionality`, `ArrayFiniteExtensionality`,
//! and `ArrayFiniteSelectExpansion`.
//!
//! Context (#8820): the previous checker accepted any non-empty clause here,
//! so an attacker could forge an "array axiom" lemma containing arbitrary
//! Boolean literals and derive UNSAT. This module tightens the check to the
//! canonical axiom schemas from SMT-LIB McCarthy array theory:
//!
//! - `ArraySelectStore { index_eq: true }`  — read-over-write positive:
//!   the clause must mention `(select (store a i v) j)` (where `i = j` is
//!   justified by context) with `v` or a related witness on the opposite
//!   side of an equality.
//! - `ArraySelectStore { index_eq: false }` — read-over-write negative: the
//!   clause must mention both a `select` over a `store` and a disequality
//!   literal between the store and read indices.
//! - `ArrayStorePermutation` — n-ary store-commutativity: two `store` chains
//!   over one base array that write the same `(index, value)` multiset, with
//!   the pairwise index disjointness carried as clause literals (see
//!   [`validate_array_store_permutation`]).
//! - `ArrayRowChain` — read-over-write evaluated through a `store` CHAIN,
//!   optionally under an array-equality premise (see
//!   [`validate_array_row_chain`]).
//! - `ArrayExtensionality` — a one-or-more-level Skolemized extensionality
//!   chain `(= a b) ∨ ¬(= a[k0]...[kn] b[k0]...[kn])`, or its exact
//!   one-level const/store/array-ITE folded-read form. These are NOT
//!   tautologies: they hold only because every witness is FRESH and minted for
//!   its exact array pair. They are therefore accepted only against an
//!   [`ExtDiffRegistry`] built from the proof's own `array_ext_diff_intro`
//!   steps and the problem's assertion set (see
//!   [`validate_array_extensionality`]); with no registry it stays fail-closed
//!   exactly as before.
//! - `ArrayFiniteExtensionality` / `ArrayFiniteSelectExpansion` — exact
//!   complete-carrier schemas validated in the sibling `array_finite` module.
//!   Unlike Skolemized extensionality, these are tautologies by finite-domain
//!   exhaustion and need no witness-provenance registry.
//!
//! Full semantic validation (#8073) is still future work for the remaining
//! kinds. Strict mode accepts the exact read-over-write schemas and rejects
//! anything it cannot re-derive from the proof plus the problem.

use std::sync::atomic::{AtomicUsize, Ordering};

// #8529: deterministic hash containers in all builds.
use ay_core::kani_compat::{det_hash_set_new, DetHashMap, DetHashSet};
use ay_core::{
    AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};

use super::ProofCheckError;

mod chain_extensions;
pub(crate) mod ite_eval;

/// Maximum number of `store` nodes the folded-default checker will traverse.
/// This bounds work on untrusted proof bundles independently of proof size.
/// Only reached on a provably infinite index carrier -- see
/// [`sort_provably_infinite`].
const MAX_ARRAY_DEFAULT_STORE_DEPTH: usize = 1_024;

/// Validate a `ArraySelectStore { index_eq }` lemma in strict mode.
pub(crate) fn validate_array_select_store(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    index_eq: bool,
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array axiom clause must be non-empty".to_string(),
        });
    }
    reject_non_bool_literals(terms, step_id, clause, "array axiom")?;

    let literals = flatten_clause_literals(terms, clause);
    reject_non_bool_literals(terms, step_id, &literals, "array axiom")?;
    let valid = if index_eq {
        matches_row1_unit(terms, &literals) || matches_row1_conditional(terms, &literals)
    } else {
        matches_row2_conditional(terms, &literals)
    };
    if !valid {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "array axiom (index_eq={index_eq}) does not match an exact \
                 read-over-write schema"
            ),
        });
    }

    Ok(())
}

/// Recognize whether `clause` is an exact read-over-write schema, returning the
/// matching `ArraySelectStore { index_eq }` flag — `Some(true)` for the ROW1
/// (index-equal) schema, `Some(false)` for the ROW2 (index-disequality) schema,
/// or `None` if it is not a strict-checkable read-over-write lemma.
///
/// This is the EXACT inverse of `validate_array_select_store`: the proof
/// classifier (`ay-dpll` `theory_inference`) calls it so the kind it assigns is
/// precisely the one strict mode will accept — no classifier/checker drift.
/// Extensionality is intentionally NOT recognized here: it is not a tautology,
/// so shape alone can never license it. Its recognizer is the separate
/// [`recognize_array_extensionality`] and
/// [`recognize_array_extensionality_chain`], which the PROOF EMITTER pairs with
/// `array_ext_diff_intro` steps; the live conflict classifier (which has no
/// proof to attach introductions to) must leave such clauses `Generic`. Schema
/// logic lives ONLY in this module.
#[must_use]
pub fn recognize_array_select_store(terms: &TermStore, clause: &[TermId]) -> Option<bool> {
    if clause.is_empty() {
        return None;
    }
    if clause
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return None;
    }
    let literals = flatten_clause_literals(terms, clause);
    if literals
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return None;
    }
    if matches_row1_unit(terms, &literals) || matches_row1_conditional(terms, &literals) {
        Some(true)
    } else if matches_row2_conditional(terms, &literals) {
        Some(false)
    } else {
        None
    }
}

/// Exact, top-level ROW shapes the Alethe printer can lower to Carcara.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ArraySelectStorePrinterTerms {
    /// `select(store(a, i, v), j) = v`, either as a unit with `i == j` or
    /// guarded by the exact literal `not (= i j)`.
    Row1 {
        row: TermId,
        select: TermId,
        base_array: TermId,
        store_index: TermId,
        value: TermId,
        read_index: TermId,
        guard: Option<TermId>,
        packed_or: Option<TermId>,
    },
    /// `select(store(a, i, v), j) = select(a, j)`, guarded by `= i j`.
    Row2 {
        row: TermId,
        select_store: TermId,
        select_base: TermId,
        base_array: TermId,
        store_index: TermId,
        value: TermId,
        read_index: TermId,
        guard: TermId,
        packed_or: Option<TermId>,
    },
}

/// Return the exact primitive terms the Alethe printer may lower to Carcara's
/// checked array rules.
///
/// Unlike the internal schema validator, this deliberately does not flatten a
/// unit `or`: changing a unit-or proof term into a multi-literal external
/// clause would break downstream steps that consume the or-term itself. Both
/// equality orientations are returned through their component terms; the
/// printer must explicitly derive the requested orientation and reject any
/// surface override outside these exact shapes.
pub(crate) fn array_select_store_printer_terms(
    terms: &TermStore,
    clause: &[TermId],
    index_eq: bool,
) -> Option<ArraySelectStorePrinterTerms> {
    let (clause, packed_or): (&[TermId], Option<TermId>) = match clause {
        [packed] => match terms.get(*packed) {
            TermData::App(Symbol::Named(symbol), args) if symbol == "or" && args.len() == 2 => {
                (args.as_slice(), Some(*packed))
            }
            _ => (clause, None),
        },
        _ => (clause, None),
    };
    if clause
        .iter()
        .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return None;
    }
    if index_eq {
        let candidates = match clause {
            [row] => [Some((*row, None)), None],
            [first, second] => [Some((*first, Some(*second))), Some((*second, Some(*first)))],
            _ => return None,
        };
        for (row, guard) in candidates.into_iter().flatten() {
            let Some((lhs, rhs)) = equality_sides(terms, row) else {
                continue;
            };
            for (select, value) in [(lhs, rhs), (rhs, lhs)] {
                let Some((base_array, store_index, store_value, read_index)) =
                    select_store_parts(terms, select)
                else {
                    continue;
                };
                if store_value != value {
                    continue;
                }
                match guard {
                    None if store_index == read_index => {
                        return Some(ArraySelectStorePrinterTerms::Row1 {
                            row,
                            select,
                            base_array,
                            store_index,
                            value,
                            read_index,
                            guard: None,
                            packed_or,
                        });
                    }
                    Some(guard)
                        if matches_not_equality_pair(terms, guard, store_index, read_index) =>
                    {
                        return Some(ArraySelectStorePrinterTerms::Row1 {
                            row,
                            select,
                            base_array,
                            store_index,
                            value,
                            read_index,
                            guard: Some(guard),
                            packed_or,
                        });
                    }
                    _ => {}
                }
            }
        }
        return None;
    }

    let [first, second] = clause else {
        return None;
    };
    for (row, guard) in [(*first, *second), (*second, *first)] {
        let Some((lhs, rhs)) = equality_sides(terms, row) else {
            continue;
        };
        for (select_store, select_base) in [(lhs, rhs), (rhs, lhs)] {
            let Some((base_array, store_index, value, read_index)) =
                select_store_parts(terms, select_store)
            else {
                continue;
            };
            if is_select_of(terms, select_base, base_array, read_index)
                && matches_equality_pair(terms, guard, store_index, read_index)
            {
                return Some(ArraySelectStorePrinterTerms::Row2 {
                    row,
                    select_store,
                    select_base,
                    base_array,
                    store_index,
                    value,
                    read_index,
                    guard,
                    packed_or,
                });
            }
        }
    }
    None
}

/// The exact primitive terms of an `ArrayStorePermutation` clause that the
/// Alethe printer may lower to Carcara's checked array rules.
///
/// Every field is read back off the clause by
/// [`array_store_permutation_printer_terms`]; nothing is taken on the
/// producer's word. `left`/`right` list `(index, value)` pairs OUTERMOST-FIRST,
/// matching [`StoreChain::entries`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArrayStorePermutationPrinterTerms {
    /// The positive `(= L R)` literal, and its position in the clause.
    pub row: TermId,
    /// Index of `row` in the clause as the printer received it.
    pub row_position: usize,
    /// The `L` and `R` store-chain terms, in the orientation `row` spells.
    pub left_array: TermId,
    pub right_array: TermId,
    /// The common innermost non-`store` base array.
    pub base: TermId,
    /// `L`'s written pairs, outermost-first.
    pub left: Vec<(TermId, TermId)>,
    /// `R`'s written pairs, outermost-first.
    pub right: Vec<(TermId, TermId)>,
    /// For every unordered pair of the chains' index terms, the clause literal
    /// that carries it, together with the exact orientation that literal
    /// spells: `(literal, position, lhs, rhs)`.
    pub index_equalities: Vec<(TermId, usize, TermId, TermId)>,
    /// The array sort's index sort, for the `choice` binder the checker's
    /// `arrays_ext` rule constructs.
    pub index_sort: Sort,
}

/// Largest store-chain length the Alethe lowering will derive.
///
/// The derivation is quadratic in the chain length (bubble-sort schedule ×
/// per-transposition block), and the clause must carry one index-equality
/// literal per unordered pair, so a longer chain is a printing pathology.
/// Beyond the cap the lemma stays an honest `hole`; AY's native strict checker
/// is unaffected.
pub(crate) const MAX_STORE_PERMUTATION_CHAIN: usize = 8;

/// Return the exact primitive terms of a strict-checkable
/// `ArrayStorePermutation` clause, or `None` when the clause is outside the
/// subset the printer can rebuild as checked Alethe.
///
/// This is DELIBERATELY narrower than [`validate_array_store_permutation`],
/// which tolerates extra literals and only asks that SOME positive literal
/// carry the permutation. The printer has to reproduce the whole clause, so it
/// additionally requires:
///
/// * the clause is flat — a single packed `or` is refused rather than
///   silently reshaped, exactly as [`array_select_store_printer_terms`] avoids
///   flattening a unit `or`;
/// * exactly ONE literal is a permutation equality (an ambiguous clause would
///   leave the printer choosing which claim to derive);
/// * the chain length is at most [`MAX_STORE_PERMUTATION_CHAIN`].
///
/// Everything else it reports is read straight back out of the clause: the
/// caller re-derives the permutation from `left`/`right` and discharges each
/// transposition against the `index_equalities` literal for that exact pair.
#[path = "array_axiom/store_permutation_printer.rs"]
mod store_permutation_printer;
pub(crate) use store_permutation_printer::array_store_permutation_printer_terms;

/// One `store` skipped while evaluating a chain at the read index.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RowChainSkip {
    /// The POSITIVE `(= x i)` clause literal that licenses the skip. Its
    /// printed orientation is whatever the clause carries; the printer checks
    /// it against both spellings and bridges with `not_symm` when needed.
    pub guard: TermId,
    /// `(store inner i v)` — the array term before the skip.
    pub outer: TermId,
    /// The array term after the skip (`inner`).
    pub inner: TermId,
    /// The skipped store's index `i`.
    pub store_index: TermId,
}

/// How a read-over-write chain walk terminates at the read index.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RowChainEnd {
    /// The walk reached `(store inner x v)` whose index IS the read index, so
    /// the chain evaluates to `v` by `arrays_idx`.
    Value { outer: TermId, value: TermId },
    /// The walk exhausted the chain: the value is `(select base x)`.
    Base { base: TermId },
    /// The walk exhausted at `(const-array value)`, so every read is `value`.
    /// The internal checker validates this SMT-LIB axiom directly; the pinned
    /// external Alethe checker currently has no corresponding primitive rule.
    Const { array: TermId, value: TermId },
}

/// The intermediate array terms of one chain walk, in outermost-first order.
///
/// This is exactly the trace [`eval_chain_at`] takes, recorded so the Alethe
/// printer can emit one `arrays_row` step per skipped `store`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RowChainPath {
    pub root: TermId,
    pub skips: Vec<RowChainSkip>,
    pub end: RowChainEnd,
}

/// Exact `ArrayRowChain` shapes the Alethe printer may lower to Carcara's
/// `arrays_idx` / `arrays_row` / `cong` / `trans` rules.
///
/// Mirrors the two sub-schemas of [`validate_array_row_chain`]. The extractor
/// additionally demands that the clause carry NO literal beyond the ones the
/// derivation consumes: the printer discharges exactly the guards it assumed
/// and cannot manufacture an unrelated extra literal in the final resolvent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ArrayRowChainPrinterTerms {
    /// Sub-schema (A): `(= (select C x) eval(C, x))`.
    Eval {
        conclusion: TermId,
        select: TermId,
        value_side: TermId,
        read_index: TermId,
        path: RowChainPath,
        packed_or: Option<TermId>,
    },
    /// Sub-schema (B): `(not (= L R))` plus `(= eval(L, x) eval(R, x))`.
    UnderArrayEq {
        conclusion: TermId,
        /// The `(not (= L R))` clause literal.
        array_eq_lit: TermId,
        /// The `(= L R)` term inside it.
        eq_term: TermId,
        /// The conclusion side `eval(L, x)` denotes.
        left_target: TermId,
        /// The conclusion side `eval(R, x)` denotes.
        right_target: TermId,
        read_index: TermId,
        left: RowChainPath,
        right: RowChainPath,
        packed_or: Option<TermId>,
    },
}

/// Primitive terms of the exact array-read congruence clause
/// `not (= L R) OR (= (select L i) (select R i))`.
///
/// This deliberately does not share the more permissive ROW-chain matcher:
/// neither side is evaluated, and every root/index is matched syntactically.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ArrayReadCongruenceTerms {
    conclusion: TermId,
    array_eq_lit: TermId,
    eq_term: TermId,
    left: TermId,
    right: TermId,
    left_read: TermId,
    right_read: TermId,
    read_index: TermId,
}

/// The literal `(= a b)` / `(= b a)` of `literals`, if the clause carries one.
fn find_positive_eq_literal(
    terms: &TermStore,
    literals: &[TermId],
    a: TermId,
    b: TermId,
) -> Option<TermId> {
    literals
        .iter()
        .copied()
        .find(|&lit| matches_equality_pair(terms, lit, a, b))
}

/// Record the chain walk [`eval_chain_at`] performs, keeping every
/// intermediate array term. Returns `None` in exactly the cases
/// `eval_chain_at` returns `None`.
fn row_chain_path_at(
    terms: &TermStore,
    term: TermId,
    index: TermId,
    literals: &[TermId],
) -> Option<RowChainPath> {
    // Re-run the full well-sortedness check of the chain before trusting any
    // of its nodes; `parse_store_chain` is the single source of that truth.
    parse_store_chain(terms, term)?;
    let Sort::Array(array_sort) = terms.sort(term) else {
        return None;
    };
    if terms.sort(index) != &array_sort.index_sort {
        return None;
    }
    let mut skips = Vec::new();
    let mut current = term;
    while let TermData::App(sym, args) = terms.get(current) {
        if !matches!(sym, Symbol::Named(name) if name == "store") || args.len() != 3 {
            break;
        }
        let (inner, entry_index, entry_value) = (args[0], args[1], args[2]);
        if entry_index == index {
            return Some(RowChainPath {
                root: term,
                skips,
                end: RowChainEnd::Value {
                    outer: current,
                    value: entry_value,
                },
            });
        }
        let guard = find_positive_eq_literal(terms, literals, index, entry_index)?;
        skips.push(RowChainSkip {
            guard,
            outer: current,
            inner,
            store_index: entry_index,
        });
        current = inner;
    }
    if let Some(value) = terms.get_const_array(current) {
        if terms.sort(value) != &array_sort.element_sort {
            return None;
        }
        return Some(RowChainPath {
            root: term,
            skips,
            end: RowChainEnd::Const {
                array: current,
                value,
            },
        });
    }
    Some(RowChainPath {
        root: term,
        skips,
        end: RowChainEnd::Base { base: current },
    })
}

/// Whether the walk's terminal value is denoted by `target`.
fn path_end_denotes(terms: &TermStore, path: &RowChainPath, index: TermId, target: TermId) -> bool {
    match path.end {
        RowChainEnd::Value { value, .. } => value == target,
        RowChainEnd::Base { base } => is_select_of(terms, target, base, index),
        RowChainEnd::Const { value, .. } => value == target,
    }
}

/// Build the proof path from `array` to `target` at `index`.
///
/// Usually `target` is the result of actually reducing a non-empty store
/// chain.  Under an array-equality premise, however, one side of the
/// congruence may intentionally remain the exact root read
/// `(select array index)`: the other side's ROW reduction plus congruence is
/// already sufficient.  The returned flag records whether this path performs
/// at least one genuine ROW step, so callers can reject the vacuous case where
/// both endpoints are merely their root reads.
fn row_chain_path_to_target(
    terms: &TermStore,
    array: TermId,
    index: TermId,
    literals: &[TermId],
    target: TermId,
) -> Option<(RowChainPath, bool)> {
    if let Some(path) = row_chain_path_at(terms, array, index, literals) {
        if path_end_denotes(terms, &path, index, target) {
            let reduced = !path.skips.is_empty()
                || matches!(
                    path.end,
                    RowChainEnd::Value { .. } | RowChainEnd::Const { .. }
                );
            return Some((path, reduced));
        }
    }

    let (target_array, target_index) = well_sorted_select_parts(terms, target)?;
    if target_array != array || target_index != index {
        return None;
    }
    Some((
        RowChainPath {
            root: array,
            skips: Vec::new(),
            end: RowChainEnd::Base { base: array },
        },
        false,
    ))
}

/// Whether `literals` is EXACTLY the set `used` (order and multiplicity are
/// irrelevant; every clause literal must be consumed by the derivation).
fn consumes_every_literal(literals: &[TermId], used: &[TermId]) -> bool {
    literals.iter().all(|lit| used.contains(lit))
}

/// Return the exact primitive terms the Alethe printer may lower to Carcara's
/// checked array rules for an `ArrayRowChain` lemma.
///
/// The search order mirrors [`matches_row_chain`] exactly, so any clause this
/// returns terms for is one [`validate_array_row_chain`] accepts. The converse
/// does NOT hold: this refuses clauses carrying literals the derivation would
/// not discharge, because the printer's closing `resolution` can only produce
/// the resolvent of what it actually assumed.
pub(crate) fn array_row_chain_printer_terms(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ArrayRowChainPrinterTerms> {
    let (literals, packed_or): (Vec<TermId>, Option<TermId>) = match clause {
        [packed] => match terms.get(*packed) {
            TermData::App(Symbol::Named(symbol), args) if symbol == "or" && args.len() >= 2 => {
                (args.clone(), Some(*packed))
            }
            _ => (clause.to_vec(), None),
        },
        _ => (clause.to_vec(), None),
    };

    // Sub-schema (A).
    for &lit in &literals {
        let Some((lhs, rhs)) = equality_sides(terms, lit) else {
            continue;
        };
        if terms.sort(lhs) != terms.sort(rhs) {
            continue;
        }
        for (select_side, value_side) in [(lhs, rhs), (rhs, lhs)] {
            let Some((array, read_index)) = well_sorted_select_parts(terms, select_side) else {
                continue;
            };
            let Some(chain) = parse_store_chain(terms, array) else {
                continue;
            };
            if chain.entries.is_empty() {
                continue;
            }
            let Some(path) = row_chain_path_at(terms, array, read_index, &literals) else {
                continue;
            };
            if !path_end_denotes(terms, &path, read_index, value_side) {
                continue;
            }
            let mut used: Vec<TermId> = path.skips.iter().map(|skip| skip.guard).collect();
            used.push(lit);
            if !consumes_every_literal(&literals, &used) {
                continue;
            }
            return Some(ArrayRowChainPrinterTerms::Eval {
                conclusion: lit,
                select: select_side,
                value_side,
                read_index,
                path,
                packed_or,
            });
        }
    }

    if let Some(shape) = chain_extensions::under_array_eq_printer_terms(terms, &literals, packed_or)
    {
        return Some(shape);
    }

    // Sub-schema (B).
    let premises: Vec<(TermId, TermId, TermId)> = literals
        .iter()
        .filter_map(|&lit| negated_equality_sides(terms, lit).map(|(l, r)| (lit, l, r)))
        .filter(|&(_, l, r)| {
            matches!(terms.sort(l), Sort::Array(_)) && terms.sort(l) == terms.sort(r)
        })
        .collect();
    for &lit in &literals {
        let Some((lhs, rhs)) = equality_sides(terms, lit) else {
            continue;
        };
        if terms.sort(lhs) != terms.sort(rhs) {
            continue;
        }
        let mut candidates: Vec<TermId> = Vec::new();
        for side in [lhs, rhs] {
            if let Some((_, read_index)) = well_sorted_select_parts(terms, side) {
                if !candidates.contains(&read_index) {
                    candidates.push(read_index);
                }
            }
        }
        for &(premise_lit, left, right) in &premises {
            let Sort::Array(array_sort) = terms.sort(left) else {
                continue;
            };
            if terms.sort(lhs) != &array_sort.element_sort {
                continue;
            }
            for &read_index in &candidates {
                if terms.sort(read_index) != &array_sort.index_sort {
                    continue;
                }
                let mut matched = None;
                for (left_target, right_target) in [(lhs, rhs), (rhs, lhs)] {
                    let (Some((left_path, left_reduced)), Some((right_path, right_reduced))) = (
                        row_chain_path_to_target(terms, left, read_index, &literals, left_target),
                        row_chain_path_to_target(terms, right, read_index, &literals, right_target),
                    ) else {
                        continue;
                    };
                    // Pure congruence belongs to the EUF lane.  This array
                    // schema must contribute at least one checked ROW step.
                    if left_reduced || right_reduced {
                        matched = Some((left_target, right_target, left_path, right_path));
                        break;
                    }
                }
                let Some((left_target, right_target, left_path, right_path)) = matched else {
                    continue;
                };
                let mut used: Vec<TermId> = left_path
                    .skips
                    .iter()
                    .chain(right_path.skips.iter())
                    .map(|skip| skip.guard)
                    .collect();
                used.push(lit);
                used.push(premise_lit);
                if !consumes_every_literal(&literals, &used) {
                    continue;
                }
                let eq_term = match terms.get(premise_lit) {
                    TermData::Not(inner) => *inner,
                    _ => continue,
                };
                return Some(ArrayRowChainPrinterTerms::UnderArrayEq {
                    conclusion: lit,
                    array_eq_lit: premise_lit,
                    eq_term,
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

/// Recognize the array theory lemma kind `clause` can be strict-validated as,
/// or `None` when no exact schema matches (the lemma must then stay `Generic`
/// / `:rule trust`).
///
/// This is the EXACT inverse of the `validate_*` entry points in this module,
/// so the proof classifier (`ay-dpll` `theory_inference`) assigns precisely the
/// kind strict mode will accept — no classifier/checker drift. Ordering keeps
/// the narrow depth-1 `ArraySelectStore` kinds first so existing rule emission
/// (and its Lean firewall) is unchanged; the n-ary schemas only ever claim
/// clauses that were previously `Generic`.
///
/// Skolemized extensionality is intentionally NOT recognized here — see
/// [`recognize_array_select_store`] for why it needs its own emitter-side path.
/// Complete finite-carrier extensionality is a tautology and is recognized
/// first through the independent `array_finite` validator.
#[must_use]
pub fn recognize_array_theory_lemma(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<TheoryLemmaKind> {
    if super::array_finite::recognize_array_finite_extensionality(terms, clause) {
        return Some(TheoryLemmaKind::ArrayFiniteExtensionality);
    }
    if super::array_finite::recognize_array_finite_select_expansion(terms, clause) {
        return Some(TheoryLemmaKind::ArrayFiniteSelectExpansion);
    }
    if let Some(index_eq) = recognize_array_select_store(terms, clause) {
        return Some(TheoryLemmaKind::ArraySelectStore { index_eq });
    }
    if clause.is_empty()
        || clause
            .iter()
            .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return None;
    }
    let literals = flatten_clause_literals(terms, clause);
    if literals
        .iter()
        .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return None;
    }
    if matches_array_default_const(terms, &literals) {
        return Some(TheoryLemmaKind::ArrayDefaultConst);
    }
    if matches_store_permutation(terms, &literals) {
        return Some(TheoryLemmaKind::ArrayStorePermutation);
    }
    if matches_row_chain(terms, &literals) {
        return Some(TheoryLemmaKind::ArrayRowChain);
    }
    None
}

/// Typed-context form of [`recognize_array_theory_lemma`].
///
/// The extra context lets the two finite-array schemas authenticate the exact
/// nullary constructor terms of an enum index carrier. All context-independent
/// schemas retain the same classifier and ordering as the compatibility API.
#[must_use]
pub fn recognize_array_theory_lemma_with_typed_context(
    terms: &TermStore,
    clause: &[TermId],
    datatype_declarations: &[(String, Vec<String>)],
    constructor_selectors: &[(String, Vec<String>)],
    datatype_member_signatures: &[super::DatatypeMemberSignature],
) -> Option<TheoryLemmaKind> {
    if super::array_finite::recognize_array_finite_extensionality_with_typed_context(
        terms,
        clause,
        datatype_declarations,
        constructor_selectors,
        datatype_member_signatures,
    ) {
        return Some(TheoryLemmaKind::ArrayFiniteExtensionality);
    }
    if super::array_finite::recognize_array_finite_select_expansion_with_typed_context(
        terms,
        clause,
        datatype_declarations,
        constructor_selectors,
        datatype_member_signatures,
    ) {
        return Some(TheoryLemmaKind::ArrayFiniteSelectExpansion);
    }
    recognize_array_theory_lemma(terms, clause)
}

/// Validate the exact array-default/const-array schemas.
///
/// The accepted clause has exactly two flattened literals: a negated equality
/// between an array `A` and a well-sorted finite `store` chain rooted at one
/// exact `const-array(v)`, and a positive equality between `default(A)` and
/// that same `v`. Every term and sort is re-derived from the clause; the
/// producer's theory label carries no authority. A second exact shape accepts
/// `not (= (store A i v) (store (const-array fill) i v))) OR
/// (= (default A) fill)`: same-index/same-value stores preserve their bases'
/// defaults, and the constant-array base has default `fill`.
pub(crate) fn validate_array_default_const(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty()
        || clause
            .iter()
            .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array-default-const clause must contain only Boolean literals".to_string(),
        });
    }
    let literals = flatten_clause_literals(terms, clause);
    reject_non_bool_literals(terms, step_id, &literals, "array-default-const")?;
    if matches_array_default_const(terms, &literals) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "array-default-const clause must be exactly `(not (= A store*(const-array(v)))) OR (= (default A) v)`, or the exact matched-store form `(not (= (store A i v) (store (const-array(fill)) i v))) OR (= (default A) fill)`"
            .to_string(),
    })
}

fn matches_array_default_const(terms: &TermStore, literals: &[TermId]) -> bool {
    if matches_default_const_under_equal_matched_stores(terms, literals) {
        return true;
    }
    if literals.len() != 2 {
        return false;
    }

    for premise_index in 0..2 {
        let conclusion_index = 1 - premise_index;
        let Some((premise_lhs, premise_rhs)) =
            negated_equality_sides(terms, literals[premise_index])
        else {
            continue;
        };
        let Some((conclusion_lhs, conclusion_rhs)) =
            equality_sides(terms, literals[conclusion_index])
        else {
            continue;
        };

        for (array, folded_array) in [(premise_lhs, premise_rhs), (premise_rhs, premise_lhs)] {
            let Some(fill) = const_array_default_fill(terms, folded_array) else {
                continue;
            };
            let Sort::Array(array_sort) = terms.sort(array) else {
                continue;
            };
            if terms.sort(folded_array) != terms.sort(array)
                || terms.sort(fill) != &array_sort.element_sort
            {
                continue;
            }

            for (default_term, value) in [
                (conclusion_lhs, conclusion_rhs),
                (conclusion_rhs, conclusion_lhs),
            ] {
                if value == fill
                    && terms.get_array_default(default_term) == Some(array)
                    && terms.sort(default_term) == &array_sort.element_sort
                    && terms.sort(value) == &array_sort.element_sort
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Re-derive `default(array)` for an EXACT constant-array term. No `store`
/// peeling — see the soundness note.
///
/// # Soundness
///
/// From the clause's premise `A = const-array(v)`, congruence gives
/// `default(A) = default(const-array(v))` and the constant-array axiom gives
/// `= v`. That holds on **every** carrier, under any axiomatization containing
/// the const axiom — including AY's own, which is too weak to derive the fold.
/// No cardinality reasoning is needed, which is why this form is safe.
///
/// # Why peeling a `store` was removed
///
/// This function used to walk up to `MAX_ARRAY_DEFAULT_STORE_DEPTH` stores to a
/// constant root and return that root's fill. That is the rule
/// `default(store(a,i,v)) = default(a)`, which is **carrier-sensitive** and
/// false on a finite index carrier — a store can change the element the default
/// is read from. One store over `Bool` already breaks it; measured against
/// Z3 5.0.0:
///
/// ```text
/// (= a (store ((as const (Array Bool Int)) 0) true 7))
/// (not (= (default a) 0))                                  => sat
/// ```
///
/// and with a chain that covers the carrier the const root's fill is provably
/// the wrong answer:
///
/// ```text
/// A = (store (store ((as const (Array Bool Int)) 0) false 7) true 7)
/// (= (default A) 0) => unsat        (= (default A) 7) => sat
/// ```
///
/// The matcher inspects no carrier, so it accepted both. Note this was NOT a
/// covering-chain-only defect: a single store over any finite carrier suffices.
/// Re-admitting peels requires a carrier-cardinality side condition the checker
/// cannot currently evaluate — `validate_array_default_const` is dispatched
/// without a datatype registry, so a finite enum is indistinguishable from a
/// genuine uninterpreted sort.
fn const_array_default_fill(terms: &TermStore, array: TermId) -> Option<TermId> {
    let Sort::Array(array_sort) = terms.sort(array) else {
        return None;
    };
    let expected = array_sort.as_ref().clone();
    let expected_array_sort = Sort::Array(Box::new(expected.clone()));

    // Peel stores ONLY when no finite chain can reach the whole carrier. On a
    // provably infinite index sort the fold is valid (oracle-confirmed); on any
    // other carrier -- including one we merely cannot classify -- refuse and
    // accept only an exact constant array.
    let may_peel = sort_provably_infinite(&expected.index_sort);

    let mut current = array;
    let mut seen: DetHashSet<TermId> = det_hash_set_new();

    for _ in 0..=MAX_ARRAY_DEFAULT_STORE_DEPTH {
        if !seen.insert(current) || terms.sort(current) != &expected_array_sort {
            return None;
        }
        if let Some(fill) = terms.get_const_array(current) {
            return (terms.sort(fill) == &expected.element_sort).then_some(fill);
        }
        if !may_peel {
            return None;
        }
        let TermData::App(Symbol::Named(symbol), args) = terms.get(current) else {
            return None;
        };
        if symbol != "store"
            || args.len() != 3
            || terms.sort(args[0]) != &expected_array_sort
            || terms.sort(args[1]) != &expected.index_sort
            || terms.sort(args[2]) != &expected.element_sort
        {
            return None;
        }
        current = args[0];
    }
    None
}

/// Whether `sort` is **provably** infinite from its structure alone.
///
/// Deliberately conservative and one-sided: `false` means "not proven infinite",
/// never "proven finite". Every caller must treat `false` as a refusal.
///
/// This is the side condition that makes peeling a `store` sound again. The rule
/// `default(store(a,i,v)) = default(a)` fails exactly when a store can change the
/// element the default is read from, which requires a carrier a finite chain can
/// reach. On a provably infinite index sort no finite chain can, and the oracle
/// agrees — Z3 5.0.0 refutes `(not (= (default A) 3))` for
/// `A = (store (store ((as const (Array Int Int)) 3) 0 5) 7 9)`.
///
/// `Uninterpreted` and `Datatype` MUST return `false`, and that is soundness
/// rather than caution: [`validate_array_default_const`] is dispatched without a
/// datatype registry, so a three-element enum arrives indistinguishable from a
/// genuine uninterpreted sort. Z3 refutes the fold for such an enum
/// (`(declare-datatypes ((C3 0)) (((r)(g)(b))))` ... `(not (= (default a) 0))`
/// => sat), so accepting either would reinstate the hole this narrowing closed.
fn sort_provably_infinite(sort: &Sort) -> bool {
    match sort {
        // Unbounded by construction.
        Sort::Int | Sort::Real | Sort::String | Sort::RegLan => true,
        // `|Seq T|` is infinite for any inhabited `T`, and every sort is inhabited.
        Sort::Seq(_) => true,
        // `|Array I E| = |E|^|I|`, and `|I| >= 1` always, so an infinite element
        // sort forces an infinite array sort. An infinite INDEX sort does not:
        // `(Array Int E)` with `|E| = 1` has exactly one inhabitant -- which is a
        // real shape, not a hypothetical.
        Sort::Array(a) => sort_provably_infinite(&a.element_sort),
        // Finite by construction.
        Sort::Bool | Sort::BitVec(_) | Sort::FloatingPoint(..) => false,
        // Cardinality not recoverable here -- see the doc note above.
        Sort::Uninterpreted(_) | Sort::Datatype(_) => false,
        // Everything else, INCLUDING any sort added after this was written.
        //
        // The catch-all is deliberate and must stay: this predicate gates a
        // proof-checker rule, so an unclassified sort has to fail CLOSED. An
        // exhaustive match would turn "someone added a sort" into a compile
        // error, which is louder but tempts a mechanical `=> true` fix; here the
        // silent default is the safe one. `Char` lands here correctly -- it is a
        // bounded code point over [0, 196607], i.e. finite.
        _ => false,
    }
}

/// Validate an `ArrayStorePermutation` lemma in strict mode.
///
/// SCHEMA (all conditions are necessary; any failure REJECTS):
///
/// The clause must contain a POSITIVE literal whose two sides name an array
/// pair `(L, R)` — either DIRECTLY, as `(= L R)` over one array sort, or
/// READ-THROUGH, as `(= (select L k) (select R k))` where both reads are
/// well-sorted and use the SAME index term `k` — where
///  1. `L` and `R` both parse as maximal `store` chains whose every node is a
///     well-sorted array `store`, and both chains bottom out in the SAME base
///     array term (identical `TermId`);
///  2. both chains have the same length `n >= 2`;
///  3. the `n` index terms of `L`'s chain are PAIRWISE DISTINCT `TermId`s
///     (a repeated index term is rejected: `store(store(b,i,v),i,w)` and
///     `store(store(b,i,w),i,v)` write the same pair multiset but denote
///     different arrays);
///  4. the multisets of `(index, value)` `TermId` pairs of the two chains are
///     EQUAL (so `R` is a permutation of `L`);
///  5. for EVERY unordered pair `{i_p, i_q}` of the `n` index terms the clause
///     carries a POSITIVE literal `(= i_p i_q)` or `(= i_q i_p)`.
///
/// SOUNDNESS. Assume the clause false. By (5) every index pair is distinct, so
/// by (3)+(4) each chain maps `i_k` to `v_k` and agrees with the base array
/// everywhere else; the two chains are therefore pointwise equal, hence equal
/// by extensionality (SMT-LIB `ArraysEx`, the theory every array logic uses).
/// For the DIRECT conclusion that already contradicts the assumed-false
/// literal. For the READ-THROUGH conclusion, `L = R` gives
/// `select(L,k) = select(R,k)` by congruence of the well-sorted `select(_, k)`
/// function — the read-through clause is therefore strictly WEAKER than the
/// direct one over the same side conditions, never an independent claim. Either
/// way the clause is a theory tautology. Extra literals are harmless: a
/// superset of a valid clause is valid.
/// Walk the maximal leading `store` spine of `term`, debiting one unit per node
/// so the measurement is itself bounded and fails closed. Mirrors
/// `chain_extensions::parse_store_chain`'s `args[0]` base spine, so it
/// upper-bounds the nodes any single parse visits; the interned term DAG is
/// acyclic, so the walk terminates.
fn metered_store_spine_len(
    terms: &TermStore,
    term: TermId,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<usize, ProofCheckError> {
    let mut len = 0usize;
    let mut current = term;
    while let TermData::App(sym, args) = terms.get(current) {
        if !matches!(sym, Symbol::Named(name) if name == "store") || args.len() != 3 {
            break;
        }
        // Debit THIS node before descending: covers this measurement walk plus
        // `matches_store_permutation`'s single `parse_store_chain` re-walk.
        if !progress(64, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        len += 1;
        current = args[0];
    }
    Ok(len)
}

/// Debit the strict-check meter for the ACTUAL work
/// [`validate_array_store_permutation`] is about to perform, failing closed if
/// the caller's envelope cannot absorb it.
///
/// This is the store-permutation half of the `ArrayClauseSchema` fix: instead of
/// the up-front `~8 * unfolded_work^2` precharge (QUARTIC in chain length for the
/// store-commutativity clause, whose `O(P^2)` index-pair literals make
/// `unfolded_work` itself `Θ(P^2)`, which withheld correctly-decided `storecomm`
/// UNSATs), the validator now charges a TIGHT bound on
/// [`matches_store_permutation`]'s real cost through the same progress callback
/// `ResolutionRoute`/`ArrayRowChain` debit.
///
/// SOUNDNESS OF THE BOUND (it must never UNDER-charge — an unbounded check is a
/// DoS hole as severe as a wrong verdict). Let `L = literals.len()`.
///  * `matches_store_permutation` scans every literal once (`equality_sides` and
///    `permutation_conclusion_arrays` are each `O(1)` per literal) and collects
///    `PositiveEqPairs` once (`O(L)`) — covered by `64*L` up front.
///  * For EVERY literal that is a positive array-equality candidate,
///    `chains_are_validated_permutation` parses both store spines (walked here
///    per node), clones and sorts the two length-`P` `(index, value)` lists
///    (`O(P log P)`), and runs the `O(P^2)` all-unordered-index-pairs check.
///    `P^2` per candidate upper-bounds BOTH the sort and the pair check; the
///    per-node spine walks upper-bound the parses. Charging every candidate
///    (rather than stopping at the first that validates) only over-approximates.
///
/// A genuine store-commutativity clause has ONE array equality (the conclusion)
/// over one length-`P` chain, so the whole bound is `O(L + P^2)` and certifies
/// cheaply; an adversarial many-equality or long-chain clause is priced in full
/// and refused.
fn charge_store_permutation_validation(
    terms: &TermStore,
    literals: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mul = |a: usize, b: usize| a.checked_mul(b).ok_or(ProofCheckError::ResourceLimit);

    // Linear per-literal scan plus the one `PositiveEqPairs` collection.
    if !progress(
        mul(literals.len(), 64)?,
        mul(literals.len(), 4 * size_of::<TermId>())?,
    ) {
        return Err(ProofCheckError::ResourceLimit);
    }

    for &lit in literals {
        let Some((lhs, rhs)) = equality_sides(terms, lit) else {
            continue;
        };
        // RECOGNITION-PATH SORT COMPARISONS. `permutation_conclusion_arrays` and
        // `well_sorted_select_parts` compare whole `Sort` trees — `Θ(sort size)`,
        // NOT O(1) — over the sorts of `lhs`, `rhs`, and (for selects/stores)
        // their array children, on EVERY equality literal, INCLUDING ones that are
        // then rejected as non-candidates (a `None` return). Charge that
        // structural work per literal so a fan-out of rejected `(= (select A i)
        // (select A j))` literals over one huge sort cannot smuggle unbounded
        // comparison work past the meter. Each side's own sort plus its immediate
        // children's sorts upper-bound every comparison those recognizers make.
        for side in [lhs, rhs] {
            crate::quality::meter_sort(terms.sort(side), progress)?;
            if let TermData::App(_, args) = terms.get(side) {
                for &arg in args {
                    crate::quality::meter_sort(terms.sort(arg), progress)?;
                }
            }
        }
        let Some((left_array, right_array)) =
            chain_extensions::permutation_conclusion_arrays(terms, lhs, rhs)
        else {
            continue;
        };
        let left_len = metered_store_spine_len(terms, left_array, progress)?;
        let right_len = metered_store_spine_len(terms, right_array, progress)?;
        let p = left_len.max(right_len);

        // STRUCTURAL SORT COMPARISONS. `terms.sort(x) == terms.sort(y)` compares
        // whole `Sort` trees (nested sorts and owned names), so each is
        // `Θ(sort size)`, NOT O(1). `parse_store_chain` does three per spine node
        // (current/base, index, element), `permutation_conclusion_arrays` and
        // `chains_are_validated_permutation` a few more. Because the shared chain
        // is re-parsed FOR EACH candidate literal (the base payload walk charges
        // the shared store nodes only once), this structural work must be charged
        // per candidate. Measure the array sort's structural cost once (itself
        // debited), then charge `8*P + 8` copies — a sound over-count of the
        // `~6*P` per-node plus top-level comparisons.
        let mut sort_work = 0usize;
        let mut sort_bytes = 0usize;
        {
            let mut measure = |w: usize, b: usize| {
                sort_work = sort_work.saturating_add(w);
                sort_bytes = sort_bytes.saturating_add(b);
                progress(w, b)
            };
            crate::quality::meter_sort(terms.sort(left_array), &mut measure)?;
        }
        let comparisons = mul(p, 8)?.saturating_add(8);
        if !progress(mul(comparisons, sort_work)?, mul(comparisons, sort_bytes)?) {
            return Err(ProofCheckError::ResourceLimit);
        }

        // The `O(P^2)` unordered-index-pair check, plus the `O(P log P)` pair
        // sort. Scratch retained simultaneously: two parsed `(index, value)`
        // vectors (`16P` bytes), the `indices` list (`4P`), and two cloned pair
        // vectors (`16P`) — ~`36P` bytes; `64*P` covers that with hash-set and
        // growth slack.
        if !progress(mul(p, p)?, mul(p, 64)?) {
            return Err(ProofCheckError::ResourceLimit);
        }
    }
    Ok(())
}

pub(crate) fn validate_array_store_permutation(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array axiom clause must be non-empty".to_string(),
        });
    }
    reject_non_bool_literals(terms, step_id, clause, "array store permutation")?;

    let literals = flatten_clause_literals(terms, clause);
    reject_non_bool_literals(terms, step_id, &literals, "array store permutation")?;
    // Debit the validator's actual work BEFORE it runs, failing closed.
    charge_store_permutation_validation(terms, &literals, progress)?;
    if matches_store_permutation(terms, &literals) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "array store-permutation clause does not match the exact schema: it needs a \
                 positive equality between two well-sorted store chains over one common base \
                 array (or between two well-sorted reads of them at one shared index term) \
                 that are a permutation of the same (index, value) pairs, with pairwise \
                 distinct index terms and one `(= i j)` literal for every unordered index pair"
            .to_string(),
    })
}

mod row_chain_validation;
pub(crate) use row_chain_validation::validate_array_row_chain;

/// Validate an `ArrayExtensionality` lemma in strict mode.
///
/// SCHEMA. The clause must be EXACTLY a two-literal Skolemized extensionality
/// chain for an array pair `(a, b)` at one or more witness indices:
///
/// ```text
/// (cl (= a b)
///     (not (= (select ... (select a k0) ... kn)
///             (select ... (select b k0) ... kn))))
/// ```
///
/// Every corresponding pair of `select`s must use the SAME index term and be
/// well-sorted. The polarities are fixed: the root array equality is POSITIVE
/// and the final select equality is NEGATED. The one-level case is the usual
/// `(= a b) ∨ ¬(= (select a k) (select b k))` schema. Its mirror image is a
/// DIFFERENT (and false) claim and is rejected.
///
/// A second exact one-level schema permits each raw witness read to be folded
/// through const-array, well-sorted stores, and array ITEs. The checker
/// independently re-derives that fold with
/// [`recognize_folded_array_extensionality`]. Because a const-array fold can
/// erase `k` from the clause, the checked registry supplies candidate
/// `(k, a, b)` bindings; no symbol name or emitter annotation is trusted.
///
/// WHY A REGISTRY IS REQUIRED. Unlike every other schema in this module, this
/// clause is **not** a theory tautology: `(select a k) = (select b k)` is
/// perfectly consistent with `a != b` for arbitrary index terms. The clause is
/// sound only as a chain of Skolemized array-theory `diff` choices — one fresh
/// witness for every intermediate array pair. That is provenance, not shape,
/// so `registry` is mandatory: with `None` the lemma fails closed (the
/// historical behaviour of this entry point).
///
/// CHECKS (all necessary; any failure REJECTS):
///  1. the clause matches the schema above and yields every `(a_i, b_i, k_i)`;
///  2. every `k_i` is an atomic symbol (`TermData::Var`), not a compound term;
///  3. an `array_ext_diff_intro` step in the SAME proof binds each symbol
///     (looked up by NAME, so a same-named symbol at another sort cannot
///     smuggle a binding in);
///  4. every introduction resolves to the very `TermId` used at that level and
///     binds the UNORDERED pair `{a_i, b_i}` used there — an introduction for a
///     different array pair is rejected.
///
/// Conditions the [`ExtDiffRegistry`] itself already enforced when it was
/// built (see [`ExtDiffRegistry::collect`]): the symbol is FRESH (occurs in no
/// problem assertion and in no `assume` of the proof), is bound exactly ONCE,
/// and all introduced-witness dependencies through array pairs are ACYCLIC.
///
/// SOUNDNESS. Let `P` be the problem and let the checks above hold. Take any
/// model `M ⊨ P`. Interpret introduced witnesses in a topological order of the
/// registry's dependency DAG. When choosing `k_i`, every witness occurring in
/// `a_i` or `b_i` is already fixed. If `a_i = b_i`, choose `k_i` arbitrarily;
/// otherwise extensionality supplies an index where their selected values
/// differ. Thus, if the root pair differs, induction down the recognized chain
/// makes the final selected pair differ and satisfies the second literal.
/// Bound-once makes every choice unique to its pair, so every model of `P`
/// extends to all certified clauses and a refutation of the extension refutes
/// `P`.
pub(crate) fn validate_array_extensionality(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    registry: Option<&ExtDiffRegistry>,
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array axiom clause must be non-empty".to_string(),
        });
    }
    reject_non_bool_literals(terms, step_id, clause, "array extensionality")?;

    let literals = flatten_clause_literals(terms, clause);
    reject_non_bool_literals(terms, step_id, &literals, "array extensionality")?;
    if let Some(bindings) = extensionality_chain_parts(terms, &literals) {
        let Some(registry) = registry else {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "array extensionality clause carries a diff witness with no \
                         checked provenance: this checker was given no problem \
                         assertion set, so it cannot verify the witness is fresh and \
                         fails closed"
                    .to_string(),
            });
        };

        for (array_a, array_b, witness) in bindings {
            validate_extensionality_binding(terms, step_id, array_a, array_b, witness, registry)?;
        }
        return Ok(());
    }

    // A late solver pass may normalize each witness read through const-array,
    // store, and array-ITE structure before asserting the extensionality
    // clause. Such a clause no longer exposes the witness as a raw select
    // spine, so provenance cannot be recovered from shape. Instead, try every
    // already-checked introduction: the registry has independently enforced
    // atomicity, sort, freshness, single binding, and acyclic dependencies.
    // The structural recognizer below then proves that the exact clause is the
    // fold of that binding's array pair at that binding's witness.
    if let Some(registry) = registry {
        if validate_folded_registry_match_with_budget(terms, step_id, clause, registry)? {
            return Ok(());
        }
    }

    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "array extensionality clause does not match either exact checked schema: \
                 `(= a b) ∨ ¬(= a[k0]...[kn] b[k0]...[kn])`, or the one-level \
                 independently folded reads of a registered diff-witness pair"
            .to_string(),
    })
}

/// Validate one witness link from a recognized extensionality chain against
/// the whole-proof introduction registry.
fn validate_extensionality_binding(
    terms: &TermStore,
    step_id: ProofId,
    array_a: TermId,
    array_b: TermId,
    witness: TermId,
    registry: &ExtDiffRegistry,
) -> Result<(), ProofCheckError> {
    let TermData::Var(witness_name, _) = terms.get(witness) else {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array extensionality diff witness must be an atomic symbol \
                     introduced by an `array_ext_diff_intro` step"
                .to_string(),
        });
    };

    let Some(binding) = registry.get(witness_name) else {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "array extensionality diff witness `{witness_name}` has no \
                 `array_ext_diff_intro` step binding it to an array pair"
            ),
        });
    };

    if binding.witness != witness {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "array extensionality diff witness `{witness_name}` resolves to a \
                 different term than the one its `array_ext_diff_intro` bound"
            ),
        });
    }

    if unordered(binding.array_a, binding.array_b) != unordered(array_a, array_b) {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "array extensionality diff witness `{witness_name}` was introduced \
                 for a DIFFERENT array pair (step {}) than the one this clause uses",
                binding.step
            ),
        });
    }

    Ok(())
}

/// Recognize `clause` as the exact ONE-LEVEL Skolemized extensionality schema,
/// returning `(array_a, array_b, witness_index)`.
///
/// This API deliberately preserves its historical one-level contract. Use
/// [`recognize_array_extensionality_chain`] when an emitter needs every witness
/// in a nested select chain. Recognition alone is NOT a licence to accept the
/// clause — the provenance half (freshness, single binding, matching pair)
/// lives in [`ExtDiffRegistry`] and is checked separately.
#[must_use]
pub fn recognize_array_extensionality(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TermId, TermId, TermId)> {
    let mut bindings = recognize_array_extensionality_chain(terms, clause)?;
    if bindings.len() != 1 {
        return None;
    }
    bindings.pop()
}

/// Recognize an exact one-or-more-level Skolemized array-extensionality chain.
///
/// The returned tuples are `(array_a, array_b, witness_index)` in outer-to-inner
/// order. Each tuple describes the array pair selected by its witness;
/// later pairs therefore contain the earlier witnesses syntactically. Shape
/// recognition alone does not certify provenance: callers that promote a
/// clause must still provide one checked [`ExtDiffRegistry`] binding per tuple.
#[must_use]
pub fn recognize_array_extensionality_chain(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<Vec<(TermId, TermId, TermId)>> {
    if clause.is_empty()
        || clause
            .iter()
            .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return None;
    }
    let literals = flatten_clause_literals(terms, clause);
    if literals
        .iter()
        .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return None;
    }
    extensionality_chain_parts(terms, &literals)
}

/// Recognize a one-level Skolemized array-extensionality clause whose witness
/// reads have been structurally folded through array constructors.
///
/// The exact accepted shape is
///
/// ```text
/// (= array_a array_b) ∨ ¬(= fold(array_a, witness)
///                              fold(array_b, witness))
/// ```
///
/// with exactly two literals. `fold` is re-derived independently and accepts
/// only the proof-shape-preserving rules used by the late datatype-array lane:
/// const-array fill, ROW1, ROW2 for two distinct constant indices, the general
/// McCarthy store ITE, array-ITE distribution, and raw-select fallback. Every
/// array operation and intermediate term is sort-checked, and recursion stops
/// at the same depth-64 raw-select fallback as the emitter.
///
/// This function checks shape only. The clause is not a theory tautology for
/// an arbitrary `witness`; callers that use it for proof certification must
/// separately establish fresh-witness provenance for exactly the supplied
/// array pair. Strict checking does that through [`ExtDiffRegistry`].
#[must_use]
pub fn recognize_folded_array_extensionality(
    terms: &TermStore,
    clause: &[TermId],
    array_a: TermId,
    array_b: TermId,
    witness: TermId,
) -> bool {
    let remaining = AtomicUsize::new(FOLDED_READ_WORK_LIMIT);
    let mut budget = FoldedReadWorkBudget::new(&remaining);
    recognize_folded_array_extensionality_with_budget(
        terms,
        clause,
        array_a,
        array_b,
        witness,
        &mut budget,
    )
}

fn recognize_folded_array_extensionality_with_budget(
    terms: &TermStore,
    clause: &[TermId],
    array_a: TermId,
    array_b: TermId,
    witness: TermId,
    budget: &mut FoldedReadWorkBudget<'_>,
) -> bool {
    let Sort::Array(array_sort) = terms.sort(array_a) else {
        return false;
    };
    if array_a == array_b
        || terms.sort(array_b) != terms.sort(array_a)
        || terms.sort(witness) != &array_sort.index_sort
    {
        return false;
    }
    if clause.is_empty()
        || clause
            .iter()
            .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return false;
    }

    let literals = flatten_clause_literals(terms, clause);
    if literals.len() != 2
        || literals
            .iter()
            .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return false;
    }

    let mut fold_matcher = FoldedReadMatcher::new(terms, budget);
    for (root_literal, folded_literal) in [(literals[0], literals[1]), (literals[1], literals[0])] {
        if !matches_equality_pair(terms, root_literal, array_a, array_b) {
            continue;
        }
        let Some((folded_left, folded_right)) = negated_equality_sides(terms, folded_literal)
        else {
            continue;
        };
        if (fold_matcher.matches(array_a, witness, folded_left, 0)
            && fold_matcher.matches(array_b, witness, folded_right, 0))
            || (fold_matcher.matches(array_a, witness, folded_right, 0)
                && fold_matcher.matches(array_b, witness, folded_left, 0))
        {
            return true;
        }
    }
    false
}

const FOLDED_READ_WORK_LIMIT: usize = 100_000;
const FOLDED_REGISTRY_WORK_LIMIT: usize = FOLDED_READ_WORK_LIMIT;

struct FoldedReadWorkBudget<'a> {
    remaining: &'a AtomicUsize,
    exhausted: bool,
}

impl<'a> FoldedReadWorkBudget<'a> {
    fn new(remaining: &'a AtomicUsize) -> Self {
        Self {
            remaining,
            exhausted: false,
        }
    }

    // MODEL_CHECKER_CONSUMER's pinned compiler predates the `try_update` rename, while the
    // current Trust compiler deprecates its semantics-identical old name.
    #[allow(deprecated)]
    fn consume(&mut self) -> bool {
        // `fetch_update` is the stable equivalent of the unstable
        // `atomic_try_update::try_update` (identical signature and
        // Ok(prev)/Err(prev) semantics). Using it keeps ay-proof buildable as a
        // dependency under model-checker-consumer's pinned nightly, which does not enable the
        // `atomic_try_update` feature.
        if self
            .remaining
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |remaining| {
                remaining.checked_sub(1)
            })
            .is_err()
        {
            self.exhausted = true;
            return false;
        }
        true
    }
}

/// Try every certified binding under ONE shared work budget. Scanning a
/// binding and every uncached folded-read product state both consume from the
/// same allowance, so neither a large registry nor repeated near-matches can
/// multiply the per-recognizer ceiling. Exhaustion rejects the lemma.
pub(super) fn validate_folded_registry_match_with_budget(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    registry: &ExtDiffRegistry,
) -> Result<bool, ProofCheckError> {
    let mut budget = FoldedReadWorkBudget::new(&registry.folded_work_remaining);
    for binding in registry.bindings.values() {
        if !budget.consume() {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "array extensionality folded-read registry matching exhausted its \
                         shared whole-proof work budget"
                    .to_string(),
            });
        }
        if recognize_folded_array_extensionality_with_budget(
            terms,
            clause,
            binding.array_a,
            binding.array_b,
            binding.witness,
            &mut budget,
        ) {
            return Ok(true);
        }
        if budget.exhausted {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "array extensionality folded-read registry matching exhausted its \
                         shared whole-proof work budget"
                    .to_string(),
            });
        }
    }
    Ok(false)
}

mod folded_read;
pub(crate) use folded_read::distinct_interpreted_indices;
use folded_read::FoldedReadMatcher;

fn is_exact_well_sorted_select(
    terms: &TermStore,
    candidate: TermId,
    array: TermId,
    index: TermId,
) -> bool {
    well_sorted_select_parts(terms, candidate).is_some_and(|(candidate_array, candidate_index)| {
        candidate_array == array && candidate_index == index
    })
}

// ---------- extensionality diff-witness provenance ----------

/// One `array_ext_diff_intro` binding: the fresh witness symbol and the
/// UNORDERED array pair it was minted for.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ExtDiffBinding {
    /// The witness term (an atomic `TermData::Var`).
    pub(crate) witness: TermId,
    /// First array of the pair.
    pub(crate) array_a: TermId,
    /// Second array of the pair.
    pub(crate) array_b: TermId,
    /// The introducing step, for diagnostics.
    pub(crate) step: ProofId,
}

/// Whole-proof registry of extensionality diff-witness introductions.
///
/// Built ONCE per strict check from the proof's `array_ext_diff_intro` steps
/// and the problem's assertion terms. Construction is where the whole-proof
/// soundness conditions are enforced (see
/// [`ExtDiffRegistry::collect`]); per-step validation then only has to confirm
/// that the clause in hand matches its symbol's single recorded binding.
#[derive(Debug)]
pub struct ExtDiffRegistry {
    bindings: DetHashMap<String, ExtDiffBinding>,
    /// One budget for every folded-extensionality lemma in this proof. Keeping
    /// it on the proof-scoped registry prevents many individually bounded
    /// lemmas from multiplying the checker work ceiling.
    folded_work_remaining: AtomicUsize,
}

impl Default for ExtDiffRegistry {
    fn default() -> Self {
        Self {
            bindings: DetHashMap::default(),
            folded_work_remaining: AtomicUsize::new(FOLDED_REGISTRY_WORK_LIMIT),
        }
    }
}

impl ExtDiffRegistry {
    fn get(&self, name: &str) -> Option<&ExtDiffBinding> {
        self.bindings.get(name)
    }

    /// Whether the registry recorded no introductions at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Build the registry for `proof`, given the problem's assertion terms.
    ///
    /// `problem_assertions` must be the terms the PROBLEM asserted — the
    /// authored assertion window, NOT the solver-time assertion stack (which
    /// also carries the injected extensionality axioms themselves, and would
    /// make every witness look non-fresh). Passing a SUPERSET is always safe:
    /// every extra term can only make the freshness test stricter.
    ///
    /// Enforced here, once, for every introduction:
    ///
    ///  1. SHAPE — no premises, no conclusion clause, exactly three `:args`
    ///     `(k a b)` with `a`, `b` two DISTINCT terms of the same array sort
    ///     and `k` an atomic symbol at that sort's index sort
    ///     (`validate_ext_diff_intro`).
    ///  2. BOUND ONCE — two introductions naming the same symbol are rejected
    ///     outright, so a symbol can never acquire two array-pair definitions
    ///     (which would be unsound: one index cannot in general witness two
    ///     independent array disequalities).
    ///  3. FRESH — the symbol's NAME must occur in no `problem_assertions`
    ///     term and in no `assume` step of the proof. This is the soundness
    ///     crux and is verified against the problem, never assumed from a name
    ///     prefix or a solver-side "this is a Skolem" flag: a witness that the
    ///     problem also constrains is not a witness at all.
    ///  4. ACYCLIC DEPENDENCIES — an introduced witness may occur in another
    ///     witness's array pair only when all such dependencies form a DAG.
    ///     Direct self-reference is the one-node cycle. Longer cycles are just
    ///     as unsound: the witnesses would have to be chosen simultaneously,
    ///     and the individually satisfiable Skolem extensions need not have a
    ///     joint solution.
    ///
    /// # Errors
    ///
    /// Returns [`ProofCheckError::InvalidTheoryLemma`] for the offending
    /// introduction step whenever any condition fails. There is deliberately no
    /// lenient mode: an introduction that cannot be verified makes the whole
    /// check fail rather than silently dropping the binding (which would only
    /// re-surface as an unbound witness later, with a worse diagnostic).
    pub fn collect(
        proof: &Proof,
        terms: &TermStore,
        problem_assertions: &[TermId],
    ) -> Result<Self, ProofCheckError> {
        let mut bindings: DetHashMap<String, ExtDiffBinding> = DetHashMap::default();

        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            let step_id = ProofId(index as u32);
            let (witness, array_a, array_b, name) =
                validate_ext_diff_intro(terms, step_id, clause, premises, args)?;

            // (2) bound once.
            if let Some(prior) = bindings.insert(
                name.clone(),
                ExtDiffBinding {
                    witness,
                    array_a,
                    array_b,
                    step: step_id,
                },
            ) {
                return Err(ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: format!(
                        "array ext-diff witness `{name}` is introduced more than once \
                         (already bound at step {}); a difference witness may bind to \
                         exactly one array pair",
                        prior.step
                    ),
                });
            }
        }

        if bindings.is_empty() {
            return Ok(Self {
                bindings,
                folded_work_remaining: AtomicUsize::new(FOLDED_REGISTRY_WORK_LIMIT),
            });
        }

        // (4) Dependencies between fresh witnesses must be acyclic. An edge
        // `k -> j` means that the arrays whose difference `k` witnesses contain
        // `j`, so `j` has to be interpreted before `k`. A DAG admits exactly
        // that topological interpretation. A cycle does not: for Bool-indexed
        // arrays, one clause can force `k = not j` while another forces `j = k`,
        // making an originally satisfiable problem inconsistent. Checking only
        // direct self-reference misses that two-witness counterexample.
        validate_ext_diff_dependency_graph(terms, &bindings)?;

        // (3) freshness, checked against the problem itself. One traversal of
        // the problem terms and the proof's `assume` leaves collects every
        // symbol name they mention; any introduced witness in that set is not
        // fresh and the proof is rejected.
        let mut problem_symbols: DetHashSet<String> = det_hash_set_new();
        let mut visited: DetHashSet<TermId> = det_hash_set_new();
        for &assertion in problem_assertions {
            collect_symbol_names(terms, assertion, &mut problem_symbols, &mut visited);
        }
        for step in &proof.steps {
            if let ProofStep::Assume(term) = step {
                collect_symbol_names(terms, *term, &mut problem_symbols, &mut visited);
            }
        }
        for (name, binding) in &bindings {
            if problem_symbols.contains(name) {
                return Err(ProofCheckError::InvalidTheoryLemma {
                    step: binding.step,
                    reason: format!(
                        "array ext-diff witness `{name}` is NOT fresh: the symbol also \
                         occurs in the problem, so the extensionality clause over it is \
                         not a conservative extension"
                    ),
                });
            }
        }

        Ok(Self {
            bindings,
            folded_work_remaining: AtomicUsize::new(FOLDED_REGISTRY_WORK_LIMIT),
        })
    }

    #[cfg(test)]
    pub(super) fn set_folded_work_budget_for_test(&self, limit: usize) {
        self.folded_work_remaining.store(limit, Ordering::Relaxed);
    }
}

/// Verify that introduced extensionality witnesses admit a topological choice
/// order.
///
/// For each binding `k := diff(a, b)`, every other introduced witness whose
/// symbol occurs in `a` or `b` is a dependency of `k`. Kahn elimination proves
/// the graph acyclic without recursion; if nodes remain, following unresolved
/// dependencies yields a concrete cycle for the diagnostic.
fn validate_ext_diff_dependency_graph(
    terms: &TermStore,
    bindings: &DetHashMap<String, ExtDiffBinding>,
) -> Result<(), ProofCheckError> {
    let Some(fallback_step) = bindings.values().next().map(|binding| binding.step) else {
        return Ok(());
    };
    let invariant_error = |step: ProofId, detail: &str| ProofCheckError::InvalidTheoryLemma {
        step,
        reason: format!(
            "array ext-diff dependency graph invariant failed: {detail}; \
             refusing to certify witness provenance"
        ),
    };
    let mut dependencies: DetHashMap<String, DetHashSet<String>> = DetHashMap::default();

    for (name, binding) in bindings {
        let mut pair_symbols: DetHashSet<String> = det_hash_set_new();
        let mut visited: DetHashSet<TermId> = det_hash_set_new();
        collect_symbol_names(terms, binding.array_a, &mut pair_symbols, &mut visited);
        collect_symbol_names(terms, binding.array_b, &mut pair_symbols, &mut visited);

        let deps: DetHashSet<String> = pair_symbols
            .into_iter()
            .filter(|candidate| bindings.contains_key(candidate))
            .collect();
        if deps.contains(name) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: binding.step,
                reason: format!(
                    "array ext-diff witness `{name}` occurs inside the array pair \
                     it is introduced for; the Skolem definition would be circular"
                ),
            });
        }
        dependencies.insert(name.clone(), deps);
    }

    // `remaining[k]` is the number of not-yet-eliminated witnesses that `k`
    // depends on. The reverse adjacency lets one completed dependency release
    // every witness waiting on it.
    let mut remaining: DetHashMap<String, usize> = DetHashMap::default();
    let mut dependents: DetHashMap<String, Vec<String>> = DetHashMap::default();
    for (name, deps) in &dependencies {
        remaining.insert(name.clone(), deps.len());
        for dependency in deps {
            dependents
                .entry(dependency.clone())
                .or_default()
                .push(name.clone());
        }
    }

    let mut ready: Vec<String> = remaining
        .iter()
        .filter_map(|(name, &count)| (count == 0).then_some(name.clone()))
        .collect();
    let mut eliminated = 0usize;
    while let Some(name) = ready.pop() {
        eliminated += 1;
        let Some(waiting) = dependents.get(&name) else {
            continue;
        };
        for dependent in waiting {
            let Some(count) = remaining.get_mut(dependent) else {
                return Err(invariant_error(
                    fallback_step,
                    "reverse edge names an unregistered witness",
                ));
            };
            if *count == 0 {
                return Err(invariant_error(
                    bindings
                        .get(dependent)
                        .map_or(fallback_step, |binding| binding.step),
                    "dependency count was released more than once",
                ));
            }
            *count -= 1;
            if *count == 0 {
                ready.push(dependent.clone());
            }
        }
    }
    if eliminated == bindings.len() {
        return Ok(());
    }

    let unresolved: DetHashSet<String> = remaining
        .iter()
        .filter_map(|(name, &count)| (count != 0).then_some(name.clone()))
        .collect();
    let Some(mut current) = unresolved.iter().min().cloned() else {
        return Err(invariant_error(
            fallback_step,
            "elimination stopped without an unresolved witness",
        ));
    };
    let mut positions: DetHashMap<String, usize> = DetHashMap::default();
    let mut path: Vec<String> = Vec::new();
    loop {
        if let Some(&cycle_start) = positions.get(&current) {
            let mut cycle = path[cycle_start..].to_vec();
            cycle.push(current.clone());
            let Some(binding) = bindings.get(&current) else {
                return Err(invariant_error(
                    fallback_step,
                    "cycle path names an unregistered witness",
                ));
            };
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: binding.step,
                reason: format!(
                    "array ext-diff witness dependency cycle `{}`; fresh witnesses \
                     must admit an acyclic introduction order",
                    cycle.join(" -> ")
                ),
            });
        }
        positions.insert(current.clone(), path.len());
        path.push(current.clone());
        let Some(current_dependencies) = dependencies.get(&current) else {
            return Err(invariant_error(
                bindings
                    .get(&current)
                    .map_or(fallback_step, |binding| binding.step),
                "registered witness has no dependency set",
            ));
        };
        let Some(next) = current_dependencies
            .iter()
            .filter(|dependency| unresolved.contains(*dependency))
            .min()
            .cloned()
        else {
            return Err(invariant_error(
                bindings
                    .get(&current)
                    .map_or(fallback_step, |binding| binding.step),
                "unresolved witness has no unresolved dependency",
            ));
        };
        current = next;
    }
}

/// Structural validation of one `array_ext_diff_intro` step, returning
/// `(witness, array_a, array_b, witness_name)`.
///
/// The step is a DEFINITION, so it must be inert as an inference: no premises
/// and no conclusion clause (the checker records it as clause-free, exactly
/// like an `anchor`, so it can never be resolved against or seed a RUP check).
pub(crate) fn validate_ext_diff_intro(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
) -> Result<(TermId, TermId, TermId, String), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };
    if !clause.is_empty() {
        return Err(invalid(
            "array ext-diff introduction is a definition and must conclude no clause".to_string(),
        ));
    }
    if !premises.is_empty() {
        return Err(invalid(
            "array ext-diff introduction must not have premises".to_string(),
        ));
    }
    let [witness, array_a, array_b] = args else {
        return Err(invalid(
            "array ext-diff introduction must carry exactly three arguments \
             (witness, array, array)"
                .to_string(),
        ));
    };
    let TermData::Var(name, _) = terms.get(*witness) else {
        return Err(invalid(
            "array ext-diff introduction witness must be an atomic symbol".to_string(),
        ));
    };
    let Sort::Array(array_sort) = terms.sort(*array_a) else {
        return Err(invalid(
            "array ext-diff introduction must be for two array-sorted terms".to_string(),
        ));
    };
    if terms.sort(*array_a) != terms.sort(*array_b) {
        return Err(invalid(
            "array ext-diff introduction pair has mismatched array sorts".to_string(),
        ));
    }
    if array_a == array_b {
        return Err(invalid(
            "array ext-diff introduction pair must be two distinct array terms".to_string(),
        ));
    }
    if terms.sort(*witness) != &array_sort.index_sort {
        return Err(invalid(
            "array ext-diff introduction witness is not at the array's index sort".to_string(),
        ));
    }
    Ok((*witness, *array_a, *array_b, name.clone()))
}

/// Collect every symbol name mentioned by `root` — variables, application
/// heads, and binder names alike.
///
/// Deliberately over-approximates: a binder-bound name is collected too, so a
/// witness that merely SHARES a name with some quantified variable is treated
/// as non-fresh. Over-approximating can only reject more proofs, never accept
/// one, which is the correct direction for a freshness test.
fn collect_symbol_names(
    terms: &TermStore,
    root: TermId,
    names: &mut DetHashSet<String>,
    visited: &mut DetHashSet<TermId>,
) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        match terms.get(id) {
            TermData::Var(name, _) => {
                names.insert(name.clone());
            }
            TermData::App(sym, args) => {
                names.insert(sym.name().to_string());
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    names.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                for (name, _) in vars {
                    names.insert(name.clone());
                }
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => {}
        }
    }
}

// ---------- helpers ----------

fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(Symbol::Named(sym), args) = terms.get(clause[0]) {
            if sym == "or" {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

fn reject_non_bool_literals(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    context: &str,
) -> Result<(), ProofCheckError> {
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "{context} literal has non-Bool sort {:?}; axiom clauses \
                     must be propositional",
                    terms.sort(lit)
                ),
            });
        }
    }
    Ok(())
}

fn matches_row1_unit(terms: &TermStore, literals: &[TermId]) -> bool {
    literals.len() == 1
        && equality_sides(terms, literals[0]).is_some_and(|(lhs, rhs)| {
            row1_eq_parts(terms, lhs, rhs)
                .is_some_and(|(_, store_index, _, select_index)| store_index == select_index)
        })
}

fn matches_row1_conditional(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 2 {
        return false;
    }
    for eq_lit in literals {
        let Some((select_side, value_side)) = equality_sides(terms, *eq_lit) else {
            continue;
        };
        let Some((store_array, store_index, _store_value, select_index)) =
            row1_eq_parts(terms, select_side, value_side)
        else {
            continue;
        };
        let Some(diseq_lit) = literals.iter().copied().find(|&lit| lit != *eq_lit) else {
            continue;
        };
        if matches_not_equality_pair(terms, diseq_lit, store_index, select_index)
            && matches!(terms.sort(store_array), Sort::Array(_))
        {
            return true;
        }
    }
    false
}

fn matches_row2_conditional(terms: &TermStore, literals: &[TermId]) -> bool {
    // `read_over_write_neg` is the exact two-literal ROW2 axiom.  A generator
    // may have additional explanation literals, but those belong in an
    // explicit weakening/resolution step rather than being attributed directly
    // to the primitive Alethe rule (and to its per-step Lean firewall).
    if literals.len() != 2 {
        return false;
    }
    for eq_lit in literals {
        let Some((lhs, rhs)) = equality_sides(terms, *eq_lit) else {
            continue;
        };
        let Some((store_index, select_index)) = row2_eq_parts(terms, lhs, rhs) else {
            continue;
        };
        if literals.iter().copied().any(|lit| {
            lit != *eq_lit && matches_equality_pair(terms, lit, store_index, select_index)
        }) {
            return true;
        }
    }
    false
}

/// Match an exact two-literal Skolemized extensionality chain and return every
/// `(array_a, array_b, witness_index)` link in outer-to-inner order.
///
/// The polarity assignment is FIXED — positive root-array equality, negated
/// final-select equality. Both select spines must reach the root pair at the
/// same depth, use the SAME well-sorted index term at every level, and preserve
/// one global left/right orientation. Any other arrangement (in particular the
/// mirror image `¬(= a b) ∨ (= (select a k) (select b k))`, which is a
/// different and unsound claim) fails to match.
fn extensionality_chain_parts(
    terms: &TermStore,
    literals: &[TermId],
) -> Option<Vec<(TermId, TermId, TermId)>> {
    if literals.len() != 2 {
        return None;
    }
    for (array_eq_lit, witness_lit) in [(literals[0], literals[1]), (literals[1], literals[0])] {
        let Some((array_a, array_b)) = equality_sides(terms, array_eq_lit) else {
            continue;
        };
        let Sort::Array(_) = terms.sort(array_a) else {
            continue;
        };
        if terms.sort(array_a) != terms.sort(array_b) || array_a == array_b {
            continue;
        }
        let Some((sel_a, sel_b)) = negated_equality_sides(terms, witness_lit) else {
            continue;
        };
        if let Some(bindings) = select_chain_to_array_pair(terms, array_a, array_b, sel_a, sel_b) {
            return Some(bindings);
        }
    }
    None
}

/// Peel two select spines together until they reach `(root_a, root_b)` in one
/// global orientation. The roots themselves may be select terms, so matching
/// their exact `TermId`s is the stopping condition; peeling to the ultimate
/// non-select bases would reject valid extensionality over array-valued reads.
fn select_chain_to_array_pair(
    terms: &TermStore,
    root_a: TermId,
    root_b: TermId,
    mut left: TermId,
    mut right: TermId,
) -> Option<Vec<(TermId, TermId, TermId)>> {
    let mut reversed_bindings = Vec::new();
    let roots_reversed = loop {
        if left == root_a && right == root_b {
            break false;
        }
        if left == root_b && right == root_a {
            break true;
        }

        let (left_array, left_index) = well_sorted_select_parts(terms, left)?;
        let (right_array, right_index) = well_sorted_select_parts(terms, right)?;
        if left_index != right_index
            || left_array == right_array
            || terms.sort(left_array) != terms.sort(right_array)
        {
            return None;
        }

        reversed_bindings.push((left_array, right_array, left_index));
        left = left_array;
        right = right_array;
    };

    if reversed_bindings.is_empty() {
        return None;
    }
    reversed_bindings.reverse();
    if roots_reversed {
        for (array_a, array_b, _) in &mut reversed_bindings {
            std::mem::swap(array_a, array_b);
        }
    }
    Some(reversed_bindings)
}

fn row1_eq_parts(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, TermId, TermId, TermId)> {
    // Try EACH side as the `select`-of-`store` side, taking the OTHER side as
    // the stored value. Both orientations must be attempted: a stored value can
    // itself parse as a select-of-store (routine in swap/permutation proofs, and
    // the bulk of the remaining conditional-ROW1 trust steps), so committing to
    // the first parseable side misses the mirror instance
    // `(= v (select (store C i v) k))` where `v` is such a term. Equality is
    // symmetric, so whichever orientation exhibits `store_value == value_term`
    // is the genuine read-over-write; the caller's side conditions (the
    // `(not (= store_index select_index))` guard for the conditional schema, or
    // `store_index == select_index` for the unit schema) are unchanged and
    // apply to the `store_index`/`select_index` of the returned orientation.
    for (select_side, value_term) in [(lhs, rhs), (rhs, lhs)] {
        if let Some((base_array, store_index, store_value, select_index)) =
            select_store_parts(terms, select_side)
        {
            if store_value == value_term {
                return Some((base_array, store_index, store_value, select_index));
            }
        }
    }
    None
}

fn row2_eq_parts(terms: &TermStore, lhs: TermId, rhs: TermId) -> Option<(TermId, TermId)> {
    // Do not require the base-side select to be free of another `store`.
    // ROW2 is closed under arbitrary array terms, including a nested store:
    //   select(store(store(a, i, v), j, x), i) = select(store(a, i, v), i)
    // The old `(Some, None)` match rejected this exact schema merely because
    // `select(store(a, i, v), i)` can itself be decomposed as a select-store.
    if let Some((base_array, store_index, _, select_index)) = select_store_parts(terms, lhs) {
        if is_select_of(terms, rhs, base_array, select_index) {
            return Some((store_index, select_index));
        }
    }
    if let Some((base_array, store_index, _, select_index)) = select_store_parts(terms, rhs) {
        if is_select_of(terms, lhs, base_array, select_index) {
            return Some((store_index, select_index));
        }
    }
    None
}

fn select_store_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId, TermId)> {
    let TermData::App(select_sym, select_args) = terms.get(term) else {
        return None;
    };
    if !matches!(select_sym, Symbol::Named(name) if name == "select") || select_args.len() != 2 {
        return None;
    }
    let TermData::App(store_sym, store_args) = terms.get(select_args[0]) else {
        return None;
    };
    if !matches!(store_sym, Symbol::Named(name) if name == "store") || store_args.len() != 3 {
        return None;
    }
    let Sort::Array(array_sort) = terms.sort(store_args[0]) else {
        return None;
    };
    // A named `store`/`select` application is an array-theory operator only
    // when its complete signature agrees with the base array sort.  `TermStore`
    // intentionally permits raw applications, so the strict proof boundary
    // cannot assume these relationships were checked by the frontend.
    if terms.sort(select_args[0]) != terms.sort(store_args[0])
        || terms.sort(store_args[1]) != &array_sort.index_sort
        || terms.sort(store_args[2]) != &array_sort.element_sort
        || terms.sort(select_args[1]) != &array_sort.index_sort
        || terms.sort(term) != &array_sort.element_sort
    {
        return None;
    }
    Some((store_args[0], store_args[1], store_args[2], select_args[1]))
}

fn is_select_of(terms: &TermStore, term: TermId, array: TermId, index: TermId) -> bool {
    let Sort::Array(array_sort) = terms.sort(array) else {
        return false;
    };
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(sym), args) if sym == "select"
            && args.len() == 2
            && args[0] == array
            && args[1] == index
            && terms.sort(index) == &array_sort.index_sort
            && terms.sort(term) == &array_sort.element_sort
    )
}

fn select_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(sym), args) if sym == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

// ---------- n-ary store-chain schemas ----------

/// A maximally-unrolled `store` chain: the innermost non-`store` base array
/// plus the written `(index, value)` pairs listed OUTERMOST-FIRST.
struct StoreChain {
    base: TermId,
    entries: Vec<(TermId, TermId)>,
}

/// Parse `term` as a maximal chain of well-sorted array `store` applications.
///
/// Returns `None` unless the term (and every `store` node inside it) is
/// array-sorted with a signature that agrees with the base array's sort.
/// `TermStore` intentionally permits raw applications, so the strict proof
/// boundary cannot assume the frontend checked these relationships.
fn parse_store_chain(terms: &TermStore, term: TermId) -> Option<StoreChain> {
    let Sort::Array(_) = terms.sort(term) else {
        return None;
    };
    let mut entries = Vec::new();
    let mut current = term;
    while let TermData::App(sym, args) = terms.get(current) {
        if !matches!(sym, Symbol::Named(name) if name == "store") || args.len() != 3 {
            break;
        }
        let (base, index, value) = (args[0], args[1], args[2]);
        let Sort::Array(array_sort) = terms.sort(base) else {
            return None;
        };
        if terms.sort(current) != terms.sort(base)
            || terms.sort(index) != &array_sort.index_sort
            || terms.sort(value) != &array_sort.element_sort
        {
            return None;
        }
        entries.push((index, value));
        current = base;
    }
    Some(StoreChain {
        base: current,
        entries,
    })
}

/// The positive `(= p q)` literals of a clause, normalized to unordered pairs
/// so `(= i j)` and `(= j i)` both answer a lookup for `{i, j}`.
struct PositiveEqPairs {
    pairs: DetHashSet<(TermId, TermId)>,
}

impl PositiveEqPairs {
    fn collect(terms: &TermStore, literals: &[TermId]) -> Self {
        let mut pairs = det_hash_set_new();
        for &lit in literals {
            if let Some((a, b)) = equality_sides(terms, lit) {
                pairs.insert(unordered(a, b));
            }
        }
        Self { pairs }
    }

    fn contains(&self, a: TermId, b: TermId) -> bool {
        self.pairs.contains(&unordered(a, b))
    }
}

fn unordered(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

/// See [`validate_array_store_permutation`] for the schema and its soundness
/// argument. Every numbered condition there is enforced here.
fn matches_store_permutation(terms: &TermStore, literals: &[TermId]) -> bool {
    // Cheap pre-filter: the schema needs at least one positive equality between
    // two array-sorted `store` applications (or two reads of them at one shared
    // index), plus one index-equality literal.
    if literals.len() < 2 {
        return false;
    }
    let mut pairs: Option<PositiveEqPairs> = None;
    for &lit in literals {
        let Some((lhs, rhs)) = equality_sides(terms, lit) else {
            continue;
        };
        let Some((left_array, right_array)) =
            chain_extensions::permutation_conclusion_arrays(terms, lhs, rhs)
        else {
            continue;
        };
        if chain_extensions::chains_are_validated_permutation(
            terms,
            left_array,
            right_array,
            literals,
            &mut pairs,
        ) {
            return true;
        }
    }
    false
}

/// The denotation of `eval(C, x)`: either a value term lifted straight out of
/// the chain, or the `select` of the chain's base array at `x`.
///
/// The `select` case is kept symbolic because the checker holds an immutable
/// `TermStore` and cannot intern `(select base x)` to compare `TermId`s.
enum ChainValue {
    Value(TermId),
    SelectOfBase { array: TermId, index: TermId },
}

impl ChainValue {
    /// Whether `term` denotes this evaluation result.
    fn denotes(&self, terms: &TermStore, term: TermId) -> bool {
        match *self {
            Self::Value(v) => v == term,
            Self::SelectOfBase { array, index } => is_select_of(terms, term, array, index),
        }
    }
}

/// Read-over-write evaluation of `term` at `index`, consuming one positive
/// `(= index i)` clause literal per skipped `store`. Returns `None` when the
/// chain cannot be evaluated with the disequalities the clause actually
/// carries — the fail-closed case.
fn eval_chain_at(
    terms: &TermStore,
    term: TermId,
    index: TermId,
    eqs: &PositiveEqPairs,
) -> Option<ChainValue> {
    let chain = parse_store_chain(terms, term)?;
    let Sort::Array(array_sort) = terms.sort(term) else {
        return None;
    };
    if terms.sort(index) != &array_sort.index_sort {
        return None;
    }
    for &(entry_index, entry_value) in &chain.entries {
        if entry_index == index {
            return Some(ChainValue::Value(entry_value));
        }
        // Skipping this store needs `index != entry_index`. Either the clause
        // itself carries the `(= index entry_index)` literal we get to assume
        // false, or the two indices are interpreted constants with different
        // values and the disequality is GROUND — the same side condition
        // `TermStore::mk_select` already uses to perform this exact fold, so
        // the checker is only re-deriving a step the producer took.
        if !eqs.contains(index, entry_index)
            && !distinct_interpreted_indices(terms, index, entry_index)
        {
            return None;
        }
    }
    if let Some(value) = terms.get_const_array(chain.base) {
        let Sort::Array(base_sort) = terms.sort(chain.base) else {
            return None;
        };
        return (terms.sort(value) == &base_sort.element_sort).then_some(ChainValue::Value(value));
    }
    Some(ChainValue::SelectOfBase {
        array: chain.base,
        index,
    })
}

/// Whether `target` is either the checked reduction of `array[index]` or the
/// exact, well-sorted root read itself.  The flag is true only when a
/// non-empty store chain was reduced; an array-equality ROW lemma must reduce
/// at least one of its two sides rather than smuggling plain congruence through
/// the array schema.
fn chain_or_root_select_denotes(
    terms: &TermStore,
    array: TermId,
    index: TermId,
    target: TermId,
    eqs: &PositiveEqPairs,
) -> Option<bool> {
    let chain = parse_store_chain(terms, array)?;
    if eval_chain_at(terms, array, index, eqs).is_some_and(|value| value.denotes(terms, target)) {
        return Some(!chain.entries.is_empty());
    }

    let (target_array, target_index) = well_sorted_select_parts(terms, target)?;
    (target_array == array && target_index == index).then_some(false)
}

/// See [`validate_array_row_chain`] for the schema and its soundness argument.
fn matches_row_chain(terms: &TermStore, literals: &[TermId]) -> bool {
    let eqs = PositiveEqPairs::collect(terms, literals);
    matches_row_chain_eval(terms, literals, &eqs)
        || matches_row_chain_under_array_eq(terms, literals, &eqs)
        || matches_equal_stores_force_base_alias(terms, literals)
        || exact_array_read_congruence_terms(terms, literals).is_some()
        || matches_exact_const_array_read_under_eq(terms, literals)
        || matches_exact_store_congruence(terms, literals)
        || matches_exact_store_idempotence_under_eq(terms, literals)
        || matches_exact_guarded_matching_outer_store_read(terms, literals)
        || chain_extensions::matches_extension_subschema(terms, literals)
}

/// Sub-schema (D): exact, two-literal select congruence.
fn exact_array_read_congruence_terms(
    terms: &TermStore,
    literals: &[TermId],
) -> Option<ArrayReadCongruenceTerms> {
    if literals.len() != 2 {
        return None;
    }

    for (premise_position, &array_eq_lit) in literals.iter().enumerate() {
        let Some((left, right)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        let Sort::Array(array_sort) = terms.sort(left) else {
            continue;
        };
        if terms.sort(right) != terms.sort(left) {
            continue;
        }
        let conclusion = literals[1 - premise_position];
        let Some((lhs, rhs)) = equality_sides(terms, conclusion) else {
            continue;
        };
        if terms.sort(lhs) != &array_sort.element_sort || terms.sort(rhs) != terms.sort(lhs) {
            continue;
        }
        for (left_read, right_read) in [(lhs, rhs), (rhs, lhs)] {
            let (Some((left_root, left_index)), Some((right_root, right_index))) = (
                well_sorted_select_parts(terms, left_read),
                well_sorted_select_parts(terms, right_read),
            ) else {
                continue;
            };
            if left_root != left
                || right_root != right
                || left_index != right_index
                || terms.sort(left_index) != &array_sort.index_sort
            {
                continue;
            }
            let eq_term = match terms.get(array_eq_lit) {
                TermData::Not(inner) => *inner,
                _ => continue,
            };
            return Some(ArrayReadCongruenceTerms {
                conclusion,
                array_eq_lit,
                eq_term,
                left,
                right,
                left_read,
                right_read,
                read_index: left_index,
            });
        }
    }
    None
}

/// Sub-schema (E): exact read of a root equated to a const-array.
fn matches_exact_const_array_read_under_eq(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 2 {
        return false;
    }

    for (premise_position, &array_eq_lit) in literals.iter().enumerate() {
        let Some((lhs, rhs)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        for (root, constant_array) in [(lhs, rhs), (rhs, lhs)] {
            // Exactly one side supplies the const-array axiom. Keeping the
            // root non-constant makes this shape disjoint and auditable.
            let Some(fill) = terms.get_const_array(constant_array) else {
                continue;
            };
            if terms.get_const_array(root).is_some()
                || terms.sort(root) != terms.sort(constant_array)
            {
                continue;
            }
            let Sort::Array(array_sort) = terms.sort(root) else {
                continue;
            };
            if terms.sort(fill) != &array_sort.element_sort {
                continue;
            }
            let conclusion = literals[1 - premise_position];
            let Some((conclusion_lhs, conclusion_rhs)) = equality_sides(terms, conclusion) else {
                continue;
            };
            for (read, value) in [
                (conclusion_lhs, conclusion_rhs),
                (conclusion_rhs, conclusion_lhs),
            ] {
                let Some((read_root, read_index)) = well_sorted_select_parts(terms, read) else {
                    continue;
                };
                if read_root == root
                    && value == fill
                    && terms.sort(read_index) == &array_sort.index_sort
                    && terms.sort(value) == &array_sort.element_sort
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Sub-schema (F): exact, two-literal congruence of one `store(_, i, v)`.
fn matches_exact_store_congruence(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 2 {
        return false;
    }

    for (premise_position, &array_eq_lit) in literals.iter().enumerate() {
        let Some((left, right)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        if !matches!(terms.sort(left), Sort::Array(_)) || terms.sort(right) != terms.sort(left) {
            continue;
        }
        let conclusion = literals[1 - premise_position];
        let Some((lhs, rhs)) = equality_sides(terms, conclusion) else {
            continue;
        };
        if terms.sort(lhs) != terms.sort(left) || terms.sort(rhs) != terms.sort(lhs) {
            continue;
        }
        for (left_store, right_store) in [(lhs, rhs), (rhs, lhs)] {
            let (
                Some((left_root, left_index, left_value)),
                Some((right_root, right_index, right_value)),
            ) = (
                well_sorted_store_parts(terms, left_store),
                well_sorted_store_parts(terms, right_store),
            )
            else {
                continue;
            };
            if left_root == left
                && right_root == right
                && left_index == right_index
                && left_value == right_value
            {
                return true;
            }
        }
    }
    false
}

/// Sub-schema (G): exact idempotent rewrite of a depth-one store under an
/// equality premise.
fn matches_exact_store_idempotence_under_eq(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 2 {
        return false;
    }

    for (premise_position, &array_eq_lit) in literals.iter().enumerate() {
        let Some((lhs, rhs)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        for (anchor, stored) in [(lhs, rhs), (rhs, lhs)] {
            let Some(chain) = parse_store_chain(terms, stored) else {
                continue;
            };
            if chain.entries.len() != 1 || terms.sort(anchor) != terms.sort(stored) {
                continue;
            }
            let (index, value) = chain.entries[0];
            let conclusion = literals[1 - premise_position];
            let Some((conclusion_lhs, conclusion_rhs)) = equality_sides(terms, conclusion) else {
                continue;
            };
            if terms.sort(conclusion_lhs) != terms.sort(stored)
                || terms.sort(conclusion_rhs) != terms.sort(stored)
            {
                continue;
            }
            for (stored_side, rewritten_side) in [
                (conclusion_lhs, conclusion_rhs),
                (conclusion_rhs, conclusion_lhs),
            ] {
                let Some((rewritten_root, rewritten_index, rewritten_value)) =
                    well_sorted_store_parts(terms, rewritten_side)
                else {
                    continue;
                };
                if stored_side == stored
                    && rewritten_root == anchor
                    && rewritten_index == index
                    && rewritten_value == value
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Sub-schema (H): an exact guarded read consequence of equality between two
/// stores with the same outer index and value.
fn matches_exact_guarded_matching_outer_store_read(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 3 {
        return false;
    }

    for (premise_position, &array_eq_lit) in literals.iter().enumerate() {
        let Some((left_store, right_store)) = negated_equality_sides(terms, array_eq_lit) else {
            continue;
        };
        let (
            Some((left_base, left_index, left_value)),
            Some((right_base, right_index, right_value)),
        ) = (
            well_sorted_store_parts(terms, left_store),
            well_sorted_store_parts(terms, right_store),
        )
        else {
            continue;
        };
        if terms.sort(left_store) != terms.sort(right_store)
            || left_index != right_index
            || left_value != right_value
        {
            continue;
        }

        for (conclusion_position, &conclusion) in literals.iter().enumerate() {
            if conclusion_position == premise_position {
                continue;
            }
            let Some((lhs, rhs)) = equality_sides(terms, conclusion) else {
                continue;
            };
            let (Some((lhs_root, lhs_index)), Some((rhs_root, rhs_index))) = (
                well_sorted_select_parts(terms, lhs),
                well_sorted_select_parts(terms, rhs),
            ) else {
                continue;
            };
            if lhs_index != rhs_index || terms.sort(lhs) != terms.sort(rhs) {
                continue;
            }

            let lhs_is_left = lhs_root == left_store || lhs_root == left_base;
            let lhs_is_right = lhs_root == right_store || lhs_root == right_base;
            let rhs_is_left = rhs_root == left_store || rhs_root == left_base;
            let rhs_is_right = rhs_root == right_store || rhs_root == right_base;
            if !((lhs_is_left && rhs_is_right) || (lhs_is_right && rhs_is_left)) {
                continue;
            }

            let Some((guard_position, &guard)) =
                literals.iter().enumerate().find(|(position, _)| {
                    *position != premise_position && *position != conclusion_position
                })
            else {
                continue;
            };
            debug_assert_ne!(guard_position, premise_position);
            debug_assert_ne!(guard_position, conclusion_position);
            if matches_equality_pair(terms, guard, left_index, lhs_index) {
                return true;
            }
        }
    }
    false
}

/// Sub-schema (C):
/// `¬(A=store(B,i,v)) ∨ ¬(A=store(B,j,v)) ∨ i=j ∨ B=A`.
fn matches_equal_stores_force_base_alias(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 4 {
        return false;
    }

    // Each candidate records (literal position, A, B, i, v). Try both
    // equality orientations; only the store side is decomposed.
    let mut candidates = Vec::new();
    for (position, &literal) in literals.iter().enumerate() {
        let Some((lhs, rhs)) = negated_equality_sides(terms, literal) else {
            continue;
        };
        for (anchor, stored) in [(lhs, rhs), (rhs, lhs)] {
            let Some(chain) = parse_store_chain(terms, stored) else {
                continue;
            };
            if chain.entries.len() != 1 || terms.sort(anchor) != terms.sort(stored) {
                continue;
            }
            let (index, value) = chain.entries[0];
            candidates.push((position, anchor, chain.base, index, value));
        }
    }

    for &(p1, anchor, base, i, value) in &candidates {
        for &(p2, other_anchor, other_base, j, other_value) in &candidates {
            if p1 >= p2
                || anchor != other_anchor
                || base != other_base
                || value != other_value
                || i == j
            {
                continue;
            }
            let remaining: Vec<usize> = (0..literals.len())
                .filter(|&position| position != p1 && position != p2)
                .collect();
            let [first, second] = remaining.as_slice() else {
                continue;
            };
            let first_lit = literals[*first];
            let second_lit = literals[*second];
            if (matches_equality_pair(terms, first_lit, i, j)
                && matches_equality_pair(terms, second_lit, base, anchor))
                || (matches_equality_pair(terms, second_lit, i, j)
                    && matches_equality_pair(terms, first_lit, base, anchor))
            {
                return true;
            }
        }
    }
    false
}

/// Sub-schema (A): `(= (select C x) eval(C, x))`.
fn matches_row_chain_eval(terms: &TermStore, literals: &[TermId], eqs: &PositiveEqPairs) -> bool {
    for &lit in literals {
        let Some((lhs, rhs)) = equality_sides(terms, lit) else {
            continue;
        };
        if terms.sort(lhs) != terms.sort(rhs) {
            continue;
        }
        for (select_side, value_side) in [(lhs, rhs), (rhs, lhs)] {
            let Some((array, read_index)) = well_sorted_select_parts(terms, select_side) else {
                continue;
            };
            // A depth-0 "chain" would make this the reflexivity of the very
            // literal being concluded, which proves nothing new; require at
            // least one store so the step is a genuine ROW instance.
            let Some(chain) = parse_store_chain(terms, array) else {
                continue;
            };
            if chain.entries.is_empty() {
                continue;
            }
            if eval_chain_at(terms, array, read_index, eqs)
                .is_some_and(|value| value.denotes(terms, value_side))
            {
                return true;
            }
        }
    }
    false
}

/// Sub-schema (B): `(not (= L R))` plus `(= eval(L, x) eval(R, x))`.
fn matches_row_chain_under_array_eq(
    terms: &TermStore,
    literals: &[TermId],
    eqs: &PositiveEqPairs,
) -> bool {
    // Array-equality premises are rare; conclusions carrying a top-level
    // select are the only candidates, so this stays close to linear in
    // practice and never enumerates unrelated index terms.
    let premises: Vec<(TermId, TermId)> = literals
        .iter()
        .filter_map(|&lit| negated_equality_sides(terms, lit))
        .filter(|&(l, r)| matches!(terms.sort(l), Sort::Array(_)) && terms.sort(l) == terms.sort(r))
        .collect();
    if premises.is_empty() {
        return false;
    }
    for &lit in literals {
        let Some((lhs, rhs)) = equality_sides(terms, lit) else {
            continue;
        };
        if terms.sort(lhs) != terms.sort(rhs) {
            continue;
        }
        // The witness index is read off the conclusion's own selects; the
        // checker never invents one.
        let mut candidates: Vec<TermId> = Vec::new();
        for side in [lhs, rhs] {
            if let Some((_, read_index)) = well_sorted_select_parts(terms, side) {
                if !candidates.contains(&read_index) {
                    candidates.push(read_index);
                }
            }
        }
        for &(left, right) in &premises {
            let Sort::Array(array_sort) = terms.sort(left) else {
                continue;
            };
            if terms.sort(lhs) != &array_sort.element_sort {
                continue;
            }
            for &read_index in &candidates {
                if terms.sort(read_index) != &array_sort.index_sort {
                    continue;
                }
                for (left_target, right_target) in [(lhs, rhs), (rhs, lhs)] {
                    let (Some(left_reduced), Some(right_reduced)) = (
                        chain_or_root_select_denotes(terms, left, read_index, left_target, eqs),
                        chain_or_root_select_denotes(terms, right, read_index, right_target, eqs),
                    ) else {
                        continue;
                    };
                    if left_reduced || right_reduced {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// `(select array index)` with a signature that agrees with `array`'s sort.
fn well_sorted_select_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let (array, index) = select_parts(terms, term)?;
    let Sort::Array(array_sort) = terms.sort(array) else {
        return None;
    };
    if terms.sort(index) != &array_sort.index_sort || terms.sort(term) != &array_sort.element_sort {
        return None;
    }
    Some((array, index))
}

/// `(store array index value)` with a complete signature agreeing with the
/// base array sort. `TermStore` permits raw applications, so strict checking
/// must re-establish every sort relation here.
fn well_sorted_store_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermData::App(Symbol::Named(symbol), args) = terms.get(term) else {
        return None;
    };
    if symbol != "store" || args.len() != 3 {
        return None;
    }
    let (array, index, value) = (args[0], args[1], args[2]);
    let Sort::Array(array_sort) = terms.sort(array) else {
        return None;
    };
    if terms.sort(term) != terms.sort(array)
        || terms.sort(index) != &array_sort.index_sort
        || terms.sort(value) != &array_sort.element_sort
    {
        return None;
    }
    Some((array, index, value))
}

fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    if !matches!(terms.sort(term), Sort::Bool) {
        return None;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(sym), args) if sym == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn negated_equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    if !matches!(terms.sort(term), Sort::Bool) {
        return None;
    }
    match terms.get(term) {
        TermData::Not(inner) => equality_sides(terms, *inner),
        _ => None,
    }
}

fn matches_equality_pair(terms: &TermStore, term: TermId, lhs: TermId, rhs: TermId) -> bool {
    equality_sides(terms, term)
        .is_some_and(|(a, b)| (a == lhs && b == rhs) || (a == rhs && b == lhs))
}

fn matches_not_equality_pair(terms: &TermStore, term: TermId, lhs: TermId, rhs: TermId) -> bool {
    negated_equality_sides(terms, term)
        .is_some_and(|(a, b)| (a == lhs && b == rhs) || (a == rhs && b == lhs))
}

/// Exact two-literal schema used by Seq model completion:
/// `¬(store(A,i,v)=store(C,i,v)) ∨ default(A)=fill`, where `C` is a bounded,
/// well-sorted `store*` chain rooted at `const-array(fill)`. Only the matching
/// outer stores are peeled here; `A` remains the exact root named by the
/// conclusion.
///
/// # Carrier side condition
///
/// Like the folded form, this schema is CARRIER-SENSITIVE, and for the same
/// reason: the premise pins `A` only OFF the stored indices, so concluding its
/// default requires that a finite chain cannot reach the whole carrier.
/// Measured against Z3 5.0.0 with its builtin `default`:
///
/// ```text
/// Int  index: (= (store A 0 1) (store ((as const (Array Int Int)) 7) 0 1))
///             (not (= (default A) 7))                            => unsat  VALID
/// Bool index: (= (store A true 1) (store ((as const (Array Bool Int)) 7) true 1))
///             (not (= (default A) 7))                            => sat    INVALID
/// ```
///
/// So it is gated on [`sort_provably_infinite`] exactly as the folded form is.
/// An earlier draft of this work DELETED this schema outright on the belief it
/// had no sound instance at any depth; that was wrong — the counterexample
/// behind it used a deliberately weak local axiomatization of `default` rather
/// than the real one, so it re-proved that AY's axioms are incomplete instead of
/// exhibiting a false clause.
fn matches_default_const_under_equal_matched_stores(
    terms: &TermStore,
    literals: &[TermId],
) -> bool {
    if literals.len() != 2 {
        return false;
    }

    // Carrier gate: refuse unless no finite store chain can reach the whole
    // index carrier. See the doc comment for the oracle measurements.
    let carrier_ok = literals.iter().any(|&lit| {
        equality_sides(terms, lit)
            .or_else(|| negated_equality_sides(terms, lit))
            .into_iter()
            .flat_map(|(l, r)| [l, r])
            .any(|t| match terms.sort(t) {
                Sort::Array(a) => sort_provably_infinite(&a.index_sort),
                _ => false,
            })
    });
    if !carrier_ok {
        return false;
    }

    for premise_position in 0..2 {
        let Some((premise_lhs, premise_rhs)) =
            negated_equality_sides(terms, literals[premise_position])
        else {
            continue;
        };
        let (
            Some((left_base, left_index, left_value)),
            Some((right_base, right_index, right_value)),
        ) = (
            well_sorted_store_parts(terms, premise_lhs),
            well_sorted_store_parts(terms, premise_rhs),
        )
        else {
            continue;
        };
        if terms.sort(premise_lhs) != terms.sort(premise_rhs) {
            continue;
        }
        if left_index != right_index || left_value != right_value {
            continue;
        }

        for (array, folded_constant_base) in [(left_base, right_base), (right_base, left_base)] {
            let Some(fill) = const_array_default_fill(terms, folded_constant_base) else {
                continue;
            };
            if array == folded_constant_base
                || terms.sort(array) != terms.sort(folded_constant_base)
            {
                continue;
            }
            let Sort::Array(array_sort) = terms.sort(array) else {
                continue;
            };
            if terms.sort(fill) != &array_sort.element_sort {
                continue;
            }
            let Some((conclusion_lhs, conclusion_rhs)) =
                equality_sides(terms, literals[1 - premise_position])
            else {
                continue;
            };
            for (default_term, value) in [
                (conclusion_lhs, conclusion_rhs),
                (conclusion_rhs, conclusion_lhs),
            ] {
                if terms.get_array_default(default_term) == Some(array)
                    && value == fill
                    && terms.sort(default_term) == &array_sort.element_sort
                    && terms.sort(value) == &array_sort.element_sort
                {
                    return true;
                }
            }
        }
    }
    false
}
