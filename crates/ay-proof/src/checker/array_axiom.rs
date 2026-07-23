// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for the array `TheoryLemmaKind`s:
//! `ArraySelectStore`, `ArrayStorePermutation`, `ArrayRowChain`, and
//! `ArrayExtensionality`.
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
/// This is the EXACT inverse of [`validate_array_select_store`]: the proof
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
/// Extensionality is intentionally NOT recognized here — see
/// [`recognize_array_select_store`] for why it needs its own emitter-side path.
#[must_use]
pub fn recognize_array_theory_lemma(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<TheoryLemmaKind> {
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
    if matches_store_permutation(terms, &literals) {
        return Some(TheoryLemmaKind::ArrayStorePermutation);
    }
    if matches_row_chain(terms, &literals) {
        return Some(TheoryLemmaKind::ArrayRowChain);
    }
    None
}

/// Validate an `ArrayStorePermutation` lemma in strict mode.
///
/// SCHEMA (all conditions are necessary; any failure REJECTS):
///
/// The clause must contain a POSITIVE literal `(= L R)` where
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
/// That contradicts the assumed-false conclusion literal, so the clause is a
/// theory tautology. Extra literals are harmless: a superset of a valid clause
/// is valid.
pub(crate) fn validate_array_store_permutation(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array axiom clause must be non-empty".to_string(),
        });
    }
    reject_non_bool_literals(terms, step_id, clause, "array store permutation")?;

    let literals = flatten_clause_literals(terms, clause);
    if matches_store_permutation(terms, &literals) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "array store-permutation clause does not match the exact schema: it needs a \
                 positive equality between two well-sorted store chains over one common base \
                 array that are a permutation of the same (index, value) pairs, with pairwise \
                 distinct index terms and one `(= i j)` literal for every unordered index pair"
            .to_string(),
    })
}

/// Validate an `ArrayRowChain` lemma in strict mode.
///
/// SCHEMA. Write `eval(C, x)` for the partial read-over-write evaluation of an
/// array term `C` at index `x`: walk `C`'s `store` chain OUTERMOST-FIRST; on an
/// entry `(i, v)` return `v` when `i` IS syntactically `x`, otherwise the
/// clause must carry a POSITIVE literal `(= x i)` (else `eval` FAILS and the
/// lemma is rejected) and the walk continues inward; when the chain is
/// exhausted the result is the term `(select base x)`. Every `store` node and
/// the final `select` must be well-sorted array operations.
///
/// The clause is accepted when either sub-schema holds:
///
/// (A) CHAIN EVALUATION. A POSITIVE literal `(= P Q)` where `P` is a well-
///     sorted `(select C x)` and `eval(C, x)` denotes exactly `Q` (or the
///     mirror image), and `sort(P) == sort(Q)`.
///
/// (B) UNDER AN ARRAY EQUALITY. A NEGATIVE literal `(not (= L R))` with
///     `sort(L) == sort(R) == Array(as)`, plus a POSITIVE literal `(= U W)`
///     with `sort(U) == sort(W) == as.element_sort`, and an index term `x` of
///     sort `as.index_sort` such that `eval(L, x)` denotes `U` and
///     `eval(R, x)` denotes `W` (or the mirror image). `x` is taken from a
///     top-level `(select _ x)` on either side of the conclusion literal; a
///     conclusion with no such select is REJECTED (the checker will not guess a
///     witness index).
///
/// SOUNDNESS. Assume the clause false. Then every `(= x i)` literal consumed by
/// `eval` is false, i.e. `x != i`, so each skipped `store` is transparent at
/// `x` by the read-over-write-negative axiom and each taken entry gives its
/// value by read-over-write-positive: `select(C, x) = eval(C, x)`.
/// For (A) that already contradicts the assumed-false conclusion.
/// For (B) the negative literal being false gives `L = R`, so by congruence
/// `select(L, x) = select(R, x)`, i.e. `U = W` — again contradicting the
/// assumed-false conclusion. Extra literals are harmless.
pub(crate) fn validate_array_row_chain(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array axiom clause must be non-empty".to_string(),
        });
    }
    reject_non_bool_literals(terms, step_id, clause, "array read-over-write chain")?;

    let literals = flatten_clause_literals(terms, clause);
    if matches_row_chain(terms, &literals) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "array read-over-write-chain clause does not match the exact schema: every \
                 store skipped while evaluating the chain at the read index must be justified \
                 by a positive `(= x i)` literal in the same clause, and the conclusion must be \
                 the evaluated equality (optionally under a `(not (= L R))` array-equality \
                 premise whose conclusion carries a top-level select at the read index)"
            .to_string(),
    })
}

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

/// Memoized, work-bounded structural matcher for folded witness reads.
///
/// Array terms are DAGs. In particular, proof-shape-preserving raw ITEs may
/// retain identical branches, so naive recursion would revisit one shared
/// child exponentially many times. The `(array, index, candidate, depth)` memo
/// makes matching linear in the reachable product DAG. The hard state ceiling
/// also makes an adversarial non-shared depth-64 tree fail closed instead of
/// consuming unbounded checker work.
struct FoldedReadMatcher<'terms, 'budget, 'counter> {
    terms: &'terms TermStore,
    memo: DetHashMap<(TermId, TermId, TermId, usize), bool>,
    budget: &'budget mut FoldedReadWorkBudget<'counter>,
}

impl<'terms, 'budget, 'counter> FoldedReadMatcher<'terms, 'budget, 'counter> {
    const FOLD_BOUND: usize = 64;

    fn new(terms: &'terms TermStore, budget: &'budget mut FoldedReadWorkBudget<'counter>) -> Self {
        Self {
            terms,
            memo: DetHashMap::default(),
            budget,
        }
    }

    /// Independently match the proof-shape-preserving fold of `select(array,
    /// index)` against an already-interned `candidate` term.
    fn matches(&mut self, array: TermId, index: TermId, candidate: TermId, depth: usize) -> bool {
        let key = (array, index, candidate, depth);
        if let Some(&cached) = self.memo.get(&key) {
            return cached;
        }
        if !self.budget.consume() {
            return false;
        }

        let result = self.matches_uncached(array, index, candidate, depth);
        self.memo.insert(key, result);
        result
    }

    fn matches_uncached(
        &mut self,
        array: TermId,
        index: TermId,
        candidate: TermId,
        depth: usize,
    ) -> bool {
        let Sort::Array(array_sort) = self.terms.sort(array) else {
            return false;
        };
        let index_sort = array_sort.index_sort.clone();
        let element_sort = array_sort.element_sort.clone();
        if self.terms.sort(index) != &index_sort || self.terms.sort(candidate) != &element_sort {
            return false;
        }
        if depth >= Self::FOLD_BOUND {
            return is_exact_well_sorted_select(self.terms, candidate, array, index);
        }

        if let Some(fill) = self.terms.get_const_array(array) {
            return self.terms.sort(fill) == &element_sort && candidate == fill;
        }

        match self.terms.get(array).clone() {
            TermData::App(Symbol::Named(symbol), args) if symbol == "store" && args.len() == 3 => {
                let (base, store_index, value) = (args[0], args[1], args[2]);
                if self.terms.sort(base) != self.terms.sort(array)
                    || self.terms.sort(store_index) != &index_sort
                    || self.terms.sort(value) != &element_sort
                {
                    return false;
                }
                if store_index == index {
                    return candidate == value;
                }
                if matches!(self.terms.get(index), TermData::Const(_))
                    && matches!(self.terms.get(store_index), TermData::Const(_))
                {
                    return self.matches(base, index, candidate, depth + 1);
                }

                let TermData::Ite(condition, then_value, else_value) =
                    self.terms.get(candidate).clone()
                else {
                    return false;
                };
                self.terms.sort(condition) == &Sort::Bool
                    && self.terms.sort(then_value) == &element_sort
                    && self.terms.sort(else_value) == &element_sort
                    && matches_equality_pair(self.terms, condition, index, store_index)
                    && then_value == value
                    && self.matches(base, index, else_value, depth + 1)
            }
            TermData::Ite(guard, then_array, else_array) => {
                if self.terms.sort(guard) != &Sort::Bool
                    || self.terms.sort(then_array) != self.terms.sort(array)
                    || self.terms.sort(else_array) != self.terms.sort(array)
                {
                    return false;
                }
                let TermData::Ite(candidate_guard, then_value, else_value) =
                    self.terms.get(candidate).clone()
                else {
                    return false;
                };
                candidate_guard == guard
                    && self.terms.sort(then_value) == &element_sort
                    && self.terms.sort(else_value) == &element_sort
                    && self.matches(then_array, index, then_value, depth + 1)
                    && self.matches(else_array, index, else_value, depth + 1)
            }
            _ => is_exact_well_sorted_select(self.terms, candidate, array, index),
        }
    }
}

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
    ///     ([`validate_ext_diff_intro`]).
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
    // two array-sorted `store` applications, plus one index-equality literal.
    if literals.len() < 2 {
        return false;
    }
    let mut pairs: Option<PositiveEqPairs> = None;
    for &lit in literals {
        let Some((lhs, rhs)) = equality_sides(terms, lit) else {
            continue;
        };
        if !matches!(terms.sort(lhs), Sort::Array(_)) || terms.sort(lhs) != terms.sort(rhs) {
            continue;
        }
        let (Some(left), Some(right)) =
            (parse_store_chain(terms, lhs), parse_store_chain(terms, rhs))
        else {
            continue;
        };
        // (1) same base array, (2) same chain length >= 2.
        if left.base != right.base || left.entries.len() != right.entries.len() {
            continue;
        }
        let n = left.entries.len();
        if n < 2 {
            continue;
        }
        // (3) pairwise distinct index TERMS on the left chain. Combined with
        // (4) this makes the right chain's indices distinct as well.
        let mut indices: Vec<TermId> = left.entries.iter().map(|&(i, _)| i).collect();
        let distinct: DetHashSet<TermId> = indices.iter().copied().collect();
        if distinct.len() != n {
            continue;
        }
        // (4) the two chains write the same multiset of (index, value) pairs.
        let mut left_pairs = left.entries.clone();
        let mut right_pairs = right.entries.clone();
        left_pairs.sort_unstable();
        right_pairs.sort_unstable();
        if left_pairs != right_pairs {
            continue;
        }
        // (5) one `(= i_p i_q)` literal per unordered index pair.
        let eqs = pairs.get_or_insert_with(|| PositiveEqPairs::collect(terms, literals));
        indices.sort_unstable();
        let all_pairs_present = indices
            .iter()
            .enumerate()
            .all(|(p, &ip)| indices[p + 1..].iter().all(|&iq| eqs.contains(ip, iq)));
        if all_pairs_present {
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
        // Skipping this store is only justified when the clause itself carries
        // the `(= index entry_index)` literal we get to assume false.
        if !eqs.contains(index, entry_index) {
            return None;
        }
    }
    Some(ChainValue::SelectOfBase {
        array: chain.base,
        index,
    })
}

/// See [`validate_array_row_chain`] for the schema and its soundness argument.
fn matches_row_chain(terms: &TermStore, literals: &[TermId]) -> bool {
    let eqs = PositiveEqPairs::collect(terms, literals);
    matches_row_chain_eval(terms, literals, &eqs)
        || matches_row_chain_under_array_eq(terms, literals, &eqs)
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
                let (Some(left_value), Some(right_value)) = (
                    eval_chain_at(terms, left, read_index, eqs),
                    eval_chain_at(terms, right, read_index, eqs),
                ) else {
                    continue;
                };
                if (left_value.denotes(terms, lhs) && right_value.denotes(terms, rhs))
                    || (left_value.denotes(terms, rhs) && right_value.denotes(terms, lhs))
                {
                    return true;
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

fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(sym), args) if sym == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn negated_equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
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
