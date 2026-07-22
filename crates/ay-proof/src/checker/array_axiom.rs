// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for `TheoryLemmaKind::ArraySelectStore` and
//! `TheoryLemmaKind::ArrayExtensionality` proof steps.
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
//! - `ArrayExtensionality` is fail-closed in strict mode unless a future
//!   checker can verify that the select index is a real extensionality/diff
//!   witness for the array pair. A syntactic `select` witness is not enough.
//!
//! Full semantic validation (#8073) is still future work. Strict mode accepts
//! the exact read-over-write schemas and rejects unverified extensionality
//! witnesses instead of accepting them by shape alone.

use ay_core::{ProofId, Sort, TermData, TermId, TermStore};

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
/// Extensionality is intentionally NOT recognized here: strict mode cannot yet
/// validate it (#8073), so those lemmas must stay `Generic` rather than be
/// labelled a checkable kind they would fail. Schema logic lives ONLY in this
/// module.
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

/// Validate an `ArrayExtensionality` lemma in strict mode.
pub(crate) fn validate_array_extensionality(
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
    reject_non_bool_literals(terms, step_id, clause, "array extensionality")?;

    let literals = flatten_clause_literals(terms, clause);
    let reason = if matches_extensionality(terms, &literals) {
        "array extensionality schema has no checked diff witness; strict mode \
         rejects it until semantic witness validation is available"
    } else {
        "array extensionality clause does not match the exact \
         `(= a b) ∨ ¬(= (select a k) (select b k))` schema"
    };
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: reason.to_string(),
    })
}

// ---------- helpers ----------

fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(sym, args) = terms.get(clause[0]) {
            if sym.name() == "or" {
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

fn matches_extensionality(terms: &TermStore, literals: &[TermId]) -> bool {
    if literals.len() != 2 {
        return false;
    }
    for &array_eq_lit in literals {
        let Some((array_a, array_b)) = equality_sides(terms, array_eq_lit) else {
            continue;
        };
        if !matches!(terms.sort(array_a), Sort::Array(_))
            || !matches!(terms.sort(array_b), Sort::Array(_))
        {
            continue;
        }
        let Some(&witness_lit) = literals.iter().find(|&&lit| lit != array_eq_lit) else {
            continue;
        };
        let Some((sel_a, sel_b)) = negated_equality_sides(terms, witness_lit) else {
            continue;
        };
        if selects_match_pair_at_same_index(terms, sel_a, sel_b, array_a, array_b) {
            return true;
        }
    }
    false
}

fn row1_eq_parts(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, TermId, TermId, TermId)> {
    let (select_term, value_term) = if let Some(parts) = select_store_parts(terms, lhs) {
        (parts, rhs)
    } else {
        let parts = select_store_parts(terms, rhs)?;
        (parts, lhs)
    };
    let (base_array, store_index, store_value, select_index) = select_term;
    if store_value == value_term {
        Some((base_array, store_index, store_value, select_index))
    } else {
        None
    }
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
    if select_sym.name() != "select" || select_args.len() != 2 {
        return None;
    }
    let TermData::App(store_sym, store_args) = terms.get(select_args[0]) else {
        return None;
    };
    if store_sym.name() != "store" || store_args.len() != 3 {
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
        TermData::App(sym, args) if sym.name() == "select"
            && args.len() == 2
            && args[0] == array
            && args[1] == index
            && terms.sort(index) == &array_sort.index_sort
            && terms.sort(term) == &array_sort.element_sort
    )
}

fn selects_match_pair_at_same_index(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
    array_a: TermId,
    array_b: TermId,
) -> bool {
    let Some((lhs_array, lhs_index)) = select_parts(terms, lhs) else {
        return false;
    };
    let Some((rhs_array, rhs_index)) = select_parts(terms, rhs) else {
        return false;
    };
    lhs_index == rhs_index
        && ((lhs_array == array_a && rhs_array == array_b)
            || (lhs_array == array_b && rhs_array == array_a))
}

fn select_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
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
