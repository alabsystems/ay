// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! READ-OVER-WRITE axiom instances, minted as ordinary positive equalities so
//! a [`crate::definition_bridge`] can cite them as hypotheses.
//!
//! # Why this exists
//!
//! the development design notes measured the
//! residual the definitional bridge leaves: 97 premiseless, argument-free
//! `trust` steps whose clause is a unit `(= a b)`, none congruence-reachable.
//! **58 of them are an authored assertion after an ARRAY fold, and those split
//! cleanly in two: 20 need READ-OVER-WRITE at an equal index and 38 need
//! STORE-OVER-STORE. No step needs both.** This module closes the first 20; the
//! second class needs an array EQUALITY no validator in this crate accepts, and
//! is left byte-identical (see §7 of that doc).
//!
//! The reason congruence cannot reach the read-over-write class:
//!
//! ```text
//! authored   (assert (= a_260 (store a_258 i0 e_259)))
//! authored   (assert (= e_261 (select a_260 i0)))
//! asserted   (= e_261 e_259)
//! ```
//!
//! `mk_select` folds `(select (store a i v) i)` to `v` while `VariableSubstitution`
//! is inlining, so the term the congruence closure would have to merge on
//! **does not exist in the term store at all**. There is no node, so there is
//! no edge, so there is no path.
//!
//! # What this module does
//!
//! It re-creates exactly that missing node, as a RAW application (`mk_select`
//! would fold it straight back), pairs it with the value in a RAW equality, and
//! offers the pair as a hypothesis. The congruence closure then does the rest
//! with no array knowledge whatsoever: `a_260 ≡ (store a_258 i0 e_259)` is an
//! authored hypothesis, congruence on `select` gives
//! `(select a_260 i0) ≡ (select (store a_258 i0 e_259) i0)`, and this axiom
//! gives `(select (store a_258 i0 e_259) i0) ≡ e_259`.
//!
//! # Authority — and why NO index distinctness is ever assumed
//!
//! The minted equality is `(= (select (store a i v) i) v)` with the store index
//! and the read index the **same `TermId`**. That is the ROW1 axiom at an
//! index that is syntactically identical on both sides: a ground first-order
//! VALIDITY of the theory of arrays, true under every interpretation, with no
//! side condition of any kind. In particular this module never mints a
//! read-over-write at a DIFFERENT index — the instance that is only sound when
//! a disequality is available — and it cannot: the read index it builds is the
//! store's own index term.
//!
//! Nothing here is asserted even so. Every minted equality is handed to the
//! checker's OWN recognizer, [`crate::recognize_array_select_store`], and kept
//! only if that recognizer answers `Some(true)` — i.e. only if the unit clause
//! `(cl eq)` is one the strict validator
//! (`checker::array_axiom::validate_array_select_store`) will re-derive from
//! the clause alone. Producer and checker therefore cannot drift: the producer
//! asks the checker.
//!
//! The leaf a caller emits for a cited instance is
//! `TheoryLemma { kind: ArraySelectStore { index_eq: true }, clause: [eq] }`,
//! which the mandatory strict gate re-validates from scratch, with no premise,
//! no payload and no problem context.

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

/// Largest number of sub-term nodes the store walk will visit before it gives
/// up. An adversarial proof must not be able to make this unbounded.
pub(crate) const MAX_AXIOM_SCAN_NODES: usize = 8192;

/// Largest number of axiom instances one call will mint. Each cited instance
/// becomes an `ArraySelectStore` leaf, and that kind takes the checker's
/// `General` semantic precharge, so the count is bounded on purpose.
pub(crate) const MAX_ROW1_AXIOM_INSTANCES: usize = 256;

/// The parts of a well-sorted `(store a i v)` application.
///
/// Every sort relation of the application is re-derived here rather than
/// assumed: `TermStore` permits raw applications, so a proof-boundary consumer
/// cannot take the frontend's word for the signature. This mirrors the
/// checker's own `select_store_parts` guard.
fn well_sorted_store_parts(
    terms: &TermStore,
    term: TermId,
) -> Option<(TermId, TermId, TermId, Sort)> {
    let TermData::App(symbol, args) = terms.get(term) else {
        return None;
    };
    if !matches!(symbol, Symbol::Named(name) if name == "store") || args.len() != 3 {
        return None;
    }
    let (array, index, value) = (args[0], args[1], args[2]);
    let Sort::Array(array_sort) = terms.sort(term) else {
        return None;
    };
    let element_sort = array_sort.element_sort.clone();
    let index_sort = array_sort.index_sort.clone();
    if terms.sort(array) != terms.sort(term)
        || terms.sort(index) != &index_sort
        || terms.sort(value) != &element_sort
    {
        return None;
    }
    Some((array, index, value, element_sort))
}

/// Every `store` application reachable from `roots` through applications, in a
/// deterministic first-seen order.
///
/// Iterative on purpose: the measured QF_AX population carries `store` chains
/// a dozen deep and the recursion depth would otherwise be the proof author's
/// choice.
fn reachable_store_terms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut stores: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_AXIOM_SCAN_NODES {
            return stores;
        }
        match terms.get(term) {
            TermData::App(symbol, args) => {
                if matches!(symbol, Symbol::Named(name) if name == "store") && args.len() == 3 {
                    stores.push(term);
                }
                let args = args.clone();
                for arg in args.into_iter().rev() {
                    stack.push(arg);
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            _ => {}
        }
    }
    stores
}

/// Mint the ROW1 axiom instance `(= (select (store a i v) i) v)` for one
/// `store` term, or `None` when the term is not a well-sorted store or the
/// checker's own recognizer declines the result.
///
/// Both applications are RAW (`mk_app`): `mk_select` folds this exact select
/// back to `v` and `mk_eq` would then fold `(= v v)` to `true`, so the node the
/// congruence closure needs could not otherwise exist. Every build is decoded
/// back and checked against what it was built for, so a future builder change
/// fails closed here rather than silently producing a different term.
#[must_use]
pub fn mint_row1_axiom(terms: &mut TermStore, store_term: TermId) -> Option<TermId> {
    let (_array, index, value, element_sort) = well_sorted_store_parts(terms, store_term)?;
    let select = terms.mk_app(
        Symbol::named("select"),
        [store_term, index],
        element_sort.clone(),
    );
    match terms.get(select) {
        TermData::App(Symbol::Named(name), args)
            if name == "select" && args.as_slice() == [store_term, index] => {}
        _ => return None,
    }
    if terms.sort(select) != &element_sort {
        return None;
    }
    // A select that is somehow already its own value would make the equality
    // reflexive, which `mk_not`/`parse_clause` cannot carry as a hypothesis.
    if select == value {
        return None;
    }
    let equality = terms.mk_app(Symbol::named("="), [select, value], Sort::Bool);
    match terms.get(equality) {
        TermData::App(Symbol::Named(name), args)
            if name == "=" && args.as_slice() == [select, value] => {}
        _ => return None,
    }
    // THE authority check: the checker's own recognizer decides whether the
    // unit clause `(cl equality)` is a read-over-write instance its strict
    // validator will accept, and `Some(true)` is the index-EQUAL schema.
    // Anything else — including `Some(false)`, the index-DISEQUALITY schema
    // that would need a disequality this module never has — is declined.
    (crate::recognize_array_select_store(terms, &[equality]) == Some(true)).then_some(equality)
}

/// Every ROW1 axiom instance reachable from `roots`, deduplicated and capped.
///
/// The result is offered to [`crate::plan_definitional_bridge`] as extra
/// candidate hypotheses. The bridge MINIMISES its clause to the hypotheses the
/// explanation actually cites, so an instance nothing needs costs a forest node
/// and nothing else.
#[must_use]
pub fn plan_row1_axiom_instances(terms: &mut TermStore, roots: &[TermId]) -> Vec<TermId> {
    let stores = reachable_store_terms(terms, roots);
    let mut minted: Vec<TermId> = Vec::new();
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    for store_term in stores {
        if minted.len() >= MAX_ROW1_AXIOM_INSTANCES {
            break;
        }
        let Some(equality) = mint_row1_axiom(terms, store_term) else {
            continue;
        };
        if seen.insert(equality) {
            minted.push(equality);
        }
    }
    minted
}

#[cfg(test)]
#[path = "array_row_axiom_model_tests.rs"]
pub(crate) mod model;

#[cfg(test)]
#[path = "array_row_axiom_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "array_row_axiom_negative_tests.rs"]
mod negative_tests;

#[cfg(test)]
#[path = "array_closer_head_negative_tests.rs"]
mod closer_head_negative_tests;

#[cfg(test)]
#[path = "array_row_axiom_guard_negative_tests.rs"]
mod guard_negative_tests;
