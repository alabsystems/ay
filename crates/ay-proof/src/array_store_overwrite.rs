// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! STORE-OVER-STORE axiom instances, minted as ordinary positive equalities so
//! a [`crate::definition_bridge`] can cite them as hypotheses.
//!
//! # Why this exists
//!
//! the development design notes §7 named the
//! residual its READ-OVER-WRITE lane leaves: premiseless, argument-free `trust`
//! steps whose clause is a unit `(= a b)` that reproduce an AUTHORED assertion
//! only after `mk_store` collapsed a same-index write pair while
//! `VariableSubstitution` was inlining.
//!
//! ```text
//! authored   (assert (= a_278 (store a_276 i3 e_277)))
//! authored   (assert (= a_280 (store a_278 i3 e_279)))
//! authored   (assert (= e_281 (select a_280 i0)))
//! asserted   (= e_281 (select (store <a_276's chain> i3 e_279) i0))
//! ```
//!
//! `mk_store` folds `store(store(a, i, u), i, v)` to `store(a, i, v)`, so the
//! node `store(store(a_276, i3, e_277), i3, e_279)` — the one the congruence
//! closure would have to merge on — **does not exist in the term store at
//! all**. There is no node, so there is no edge, so there is no path. This is
//! the same defect the read-over-write lane closed, one builder along.
//!
//! # What this module does
//!
//! It re-creates exactly that missing node, as a RAW application
//! (`mk_store` would fold it straight back), pairs it with the folded store in
//! a RAW equality, and offers the pair as a hypothesis. The congruence closure
//! then does the rest with no array knowledge whatsoever:
//! `a_278 ≡ (store a_276 i3 e_277)` is an authored hypothesis, congruence on
//! `store` gives
//! `(store a_278 i3 e_279) ≡ (store (store a_276 i3 e_277) i3 e_279)`, and this
//! axiom gives `(store (store a_276 i3 e_277) i3 e_279) ≡ (store a_276 i3 e_279)`.
//!
//! # Authority
//!
//! The minted equality is `(= (store (store B i u) i v) (store B i v))` with
//! ONE index term written by all three stores. That is a ground first-order
//! VALIDITY of the theory of arrays with extensionality — the two sides agree
//! at `i` (both `v`) and at every other index (both `select(B, ·)`) — with no
//! side condition of any kind. In particular this module can never mint the
//! DIFFERENT-index instance, which is not valid at all: the index it writes
//! into the folded store is the outer store's own index term.
//!
//! Nothing here is asserted even so. Every minted equality is handed to the
//! checker's OWN recognizer, [`crate::recognize_array_theory_lemma`], and kept
//! only if that recognizer answers `ArrayRowChain` — i.e. only if the unit
//! clause `(cl eq)` is one the strict validator
//! (`checker::array_axiom::validate_array_row_chain`, sub-schema (J)) will
//! re-derive from the clause alone. Producer and checker cannot drift: the
//! producer asks the checker.
//!
//! The leaf a caller emits for a cited instance is
//! `TheoryLemma { kind: ArrayRowChain, clause: [eq] }`, which the mandatory
//! strict gate re-validates from scratch, with no premise, no payload and no
//! problem context.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind};

/// Largest number of sub-term nodes the store walk will visit before it gives
/// up. An adversarial proof must not be able to make this unbounded.
const MAX_OVERWRITE_SCAN_NODES: usize = 8192;

/// Largest number of axiom instances one call will mint.
pub(crate) const MAX_STORE_OVERWRITE_INSTANCES: usize = 256;

/// Longest same-index DEFINITION chain the walk will follow. A chain of `n`
/// consecutive same-index authored writes needs `n - 1` instances to fold; the
/// measured population is 1-2 and the cap only bounds an adversarial input.
const MAX_OVERWRITE_CHAIN: usize = 64;

/// The parts of a well-sorted `(store a i v)` application.
///
/// Every sort relation of the application is re-derived here rather than
/// assumed: `TermStore` permits raw applications, so a proof-boundary consumer
/// cannot take the frontend's word for the signature. This mirrors the
/// checker's own `well_sorted_store_parts`.
fn well_sorted_store_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermData::App(symbol, args) = terms.get(term) else {
        return None;
    };
    if !matches!(symbol, Symbol::Named(name) if name == "store") || args.len() != 3 {
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

/// Every `store` application reachable from `roots` through applications, in a
/// deterministic first-seen order.
fn reachable_store_terms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut stores: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_OVERWRITE_SCAN_NODES {
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

/// `definiendum -> (store term, its base, its index)` for every candidate
/// equality that states an array term IS a well-sorted `store`.
///
/// This is a purely SYNTACTIC index over the candidate pool. It grants no
/// authority: an entry only decides which raw nodes are worth minting, and
/// every minted node is then re-checked by the checker's own recognizer.
fn store_definitions(
    terms: &TermStore,
    definitions: &[TermId],
) -> DetHashMap<TermId, (TermId, TermId, TermId)> {
    let mut index: DetHashMap<TermId, (TermId, TermId, TermId)> = DetHashMap::default();
    for &definition in definitions {
        let TermData::App(Symbol::Named(name), args) = terms.get(definition) else {
            continue;
        };
        if name != "=" || args.len() != 2 {
            continue;
        }
        let (left, right) = (args[0], args[1]);
        for (definiendum, definiens) in [(left, right), (right, left)] {
            // A store defining a store would let the walk below revisit the
            // same node under two spellings; the folded side of an instance is
            // never itself the depth-two overwrite, so this loses nothing.
            if well_sorted_store_parts(terms, definiendum).is_some() {
                continue;
            }
            let Some((base, at, _value)) = well_sorted_store_parts(terms, definiens) else {
                continue;
            };
            index.entry(definiendum).or_insert((definiens, base, at));
        }
    }
    index
}

/// Mint the STORE-OVER-STORE axiom instance
/// `(= (store (store B i u) i v) (store B i v))` for one inner store
/// `(store B i u)` and one written value `v`, or `None` when the operands are
/// not well-sorted or the checker's own recognizer declines the result.
///
/// Both `store` applications and the equality are RAW (`mk_app`): `mk_store`
/// folds this exact overwrite back to `(store B i v)` and `mk_eq` would then
/// fold `(= x x)` to `true`, so the node the congruence closure needs could not
/// otherwise exist. Every build is decoded back and checked against what it was
/// built for, so a future builder change fails closed here rather than silently
/// producing a different term.
#[must_use]
pub fn mint_store_overwrite_axiom(
    terms: &mut TermStore,
    shadowed: TermId,
    value: TermId,
) -> Option<TermId> {
    let (base, at, _shadowed_value) = well_sorted_store_parts(terms, shadowed)?;
    let array_sort = terms.sort(shadowed).clone();
    let Sort::Array(parts) = &array_sort else {
        return None;
    };
    if terms.sort(value) != &parts.element_sort {
        return None;
    }
    let overwrite = terms.mk_app(
        Symbol::named("store"),
        [shadowed, at, value],
        array_sort.clone(),
    );
    match terms.get(overwrite) {
        TermData::App(Symbol::Named(name), args)
            if name == "store" && args.as_slice() == [shadowed, at, value] => {}
        _ => return None,
    }
    let folded = terms.mk_app(
        Symbol::named("store"),
        [base, at, value],
        array_sort.clone(),
    );
    match terms.get(folded) {
        TermData::App(Symbol::Named(name), args)
            if name == "store" && args.as_slice() == [base, at, value] => {}
        _ => return None,
    }
    if terms.sort(overwrite) != &array_sort || terms.sort(folded) != &array_sort {
        return None;
    }
    // A reflexive equality cannot be carried as a hypothesis by `mk_not` /
    // `parse_clause`. The two sides differ structurally by construction (the
    // interned DAG is acyclic, so `(store B i u)` is never `B`), and this
    // re-checks it rather than relying on that.
    if overwrite == folded {
        return None;
    }
    let equality = terms.mk_app(Symbol::named("="), [overwrite, folded], Sort::Bool);
    match terms.get(equality) {
        TermData::App(Symbol::Named(name), args)
            if name == "=" && args.as_slice() == [overwrite, folded] => {}
        _ => return None,
    }
    // THE authority check: the checker's own recognizer decides whether the
    // unit clause `(cl equality)` is a schema its strict validator will accept,
    // and `ArrayRowChain` is the kind sub-schema (J) is validated under.
    (crate::recognize_array_theory_lemma(terms, &[equality])
        == Some(TheoryLemmaKind::ArrayRowChain))
    .then_some(equality)
}

/// Every STORE-OVER-STORE instance the folds reachable from `roots` can need,
/// deduplicated and capped.
///
/// `definitions` are the candidate pool equalities; only the ones that state an
/// array term IS a well-sorted `store` are read, and they are read purely as an
/// index of which raw nodes to mint.
///
/// For each reachable `(store A i v)` whose base `A` is DEFINED as a store at
/// the SAME index `i`, the walk follows that definition chain inward and mints
/// one instance per level. That is what makes a chain of three or more
/// consecutive same-index authored writes reachable: level `k`'s folded side is
/// level `k+1`'s overwrite side, so the closure composes them by transitivity.
///
/// The result is offered to [`crate::plan_definitional_bridge`] as extra
/// candidate hypotheses. The bridge MINIMISES its clause to the hypotheses the
/// explanation actually cites, so an instance nothing needs costs a forest node
/// and nothing else.
#[must_use]
pub fn plan_store_overwrite_instances(
    terms: &mut TermStore,
    definitions: &[TermId],
    roots: &[TermId],
) -> Vec<TermId> {
    let index = store_definitions(terms, definitions);
    let stores = reachable_store_terms(terms, roots);
    let mut minted: Vec<TermId> = Vec::new();
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    for store_term in stores {
        let Some((outer_base, at, value)) = well_sorted_store_parts(terms, store_term) else {
            continue;
        };
        let mut current = outer_base;
        for _ in 0..MAX_OVERWRITE_CHAIN {
            if minted.len() >= MAX_STORE_OVERWRITE_INSTANCES {
                return minted;
            }
            let Some(&(definiens, base, definition_index)) = index.get(&current) else {
                break;
            };
            // Only a same-index write is folded away by `mk_store`; a write at
            // a different index term is left in place, so there is nothing to
            // bridge and nothing is minted.
            if definition_index != at {
                break;
            }
            if let Some(equality) = mint_store_overwrite_axiom(terms, definiens, value) {
                if seen.insert(equality) {
                    minted.push(equality);
                }
            }
            current = base;
        }
    }
    minted
}

#[cfg(test)]
#[path = "array_store_overwrite_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "array_store_overwrite_negative_tests.rs"]
mod negative_tests;
