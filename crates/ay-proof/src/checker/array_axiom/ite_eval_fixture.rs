// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fixtures shared by the three sub-schema (K) test files.
//!
//! Two properties of this file are load-bearing and are asserted, not assumed:
//!
//! 1. **Every clause term is a RAW application.** `mk_select` folds
//!    read-over-write and read-over-const-array, and `mk_eq` folds `(= x true)`
//!    to `x` and distributes over an `ite` — so the very nodes this schema is
//!    about cannot be built with the ordinary builders.
//!    `the_ordinary_builders_fold_the_nodes_this_schema_needs` pins both folds.
//! 2. **The VALUE side is built by the real producer.** [`producer_value`] is
//!    `ay_core`'s own `expand_select_over_store_inner` restricted to the
//!    symbolic case, calling the REAL `mk_eq_coerce`/`mk_ite`/`mk_select`. It
//!    shares no code with the validator, so the sweep asks "does the checker
//!    accept every chain the producer can emit", not "does the checker accept
//!    what the checker builds".

use ay_core::{ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

use crate::quality::check_proof_strict;

pub(super) fn index_sort() -> Sort {
    Sort::Uninterpreted("Index".to_string())
}

pub(super) fn element_sort() -> Sort {
    Sort::Uninterpreted("Element".to_string())
}

pub(super) fn array_sort(element: Sort) -> Sort {
    Sort::Array(Box::new(ArraySort::new(index_sort(), element)))
}

/// A RAW `(store a i v)`: `mk_store` collapses store-over-store.
pub(super) fn store(terms: &mut TermStore, base: TermId, at: TermId, value: TermId) -> TermId {
    let sort = terms.sort(base).clone();
    terms.mk_app(Symbol::named("store"), vec![base, at, value], sort)
}

/// A RAW `(select a i)`: `mk_select` folds every read this schema is about.
pub(super) fn select(terms: &mut TermStore, base: TermId, at: TermId) -> TermId {
    let Sort::Array(array) = terms.sort(base).clone() else {
        panic!("select needs an array-sorted base");
    };
    terms.mk_app(
        Symbol::named("select"),
        vec![base, at],
        array.element_sort.clone(),
    )
}

/// A RAW `(= a b)`: `mk_eq` folds Boolean equalities and distributes over `ite`.
pub(super) fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// A RAW `(or a b)`: `mk_or` sorts and dedups, and the packed corpus clause has
/// a fixed literal order the printer test pins.
pub(super) fn or(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("or"), vec![lhs, rhs], Sort::Bool)
}

/// The symbolic evaluation `ay_core::TermStore::expand_select_over_store_inner`
/// produces for `chain` at `index`, built with the REAL builders so every fold
/// the producer applies is applied here too.
pub(super) fn producer_value(terms: &mut TermStore, chain: TermId, index: TermId) -> TermId {
    let parts = match terms.get(chain) {
        ay_core::TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    };
    let Some((inner, at, value)) = parts else {
        return terms.mk_select(chain, index);
    };
    if at == index {
        return value;
    }
    let condition = terms.mk_eq_coerce(at, index);
    let otherwise = producer_value(terms, inner, index);
    terms.mk_ite(condition, value, otherwise)
}

/// How the two literals of a (K) clause may be spelled.
#[derive(Clone, Copy)]
pub(super) struct Spelling {
    /// Swap the premise's two array sides.
    pub(super) premise_flipped: bool,
    /// Put the value side first in the conclusion.
    pub(super) conclusion_flipped: bool,
    /// Put the conclusion literal first in the clause.
    pub(super) conclusion_first: bool,
    /// Pack the two literals into one `(cl (or .. ..))` literal.
    pub(super) packed: bool,
}

impl Spelling {
    pub(super) fn plain() -> Self {
        Self {
            premise_flipped: false,
            conclusion_flipped: false,
            conclusion_first: false,
            packed: false,
        }
    }

    /// Every spelling of the same clause: 2 x 2 x 2 x 2.
    pub(super) fn all() -> Vec<Self> {
        let mut out = Vec::new();
        for premise_flipped in [false, true] {
            for conclusion_flipped in [false, true] {
                for conclusion_first in [false, true] {
                    for packed in [false, true] {
                        out.push(Self {
                            premise_flipped,
                            conclusion_flipped,
                            conclusion_first,
                            packed,
                        });
                    }
                }
            }
        }
        out
    }
}

/// Assemble `(cl (not (= root chain)) (= (select root index) value))` in the
/// requested spelling, returning `(clause, literals)`.
pub(super) fn assemble(
    terms: &mut TermStore,
    root: TermId,
    chain: TermId,
    index: TermId,
    value: TermId,
    spelling: Spelling,
) -> (Vec<TermId>, Vec<TermId>) {
    let premise_eq = if spelling.premise_flipped {
        eq(terms, chain, root)
    } else {
        eq(terms, root, chain)
    };
    let premise = terms.mk_not(premise_eq);
    let read = select(terms, root, index);
    let conclusion = if spelling.conclusion_flipped {
        eq(terms, value, read)
    } else {
        eq(terms, read, value)
    };
    let literals = if spelling.conclusion_first {
        vec![conclusion, premise]
    } else {
        vec![premise, conclusion]
    };
    let clause = if spelling.packed {
        vec![or(terms, literals[0], literals[1])]
    } else {
        literals.clone()
    };
    (clause, literals)
}

/// The UNTOUCHED strict checker, on the clause closed into a self-contained
/// refutation: the lemma, the assumed negation of each of its literals, and the
/// resolution to the empty clause.
pub(super) fn strict_checks(terms: &mut TermStore, clause: &[TermId]) -> bool {
    // `mk_not` De Morgans `(not (or a b))` into `(and ..)`, which is not the
    // literal the resolution consumes — the packed clause needs the raw one.
    let negations: Vec<TermId> = clause.iter().map(|&lit| terms.mk_not_raw(lit)).collect();
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: clause.to_vec(),
        farkas: None,
        kind: ay_core::TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    let mut premises = vec![ProofId(0)];
    for (position, negated) in negations.into_iter().enumerate() {
        proof.steps.push(ProofStep::Assume(negated));
        premises.push(ProofId(u32::try_from(position + 1).expect("small fixture")));
    }
    proof.steps.push(ProofStep::Step {
        rule: ay_core::AletheRule::Resolution,
        clause: Vec::new(),
        premises,
        args: Vec::new(),
    });
    if let Err(error) = check_proof_strict(&proof, terms) {
        eprintln!("strict check refused the closed (K) refutation: {error:?}");
        return false;
    }
    true
}
