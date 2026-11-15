// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Herbrand expansions of authored quantified roots (#qlra-nested-cegqi,
//! plan §4), shared by both nested-CEGQI publication routes.
//!
//! UNSAT (M3a, plan §4.1): the nested search (`cegqi::lra_nested::nested`)
//! works over its OWN terms: Skolemized roots, fresh counterexample
//! constants, and instance tuples written over those constants. A
//! certificate may mention none of them. The NNF-polarity walker therefore
//! re-reads every authored root in lockstep with the search's rewritten root
//! and, at each quantifier occurrence, maps the search's constants onto
//! AUTHORED-surface terms (the instance values of the enclosing occurrences
//! and freshly registered Skolem witnesses) by exact structural alignment
//! ([`align`]). [`lemma_plan`] turns that walk into the tautological lemma
//! clauses of the UNSAT expansion certificate.
//!
//! SAT (M3b): [`qf_formula`] builds the quantifier-free expansion of a
//! NEGATED conjunct that the quantified model gate's expansion route refutes.
//! The instance tuples it expands with are UNTRUSTED hints
//! ([`InstanceHints`]): any tuple of well-sorted quantifier-free terms is a
//! sound instance, so a wrong hint can only cost a confirmation.

mod align;
mod lemma;
pub(in crate::executor) mod lemma_plan;

#[cfg(test)]
mod lemma_plan_tests;

pub(in crate::executor) mod qf_formula;
#[cfg(test)]
mod qf_formula_tests;

use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;

/// Candidate instance tuples, keyed by the AUTHORED quantifier term that
/// opens a maximal same-kind binder chain ([`qf_formula::binder_chain`]).
/// A tuple is positional over that chain's binders; its terms are read in
/// the scope OUTSIDE the chain (they may name enclosing binders by name).
pub(in crate::executor) type InstanceHints = DetHashMap<TermId, Vec<Vec<TermId>>>;

/// Hints one public query's producer installed for the quantified model
/// gate's expansion route (`independent_gate/expansion_route.rs`). DATA, not
/// authority: the route builds its own expansion and confirms only through a
/// checked ground refutation. Bound to the query epoch, its exact ordered
/// roots and an append-only term-store prefix; anything else ignores it.
pub(in crate::executor) struct ExpansionHints {
    pub(in crate::executor) epoch: crate::executor::QueryAuthorityEpoch,
    pub(in crate::executor) roots: Vec<TermId>,
    pub(in crate::executor) stamp: ay_core::term::TermStoreSnapshotStamp,
    pub(in crate::executor) tuples: InstanceHints,
    /// Conjuncts the route was consulted on / confirmed (diagnostics and the
    /// route-order tests; the gate snapshots `last_statistics`).
    pub(in crate::executor) consulted: std::cell::Cell<u32>,
    pub(in crate::executor) confirmed: std::cell::Cell<u32>,
}
