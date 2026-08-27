// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Alethe `reordering` rule: a clause permutation.
//!
//! # Soundness
//!
//! An Alethe clause `(cl l1 .. ln)` denotes the disjunction `l1 ∨ .. ∨ ln`.
//! Disjunction is commutative and associative, so for any permutation `π`,
//! `l1 ∨ .. ∨ ln` and `l_π(1) ∨ .. ∨ l_π(n)` have the SAME truth value under
//! every assignment — not merely "the premise entails the conclusion", but
//! logical equivalence. A step whose conclusion is a permutation of its single
//! premise therefore adds no information and can never be the point at which a
//! refutation stops being sound: any model falsifying the conclusion falsifies
//! the premise, so the empty clause remains derivable only from a genuinely
//! unsatisfiable leaf set.
//!
//! The check below decides exactly that predicate and nothing weaker: ONE
//! premise, and MULTISET-EQUAL literals compared by `TermId`,
//! which is the hash-consed identity the rest of the checker uses. Requiring a
//! multiset (rather than a set) is deliberately stricter than soundness needs
//! — dropping or duplicating a literal is also entailment-preserving in one
//! direction — because it keeps the rule's meaning identical to the pinned
//! external `reordering`, so a document AY accepts here is one the external
//! checker accepts too. That is scope, not soundness, and is recorded as such
//! in `GUARD_MUTATION_LEDGER`.
//!
//! # Why the premise arity guard IS soundness
//!
//! With zero premises there is no clause to permute. Admitting that case (by
//! reading a missing premise as the empty clause) would accept
//! `(step t (cl) :rule reordering)` — a derivation of FALSE from nothing,
//! which turns every satisfiable problem into a forged refutation. The guard
//! is checked first and fails closed.

use ay_core::{ProofId, TermId, TermStore};

use super::boolean::err;
use super::ProofCheckError;

/// Validate `reordering`: the conclusion is a permutation of the one premise.
pub(crate) fn validate_reordering(
    _terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    let [premise] = premise_clauses else {
        return err(step, "reordering", "rule requires exactly one premise");
    };
    let mut conclusion_sorted = clause.to_vec();
    conclusion_sorted.sort_unstable();
    // NB `Vec` equality already implies equal LENGTH, so a separate arity
    // check would be redundant — it was written, and deleting it failed no
    // test (recorded in `GUARD_MUTATION_LEDGER` as a negative result).
    let mut premise_sorted = premise.to_vec();
    premise_sorted.sort_unstable();
    if conclusion_sorted != premise_sorted {
        return err(
            step,
            "reordering",
            "conclusion is not a permutation of the premise clause",
        );
    }
    Ok(())
}

#[cfg(test)]
#[path = "reordering_tests.rs"]
mod tests;
