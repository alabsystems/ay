// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Plan a derivation of a REWRITTEN assertion from the AUTHORED assertions and
//! CHECKED definitions it was rewritten from — by congruence, and by nothing
//! else.
//!
//! # The class this serves
//!
//! Preprocessing rewrites an authored assertion and asserts the REWRITE.
//! `VariableSubstitution` inlines an authored array definition:
//!
//! ```text
//! authored   (assert (= a_252 (store a_250 i1 e_251)))
//! authored   (assert (= a_250 (store a1   i0 e_249)))
//! authored   (assert (= e_253 (select a_252 i2)))
//! asserted   (= e_253 (select (store (store a1 i0 e_249) i1 e_251) i2))
//! ```
//!
//! The rewrite is not a problem assertion, so `demote_non_problem_assumptions`
//! turns it into a premiseless `trust` step and the mandatory strict check
//! refuses the whole proof. But the rewrite is ENTAILED by the three authored
//! assertions, purely by congruence — no theory, no arithmetic, no array
//! axiom. This module plans that entailment as Alethe steps.
//!
//! # What is planned
//!
//! For a goal `(= s t)` and a pool of candidate hypotheses (positive binary
//! equalities), the BRIDGE CLAUSE
//!
//! ```text
//! (cl (not h_1) .. (not h_k) (= s t))
//! ```
//!
//! over the hypotheses the explanation actually uses, derived by
//! [`crate::plan_euf_congruence_derivation`] from `eq_congruent` /
//! `eq_reflexive` / `eq_transitive` / `th_resolution` / `weakening` /
//! `reordering` steps — every one of them in
//! [`ay_core::CHECKABLE_ALETHE_RULES`], with a strict validator in this crate.
//! The caller discharges each `(not h_i)` against its own leaf (an `assume` of
//! the authored assertion, or the checked definition step that states it).
//!
//! # Why the hypothesis set is MINIMISED
//!
//! The pool is the whole authored equality scope, which on the measured QF_AX
//! population is ~40 assertions carrying deep `store` chains. Carrying all of
//! them into the bridge clause would be sound but ruinous: the strict
//! checker's semantic precharge for `weakening`/`reordering` is quadratic in
//! the TREE-unfolded payload, and these are exactly the heavily-shared `store`
//! chains where tree unfolding dwarfs the DAG. So the planner runs the
//! explanation once over the whole pool, reads off the hypotheses it actually
//! cited ([`crate::congruence_derivation::essential_clause`]), and re-plans
//! over those alone.
//!
//! # Authority
//!
//! Nothing here is asserted. Every planned step is a premise-free tautology
//! decided by the checker's own validators from the clause structure alone, or
//! a resolution decided from its premises. The caller re-runs the untouched
//! strict checker over the fragment before it may replace anything, and a plan
//! that does not replay is DISCARDED — leaving the byte-identical `trust` step
//! it was trying to remove.

use ay_core::{TermData, TermId, TermStore};

use crate::congruence_derivation::{essential_clause, CongruenceDerivation};

/// Largest candidate pool one bridge will consider. A pool larger than this is
/// declined outright rather than closed over: the closure is per-goal, and an
/// adversarial problem must not be able to make it unbounded.
pub const MAX_BRIDGE_CANDIDATES: usize = 1024;

/// A planned derivation of one rewritten assertion.
pub struct DefinitionBridge {
    /// The POSITIVE equalities the derivation cites, in the order their
    /// negations appear in the bridge clause. The caller supplies one leaf
    /// per entry and resolves them away in this order.
    pub hypotheses: Vec<TermId>,
    /// Steps deriving `(cl (not h_1) .. (not h_k) goal)`, with premise ids
    /// RELATIVE to the fragment.
    pub derivation: CongruenceDerivation,
}

/// Decode a term as a binary `=` APPLICATION. Deliberately structural: a
/// Boolean `=` that `mk_eq` folded away is not an application and is declined.
fn decode_binary_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(ay_core::Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// `(not positive)` with an explicit `Not` wrapper, verified — `mk_not`
/// normalises De Morgan and double negation, so a candidate whose negation is
/// not a plain wrapper is DROPPED rather than mis-read as a hypothesis.
fn negate(terms: &mut TermStore, positive: TermId) -> Option<TermId> {
    let built = terms.mk_not(positive);
    matches!(terms.get(built), TermData::Not(inner) if *inner == positive).then_some(built)
}

/// Plan a bridge for `goal` over `candidates`, or `None` when there is none.
///
/// `candidates` are POSITIVE equality terms the caller can supply a checked
/// leaf for. Anything else in the slice is ignored.
#[must_use]
pub fn plan_definitional_bridge(
    terms: &mut TermStore,
    goal: TermId,
    candidates: &[TermId],
) -> Option<DefinitionBridge> {
    // The goal must be a binary `=` application: that is the class, and it is
    // also what `parse_clause` will read as the bridge clause's one positive
    // literal.
    let _goal_sides = decode_binary_eq(terms, goal)?;
    if candidates.len() > MAX_BRIDGE_CANDIDATES {
        return None;
    }
    let mut positives: Vec<TermId> = Vec::with_capacity(candidates.len());
    let mut negatives: Vec<TermId> = Vec::with_capacity(candidates.len());
    for &candidate in candidates {
        // A candidate that IS the goal would make the bridge clause a
        // propositional tautology rather than a congruence explanation, and
        // the goal would then be an authored assertion that never needed
        // demoting. Declined, fail-closed.
        if candidate == goal || decode_binary_eq(terms, candidate).is_none() {
            continue;
        }
        if positives.contains(&candidate) {
            continue;
        }
        let Some(negated) = negate(terms, candidate) else {
            continue;
        };
        // A negation that collides with the goal or with another candidate's
        // negation would make the clause carry a repeated literal, which
        // `parse_clause` declines anyway.
        if negated == goal || negatives.contains(&negated) {
            continue;
        }
        positives.push(candidate);
        negatives.push(negated);
    }
    if positives.is_empty() {
        return None;
    }

    // PASS 1 — the whole pool, to find out which hypotheses the explanation
    // needs. Its steps are thrown away; only the cited literals are kept.
    let mut full: Vec<TermId> = negatives.clone();
    full.push(goal);
    let cited = essential_clause(terms, &full)?;

    // PASS 2 — the minimal clause. Every cited literal must be one of the
    // clause's own, and the goal must be among them; anything else means the
    // planner and the emitter disagree, and the answer to that is to decline.
    let mut hypotheses: Vec<TermId> = Vec::new();
    let mut literals: Vec<TermId> = Vec::new();
    for (positive, negated) in positives.iter().zip(negatives.iter()) {
        if cited.contains(negated) {
            hypotheses.push(*positive);
            literals.push(*negated);
        }
    }
    if hypotheses.is_empty() || !cited.contains(&goal) || cited.len() != literals.len() + 1 {
        return None;
    }
    literals.push(goal);
    let derivation = crate::plan_euf_congruence_derivation(terms, &literals)?;
    // The fragment's last clause is what the caller resolves against, literal
    // by literal, so it must be exactly the clause planned here.
    (derivation.clause == literals).then_some(DefinitionBridge {
        hypotheses,
        derivation,
    })
}

#[cfg(test)]
#[path = "definition_bridge_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "definition_bridge_negative_tests.rs"]
mod negative_tests;
