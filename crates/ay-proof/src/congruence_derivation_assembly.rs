// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assembling a planned congruence derivation: restoring the recorded clause,
//! and closing the fragment so the strict checker can replay it.
//!
//! Split out of `congruence_derivation` so each file stays inside the
//! repository's per-file line ceiling.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TermStore};

use super::{CongruenceDerivation, MAX_DERIVATION_STEPS};

/// Close a planned derivation into a self-contained refutation the strict
/// checker can replay, changing NOTHING about the derivation itself.
///
/// `check_proof_strict` demands a closed proof, so the fragment is closed over
/// the negation of each literal of its own conclusion: assume `¬l`, resolve it
/// away, finish on the empty clause. Every step of the DERIVATION is validated
/// on the way by exactly the validators the mandatory gate runs. Shared, so the
/// producer's admission gate and the tests' gate cannot drift.
#[must_use]
pub fn close_congruence_derivation(
    terms: &mut TermStore,
    derivation: &CongruenceDerivation,
) -> Proof {
    let mut proof = Proof::default();
    proof.steps.extend(derivation.steps.iter().cloned());
    let Some(last) = derivation.steps.len().checked_sub(1) else {
        return proof;
    };
    let mut current = derivation.clause.clone();
    let mut current_id = ProofId(u32::try_from(last).unwrap_or(u32::MAX));
    for &literal in &derivation.clause {
        let negated = complement_of(terms, literal);
        let assumed = ProofId(u32::try_from(proof.steps.len()).unwrap_or(u32::MAX));
        proof.steps.push(ProofStep::Assume(negated));
        current.retain(|other| *other != literal);
        let resolved = ProofId(u32::try_from(proof.steps.len()).unwrap_or(u32::MAX));
        proof.steps.push(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: current.clone(),
            premises: vec![current_id, assumed],
            args: Vec::new(),
        });
        current_id = resolved;
    }
    proof
}

/// The SYNTACTIC complement of `literal` — the term the closing resolution can
/// actually cancel it against.
///
/// `mk_not` is the right answer for the literal shapes this closer was written
/// for: it wraps a positive literal in one `Not` and cancels the wrapper off a
/// negative one, which is exactly the proof IR's Boolean normalization. It is
/// the WRONG answer for a literal that is itself an `and`/`or`/`ite`, because
/// it returns the De Morgan DUAL — Boolean-equivalent, but not a resolution
/// complement, so the closing step is refused and a perfectly good fragment is
/// declined. Measured on `soundness_qf_uf_incremental/clearsy_0000_00307`: the
/// unit `(cl (or (= (bool p) (bool q)) (not (= p q))))` closed against
/// `(and (= p q) (not (= (bool p) (bool q))))` and the strict checker answered
/// `invalid resolution derivation`.
///
/// So: take `mk_not`'s answer when it IS the complement, and the raw `Not`
/// wrapper otherwise. This only ever admits fragments the closer previously
/// refused for a reason that was not about the fragment; the closed proof is
/// still replayed in full by `check_proof_strict`, which remains the only
/// authority over what may be committed.
fn complement_of(terms: &mut TermStore, literal: TermId) -> TermId {
    let normalized = terms.mk_not(literal);
    let cancels = match terms.get(normalized) {
        ay_core::TermData::Not(inner) => *inner == literal,
        _ => matches!(terms.get(literal), ay_core::TermData::Not(inner) if *inner == normalized),
    };
    if cancels {
        normalized
    } else {
        terms.mk_not_raw(literal)
    }
}

/// Weaken the derived clause back to every recorded hypothesis and restore the
/// recorded literal order, so the replacement is invisible to every consumer.
pub(super) fn finish(
    steps: &mut Vec<ProofStep>,
    step: usize,
    clause: Vec<TermId>,
    literals: &[TermId],
) -> Option<CongruenceDerivation> {
    if !clause.iter().all(|literal| literals.contains(literal)) {
        return None;
    }
    let mut last = step;
    let mut current = clause;
    // A tautology step legitimately REPEATS a literal: `(= (g a b) (g b a))`
    // under `a = b` needs the same premise equality at both argument
    // positions, and `eq_congruent` consumes one premise per differing
    // position. `weakening`/`reordering` are multiset rules, so the repeat is
    // removed first — by `contraction`, whose validator decides exactly that.
    if current
        .iter()
        .enumerate()
        .any(|(position, literal)| current[..position].contains(literal))
    {
        let mut contracted: Vec<TermId> = Vec::with_capacity(current.len());
        for &literal in &current {
            if !contracted.contains(&literal) {
                contracted.push(literal);
            }
        }
        last = push_derived(steps, AletheRule::Contraction, contracted.clone(), last)?;
        current = contracted;
    }
    if current.len() != literals.len() {
        // `weakening` requires its premise to be a PREFIX of the result.
        let mut widened = current.clone();
        widened.extend(literals.iter().copied().filter(|l| !current.contains(l)));
        last = push_derived(steps, AletheRule::Weakening, widened.clone(), last)?;
        current = widened;
    }
    if current != literals {
        last = push_derived(steps, AletheRule::Reordering, literals.to_vec(), last)?;
    }
    if last + 1 != steps.len() {
        return None;
    }
    Some(CongruenceDerivation {
        steps: std::mem::take(steps),
        clause: literals.to_vec(),
    })
}

/// Push a one-premise step and return its index.
fn push_derived(
    steps: &mut Vec<ProofStep>,
    rule: AletheRule,
    clause: Vec<TermId>,
    premise: usize,
) -> Option<usize> {
    if steps.len() >= MAX_DERIVATION_STEPS {
        return None;
    }
    let id = steps.len();
    steps.push(ProofStep::Step {
        rule,
        clause,
        premises: vec![ProofId(u32::try_from(premise).ok()?)],
        args: Vec::new(),
    });
    Some(id)
}

/// Whether every step of a planned derivation RENDERS under the same surface
/// overrides the exporter will use.
///
/// The printer is fail-loud: a step it cannot render as a spec-valid Alethe
/// inference makes the whole export refuse to publish, which turns a published
/// `unsat` into no answer at all. Deciding that HERE, with the printer itself,
/// means the producer declines exactly the fragments the exporter would refuse
/// — no second opinion, no drift.
#[must_use]
pub fn congruence_derivation_renders(
    terms: &TermStore,
    overrides: Option<&ay_core::kani_compat::DetHashMap<TermId, String>>,
    derivation: &CongruenceDerivation,
) -> bool {
    let printer = crate::alethe_printer::AlethePrinter::new_with_overrides(terms, overrides);
    derivation.steps.iter().enumerate().all(|(index, step)| {
        printer
            .format_step(step, ProofId(u32::try_from(index).unwrap_or(u32::MAX)))
            .is_ok()
    })
}

#[cfg(test)]
#[path = "congruence_derivation_closer_tests.rs"]
mod closer_tests;
