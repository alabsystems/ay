// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive the packed congruence-closure explanations whose only defect is
//! LITERAL ORDER.
//!
//! # The gap this closes
//!
//! `SatProofManager::add_original_clause_step` records a multi-literal original
//! clause as `assume (or l1 .. ln)` plus `(step .. (cl l1 .. ln) :rule or)`.
//! When the assume is not on the problem whitelist,
//! `demote_non_problem_assumptions` rewrites it into a premiseless
//! `Step { rule: Trust }` and mandatory strict certification refuses the whole
//! proof.
//!
//! `intrinsic_leaf_promotion` already relabels such a leaf whenever a strict
//! validator accepts the clause AS RECORDED. It deliberately does not reorder,
//! and that is exactly what this population needs: measured corpus-wide, a
//! large share of the residual QF_AX/QF_AUFLIA `or#N` leaves are EUF
//! transitivity chains that `validate_euf_transitive` accepts only with the
//! positive conclusion LAST, while the solver recorded it in the middle.
//!
//! # What is emitted
//!
//! Two steps, in place, with no step added or removed:
//!
//! ```text
//!  before                                        after
//!  i: (cl (or l1 .. ln))          :rule trust    i: (cl lp1 .. lpn) EufTransitive lemma
//!  j: (cl l1 .. ln)  :rule or  :premises (i)     j: (cl l1 .. ln) :rule reordering :premises (i)
//! ```
//!
//! where `lp1..lpn` is `l1..ln` with the unique positive literal moved last.
//! **Step `j`'s clause is byte-identical to what it was**, so every downstream
//! premise reference, resolution and pivot sees exactly the clause it saw
//! before. Only the JUSTIFICATION of `j` changes, from `or` (which needs a
//! packed unit premise) to `reordering` (which needs a permutation premise).
//!
//! # Why this is not an authority claim
//!
//! Neither replacement asserts anything the untouched strict checker does not
//! re-derive:
//!
//! * step `i` becomes `TheoryLemmaKind::EufTransitive`, whose validator IS
//!   `ay_proof::checker::validate_euf_transitive` — the same function this pass
//!   calls through `recognize_euf_transitive` before committing. The clause is
//!   accepted from nothing: no premise, no payload, no problem context;
//! * step `j` becomes `AletheRule::Reordering`, validated by
//!   `ay_proof::checker::reordering::validate_reordering` as a multiset-equal
//!   permutation of step `i`. A clause is a disjunction and `or` is
//!   commutative, so the two are logically equivalent, not merely related by
//!   entailment.
//!
//! A leaf any guard declines keeps its BYTE-IDENTICAL `trust` step and its
//! `or` consumer, so the pass can only move a proof from "rejected" toward
//! "checked" — never the reverse.
//!
//! # Guards
//!
//! Each is mutation-checked in `packed_euf_reordering_tests.rs`
//! (`GUARD_MUTATION_LEDGER` there).
//!
//! 0. **Not already accepted as recorded.** `intrinsic_leaf_promotion` runs
//!    earlier and owns that case; declining keeps this lane strictly additive.
//! 1. **Premiseless, argument-free `trust` leaf over a packed `or`.** A trust
//!    step with premises is a failed derivation, not a leaf.
//! 2. **Exactly one positive literal.** `validate_euf_transitive` needs one
//!    positive-equality conclusion; more than one (or none) is a different
//!    clause shape and is declined rather than guessed at.
//! 3. **The permuted clause is accepted by `recognize_euf_transitive`.** This
//!    is the whole authority: the checker's own validator, run first.
//! 4. **The single consumer is the matching `or` step.** The leaf's clause
//!    stops being the packed unit, so an `or` consumer would break. Requiring
//!    exactly one reference, that it is `Or`, that it cites only this leaf,
//!    that its clause is exactly the flattened children, and that it comes
//!    LATER in the proof, means the rewrite is local and complete.
//! 5. **No unrenderable surface override.** A promoted `EufTransitive` lemma
//!    whose hypothesis prints as something other than `(not ..)`/`(distinct ..)`
//!    is demoted to `hole` two lanes later, which would trade a rescuable
//!    `trust` rejection for a hard one. Decided by the SAME predicate that
//!    demotion uses, so the two cannot drift.

use ay_core::{
    AletheRule, Proof, ProofId, ProofStep, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};

use super::super::Executor;

/// The children of a unit `(cl (or l1 .. ln))` clause, `None` otherwise.
pub(super) fn packed_or_children(terms: &TermStore, clause: &[TermId]) -> Option<Vec<TermId>> {
    let [packed] = clause else { return None };
    let TermData::App(Symbol::Named(operator), children) = terms.get(*packed) else {
        return None;
    };
    (operator == "or" && children.len() >= 2).then(|| children.clone())
}

/// The clause with its unique POSITIVE literal moved last, every other literal
/// left in the recorded order. `None` unless exactly one literal is positive.
///
/// This is the only permutation `validate_euf_transitive` can accept: it reads
/// the last literal as the conclusion equality and requires every other to be
/// a negated equality, while the premise equalities themselves may appear in
/// any order (they are edges of an undirected path search).
fn conclusion_last(terms: &TermStore, flat: &[TermId]) -> Option<Vec<TermId>> {
    let mut positive: Option<usize> = None;
    for (index, &literal) in flat.iter().enumerate() {
        if !matches!(terms.get(literal), TermData::Not(_)) {
            if positive.is_some() {
                return None;
            }
            positive = Some(index);
        }
    }
    let index = positive?;
    let mut permuted = flat.to_vec();
    let conclusion = permuted.remove(index);
    permuted.push(conclusion);
    Some(permuted)
}

/// For every step, the indices that REFERENCE it — as an inference premise, as
/// a resolution operand, or as a subproof's end step.
///
/// Built ONCE. The rewrite below never changes the reference graph (the leaf
/// loses no premise, because it had none, and the consumer keeps citing
/// exactly the same leaf), so one pass is equivalent to re-scanning per leaf
/// and keeps the lane linear on proofs that carry thousands of these leaves.
pub(super) fn reference_map(proof: &Proof) -> Vec<Vec<usize>> {
    let mut map: Vec<Vec<usize>> = vec![Vec::new(); proof.steps.len()];
    let mut cite = |target: ProofId, index: usize| {
        if let Some(slot) = map.get_mut(target.0 as usize) {
            slot.push(index);
        }
    };
    for (index, step) in proof.steps.iter().enumerate() {
        match step {
            ProofStep::Step { premises, .. } => {
                for &premise in premises {
                    cite(premise, index);
                }
            }
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                cite(*clause1, index);
                cite(*clause2, index);
            }
            ProofStep::Anchor { end_step, .. } => cite(*end_step, index),
            _ => {}
        }
    }
    map
}

impl Executor {
    /// Re-derive every packed `or` trust leaf that is an EUF transitivity chain
    /// under permutation. Returns the number of leaves converted, which the
    /// tests assert on.
    pub(in crate::executor) fn derive_packed_euf_transitive_reorderings(
        &self,
        proof: &mut Proof,
    ) -> usize {
        let terms = &self.ctx.terms;
        let citations = reference_map(proof);
        let mut derived = 0usize;
        for (index, citation) in citations.iter().enumerate() {
            // Guard 1: a premiseless, argument-free `trust` leaf over a packed
            // `or` term.
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                args,
            } = &proof.steps[index]
            else {
                continue;
            };
            if !premises.is_empty() || !args.is_empty() {
                continue;
            }
            let Some(flat) = packed_or_children(terms, clause) else {
                continue;
            };
            // Already accepted AS RECORDED: `intrinsic_leaf_promotion` owns
            // that case and has already had first refusal (it runs earlier).
            // Declining keeps this lane strictly additive — it only ever sees
            // leaves that pass declined.
            if ay_proof::recognize_euf_transitive(terms, clause) {
                continue;
            }
            // Guard 2 + 3: the one permutation the validator can accept, and
            // the validator's own verdict on it.
            let Some(permuted) = conclusion_last(terms, &flat) else {
                continue;
            };
            if !ay_proof::recognize_euf_transitive(terms, &permuted) {
                continue;
            }
            // Guard 5: a lemma the printer cannot render is demoted to `hole`
            // downstream; decline instead of trading rejection classes.
            if self
                .last_proof_term_overrides
                .as_ref()
                .is_some_and(|overrides| {
                    Self::eq_transitive_clause_is_unrenderable(terms, overrides, &permuted)
                })
            {
                continue;
            }
            // Guard 4: exactly one consumer, and it is the matching `or` step.
            let leaf = ProofId(u32::try_from(index).unwrap_or(u32::MAX));
            let [consumer] = citation.as_slice() else {
                continue;
            };
            let consumer = *consumer;
            if consumer <= index {
                continue;
            }
            let ProofStep::Step {
                rule: AletheRule::Or,
                clause: consumer_clause,
                premises: consumer_premises,
                args: consumer_args,
            } = &proof.steps[consumer]
            else {
                continue;
            };
            if consumer_premises.as_slice() != [leaf]
                || !consumer_args.is_empty()
                || consumer_clause.as_slice() != flat.as_slice()
            {
                continue;
            }
            proof.steps[index] = ProofStep::TheoryLemma {
                theory: "EUF".to_owned(),
                clause: permuted,
                farkas: None,
                kind: TheoryLemmaKind::EufTransitive,
                lia: None,
            };
            proof.steps[consumer] = ProofStep::Step {
                rule: AletheRule::Reordering,
                clause: flat,
                premises: vec![leaf],
                args: Vec::new(),
            };
            derived += 1;
        }
        derived
    }
}

#[cfg(test)]
#[path = "packed_euf_reordering_tests.rs"]
mod tests;
