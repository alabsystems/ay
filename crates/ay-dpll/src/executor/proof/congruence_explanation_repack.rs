// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The RE-PACK arm of the congruence-explanation lowering.
//!
//! Split out of `congruence_explanation.rs` so each file stays inside the
//! repository's 500-line ceiling.
//!
//! A packed `(cl (or l1 .. ln))` explanation lemma whose single consumer is
//! the matching `or` step is lowered to the FLAT clause and that consumer is
//! re-justified as `reordering`. Everything else — measured on 2026-08-22,
//! six lemmas in four `soundness_qf_uf_incremental` files, each consumed
//! DIRECTLY by one to three `Resolution` steps — takes this arm instead: the
//! flat derivation is extended by one `or_neg` tautology and one
//! `th_resolution` per disjunct until its last clause is the packed unit
//! again, byte for byte, so no consumer is touched at all.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId};
use ay_proof::CongruenceDerivation;

use super::super::Executor;
use super::congruence_explanation::MAX_REPACK_DISJUNCTS;

impl Executor {
    /// The single `or` consumer whose clause is EXACTLY the packed leaf's
    /// children, or `None`.
    pub(super) fn matching_or_consumer(
        &self,
        proof: &Proof,
        citations: &[Vec<usize>],
        index: usize,
        children: &[TermId],
    ) -> Option<usize> {
        let [consumer] = citations.get(index)?.as_slice() else {
            return None;
        };
        let consumer = *consumer;
        if consumer <= index {
            return None;
        }
        let ProofStep::Step {
            rule: AletheRule::Or,
            clause: consumer_clause,
            premises,
            args,
        } = &proof.steps[consumer]
        else {
            return None;
        };
        if premises.as_slice() != [ProofId(u32::try_from(index).ok()?)]
            || !args.is_empty()
            || consumer_clause.as_slice() != children
        {
            return None;
        }
        Some(consumer)
    }

    /// Whether `negated` is the exact syntactic complement of `literal`:
    /// either `(not literal)` under one `Not` wrapper, or `literal` is
    /// `(not negated)`. Anything else (a De Morgan dual, a folded constant) is
    /// not a resolution complement.
    pub(super) fn is_syntactic_complement(&self, literal: TermId, negated: TermId) -> bool {
        match self.ctx.terms.get(negated) {
            ay_core::TermData::Not(inner) if *inner == literal => true,
            _ => {
                matches!(self.ctx.terms.get(literal), ay_core::TermData::Not(inner) if *inner == negated)
            }
        }
    }

    /// Extend a FLAT derivation so its last clause is the packed unit
    /// `(cl (or l1 .. ln))` the lemma recorded, byte for byte.
    ///
    /// For every disjunct `d` the premiseless `or_neg` tautology supplies
    /// `(cl (or l1 .. ln) (not d))`; resolving each `d` away leaves exactly
    /// `(cl (or l1 .. ln))`. This is the same construction
    /// `proof.rs`'s packed-`or` planner already uses, and every rule in it is
    /// in `CHECKABLE_ALETHE_RULES` with a strict validator in `ay-proof`.
    pub(super) fn repack_derivation(
        &mut self,
        derivation: CongruenceDerivation,
        packed: TermId,
    ) -> Option<CongruenceDerivation> {
        let CongruenceDerivation { mut steps, clause } = derivation;
        // A repeated disjunct would make the resolution below remove two
        // literals at once and the final clause would not be the unit.
        if clause.is_empty() || clause.len() > MAX_REPACK_DISJUNCTS {
            return None;
        }
        for (position, literal) in clause.iter().enumerate() {
            if clause[..position].contains(literal) {
                return None;
            }
        }
        let mut current = steps.len().checked_sub(1)?;
        let mut running = clause.clone();
        for &disjunct in &clause {
            // The resolution below is SYNTACTIC, so the complement must be the
            // literal's exact negation under the proof IR's Boolean
            // normalization: `(not d)` for a positive `d`, and `a` for
            // `d = (not a)`. `mk_not` produces exactly that pair — and pushes
            // negation through `and`/`or`, which is Boolean-equivalent but is
            // NOT a resolution complement, so the shape is CHECKED and a
            // disjunct that does not produce one is declined.
            let negated = self.ctx.terms.mk_not(disjunct);
            if !self.is_syntactic_complement(disjunct, negated) {
                return None;
            }
            let or_neg_clause = vec![packed, negated];
            steps.push(ProofStep::Step {
                rule: AletheRule::OrNeg,
                clause: or_neg_clause,
                premises: Vec::new(),
                args: Vec::new(),
            });
            let or_neg = steps.len().checked_sub(1)?;
            running.retain(|&literal| literal != disjunct);
            if !running.contains(&packed) {
                running.push(packed);
            }
            steps.push(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: running.clone(),
                premises: vec![
                    ProofId(u32::try_from(current).ok()?),
                    ProofId(u32::try_from(or_neg).ok()?),
                ],
                args: Vec::new(),
            });
            current = steps.len().checked_sub(1)?;
        }
        // The fragment must end on EXACTLY the lemma's own clause.
        if running.as_slice() != [packed] || current + 1 != steps.len() {
            return None;
        }
        Some(CongruenceDerivation {
            steps,
            clause: running,
        })
    }
}
