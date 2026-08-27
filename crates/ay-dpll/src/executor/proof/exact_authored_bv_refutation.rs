// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-authored Bool/BV refutation: an independently replayed bit-blast
//! theorem resolved against exact authored roots.

use super::*;

impl Executor {
    /// Replace a non-strict provisional BV refutation with a complete,
    /// independently replayed Bool/BV refutation of the exact authored roots.
    ///
    /// The checker first proves the clause `¬A1 ∨ ... ∨ ¬An` with its bounded
    /// bit-blast/LRAT producer. Exact `Assume(Ai)` leaves then resolve that
    /// theorem to the empty clause. Unsupported roots, too many roots, SAT
    /// authored conjunctions, resource exhaustion, or any whole-proof replay
    /// failure leave the original trust-bearing proof untouched.
    pub(super) fn replace_with_exact_authored_bv_refutation(&mut self, proof: &mut Proof) {
        const MAX_AUTHORED_ROOTS: usize = 64;
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }

        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty()
            || authored.len() > MAX_AUTHORED_ROOTS
            || authored
                .iter()
                .any(|&term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return;
        }

        let mut exact_roots = Vec::with_capacity(authored.len());
        let mut opposites = Vec::with_capacity(authored.len());
        for &assertion in &authored {
            let opposite = match self.ctx.terms.get(assertion).clone() {
                TermData::Not(inner) => inner,
                _ => self.ctx.terms.mk_not_raw(assertion),
            };
            // Resolution removes one complementary literal per assumption.
            // Distinct authored syntax can normalize to the same opposite;
            // retain the first exact root only so one resolution removes one
            // occurrence and the final residual is structurally honest.
            if opposites.contains(&opposite) {
                continue;
            }
            exact_roots.push(assertion);
            opposites.push(opposite);
        }
        if !ay_proof::recognize_bv_bitblast(&self.ctx.terms, &opposites) {
            return;
        }

        let mut candidate = Proof::new();
        let assumptions: Vec<ProofId> = exact_roots
            .iter()
            .enumerate()
            .map(|(index, &assertion)| {
                candidate.add_assume(assertion, Some(format!("authored_bv_{index}")))
            })
            .collect();
        let mut current = candidate.add_theory_lemma_with_kind(
            "bv",
            opposites.clone(),
            TheoryLemmaKind::BvBitBlast,
        );
        let mut residual = opposites.clone();
        for (&assumption, &opposite) in assumptions.iter().zip(opposites.iter()) {
            residual.retain(|&literal| literal != opposite);
            current = candidate.add_rule_step(
                AletheRule::ThResolution,
                residual.clone(),
                vec![current, assumption],
                Vec::new(),
            );
        }
        if residual.is_empty()
            && ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
        {
            *proof = candidate;
        }
    }
}
