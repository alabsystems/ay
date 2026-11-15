// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Refute the negated checked multiplication overflow identity before SAT
//! clausification.
//!
//! external-codegen's u128 `checked_mul` lowering asserts that the schoolbook high
//! half is non-zero exactly when dividing the wrapped product by the
//! multiplicand fails to give back the multiplier. Bit-blasting that at 128
//! bits (two 128-bit multipliers and a 128-stage divider) never finishes, but
//! the identity holds for every limb value: its negation is refuted by the one
//! `BvMulOverflowDivision` lemma, which the strict checker re-derives term for
//! term and the Alethe printer certifies completely.

use super::{bounded_source, source, Executor};
use ay_core::{Proof, Symbol, TermData, TermId, TheoryLemmaKind};

impl Executor {
    /// Commit the refutation of a lone authored `(not (= L R))` whose equality
    /// is exactly the checked multiplication overflow identity.
    pub(in crate::executor) fn try_early_mul_overflow_refutation(&mut self) -> bool {
        if crate::executor::theories::bv_cnf_dump::requested()
            || !self.ctx.objectives().is_empty()
            || !self.ctx.soft_constraints().is_empty()
            || self.ctx.assertions_parsed().len() != 1
            || self.should_abort_theory_loop()
        {
            return false;
        }
        let Some(authored) = self.authenticated_plain_query_assertions_after_named_core_redirect()
        else {
            return false;
        };
        if authored.len() != 1 {
            return false;
        }
        let Some(assertion) = source::expand(&self.ctx, &self.ctx.assertions_parsed()[0]) else {
            return false;
        };
        // Bound the walk before elaborating it a second time; the identity
        // reads no array.
        if bounded_source(&assertion) != Some(false)
            || self.ctx.elaborate_surface_subterm(&assertion) != Some(authored[0])
        {
            return false;
        }
        let Some(root) = self.raw_intern_surface(&assertion) else {
            return false;
        };
        let Some(equality) = negated(&self.ctx.terms, root) else {
            return false;
        };
        if !ay_proof::recognize_mul_overflow_division(&self.ctx.terms, &[equality])
            || !self.guarded_terms_print_faithfully(&[root, equality])
        {
            return false;
        }
        let mut candidate = Proof::new();
        let premise = candidate.add_assume(root, None);
        let lemma = candidate.add_theory_lemma_with_kind(
            "bv",
            vec![equality],
            TheoryLemmaKind::BvMulOverflowDivision,
        );
        candidate.add_resolution(Vec::new(), equality, premise, lemma);
        // The lemma is admitted only by the strict checker's own recognizer;
        // the single Assume was authenticated against the public epoch above.
        let Ok(quality) = self.check_proof_strict_derivation_with_datatypes(&candidate) else {
            return false;
        };
        if self.should_abort_theory_loop()
            || self.authenticated_plain_query_assertions_after_named_core_redirect()
                != Some(authored)
        {
            return false;
        }
        self.record_raw_authored_problem_assertion(root);
        self.commit_authenticated_plain_refutation(candidate, quality);
        true
    }
}

fn negated(terms: &ay_core::TermStore, root: TermId) -> Option<TermId> {
    match terms.get(root) {
        TermData::Not(inner) => Some(*inner),
        TermData::App(Symbol::Named(name), args) if &**name == "not" && args.len() == 1 => {
            Some(args[0])
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "mul_overflow_tests.rs"]
mod tests;
