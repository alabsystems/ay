// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The LRA plug-in's integer mode at a fractional vertex: Gomory cut rounds
//! and the branch choice (z3's `int_solver` schedule).

use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;

use super::LraPlugin;
use crate::lra_lemmas::{branch_lemma, cut_lemma};
use crate::plugin::{Ctx, Lemma};

/// A cut round every this many fractional final checks (z3's
/// `m_int_gomory_cut_period`); the others branch.
const GOMORY_PERIOD: u64 = 4;

/// Cuts per cut round (z3 asks for 2).
const CUTS_PER_ROUND: usize = 2;

/// Cut atoms each add a tableau row; past this many the plug-in only
/// branches.
const MAX_CUTS: usize = 2000;

impl LraPlugin {
    /// Integer mode, every [`GOMORY_PERIOD`]-th final check that finds a
    /// fractional vertex: Gomory cuts as guarded in-search lemmas over newly
    /// minted cut atoms (z3's `int_solver` schedule: a cut round, otherwise a
    /// branch). `None` when this round branches.
    pub(super) fn cuts(&mut self, ctx: &mut Ctx<'_>) -> Option<Vec<Lemma>> {
        self.fractional_rounds += 1;
        if self.fractional_rounds % GOMORY_PERIOD != 0 || self.cuts_added >= MAX_CUTS {
            return None;
        }
        let cuts = self.bracket(ctx.terms(), |lra| lra.gomory_term_cuts(CUTS_PER_ROUND));
        let lemmas: Vec<Lemma> = cuts
            .into_iter()
            .filter_map(|cut| cut_lemma(ctx.terms_mut(), cut))
            .collect();
        if lemmas.is_empty() {
            return None;
        }
        self.cuts_added += lemmas.len();
        Some(lemmas)
    }

    /// Integer mode: the first Int term (by id) with a fractional value.
    ///
    /// Which one: z3's `int_branch` rule — the fractional column with both
    /// bounds and the smallest range, else a pseudo-random fractional one
    /// (a fixed first choice can starve the others).
    pub(super) fn branch(&mut self, ctx: &mut Ctx<'_>) -> Option<Lemma> {
        let mut rng = self.branch_rng;
        let picked = self.lra_pick_fractional(ctx.terms(), &mut rng);
        self.branch_rng = rng;
        let (term, value) = picked?;
        Some(branch_lemma(ctx.terms_mut(), term, &value))
    }

    fn lra_pick_fractional(
        &mut self,
        terms: &TermStore,
        rng: &mut u64,
    ) -> Option<(TermId, BigRational)> {
        self.bracket(terms, |lra| {
            let model = lra.extract_model();
            let mut fractional: Vec<(TermId, BigRational)> = model
                .values
                .into_iter()
                .filter(|(term, value)| !value.is_integer() && terms.sort(*term) == &Sort::Int)
                .collect();
            fractional.sort_by_key(|(term, _)| *term);
            let boxed = fractional
                .iter()
                .filter_map(|(term, value)| {
                    let (Some(lo), Some(hi)) = lra.get_bounds_ref(*term)? else {
                        return None;
                    };
                    Some((
                        (hi.value.to_big() - lo.value.to_big()),
                        *term,
                        value.clone(),
                    ))
                })
                .min_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
            if let Some((_, term, value)) = boxed {
                return Some((term, value));
            }
            if fractional.is_empty() {
                return None;
            }
            *rng ^= *rng << 13;
            *rng ^= *rng >> 7;
            *rng ^= *rng << 17;
            let idx = usize::try_from(*rng % fractional.len() as u64).unwrap_or(0);
            Some(fractional.swap_remove(idx))
        })
    }
}
