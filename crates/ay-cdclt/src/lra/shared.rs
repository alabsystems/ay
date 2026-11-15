// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The LRA plug-in's side of the hub (design H1): opaque applications,
//! shared terms and their model values.

use ay_core::{TermData, TermId, TermStore};
use num_rational::BigRational;

use super::LraPlugin;
use crate::arith_defs::define_operators;
use crate::plugin::{Ctx, GiveUp, ThVar};

impl LraPlugin {
    /// Uninterpreted applications inside arithmetic atoms are opaque
    /// variables whose equalities the hub decides (design H1): the simplex
    /// must not call their atoms unsupported. The registry has named every
    /// other operator the simplex cannot interpret before the search.
    #[must_use]
    pub fn with_opaque_applications(mut self, on: bool) -> Self {
        self.lra.set_opaque_applications(on);
        self
    }

    /// The value of a term in the kept model: its own entry, or its linear
    /// form over entries (a shared term such as `(+ x 1)` has no column).
    pub(super) fn value_of(&mut self, terms: &TermStore, term: TermId) -> Option<BigRational> {
        let model = self.model.as_ref()?;
        if let Some(value) = model.values.get(&term) {
            return Some(value.clone());
        }
        let form = self.lin.linearize(terms, term).ok()?;
        let mut value = form.constant.clone();
        for (leaf, coeff) in &form.coeffs {
            value += coeff * model.values.get(leaf)?;
        }
        Some(value)
    }

    /// A hub node of this plug-in's sort: a shared term (design H1). Its
    /// operators are the ones an atom may hold (named otherwise), its
    /// `div`/`mod`/`abs` get their definitions, and its leaves get columns,
    /// so it has a value in every model.
    pub(super) fn attach_shared(
        &mut self,
        ctx: &mut Ctx<'_>,
        term: TermId,
    ) -> Result<ThVar, GiveUp> {
        let form = self.lin.linearize(ctx.terms(), term)?;
        let leaves: Vec<TermId> = form.coeffs.keys().copied().collect();
        if leaves
            .iter()
            .any(|&l| matches!(ctx.terms().get(l), TermData::Ite(..)))
        {
            // Its link lemmas come only with an atom that holds it.
            return Err(GiveUp::new("lra: a shared term holds a term-level ite"));
        }
        define_operators(ctx, term, &mut self.defined);
        self.bracket(ctx.terms(), |lra| {
            for leaf in leaves {
                lra.ensure_var_registered(leaf);
            }
        });
        self.shared.attach(term)
    }
}
