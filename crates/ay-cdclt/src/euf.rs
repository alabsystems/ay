// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF as a plug-in on the hub (design H1).
//!
//! Congruence closure is the hub itself: the kernel sends every assigned
//! literal of a hub node to the hub, and the hub's merges, conflicts and
//! propagations are complete for EUF by the time any final check runs. What
//! is left for the plug-in is the rest of a theory's face: it owns the
//! equalities over uninterpreted sorts and the uninterpreted predicates in
//! the registry, and it gives terms of uninterpreted sorts their model
//! values (one abstract element per class of the final assignment).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AtomHandle, Effort, Sort, TermId, TermStore, TheoryLit};

use crate::plugin::{Ctx, Explanation, Final, GiveUp, ThVar, TheoryPlugin};

/// The EUF plug-in (see the module docs).
#[derive(Debug, Default)]
pub struct EufPlugin {
    /// Hub terms of uninterpreted sorts, in registration order.
    elements: Vec<TermId>,
    /// Owned atoms, by handle (KC3: the handle is the index). The hub reads
    /// their values itself; the table only numbers them.
    atoms: Vec<TermId>,
    /// Their class in the accepted assignment.
    classes: HashMap<TermId, u32>,
}

impl EufPlugin {
    /// A plug-in with no terms yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// The value term naming class `class` of `sort`: an internal constant,
    /// the same for every term of the class.
    fn element(terms: &mut TermStore, sort: &Sort, class: u32) -> TermId {
        let name = match sort {
            Sort::Uninterpreted(name) => format!("@euf!{name}!{class}"),
            other => format!("@euf!{other:?}!{class}"),
        };
        terms.mk_var(name, sort.clone())
    }
}

impl TheoryPlugin for EufPlugin {
    fn name(&self) -> &'static str {
        "euf"
    }

    fn internalize_atom(&mut self, _ctx: &mut Ctx<'_>, atom: TermId) -> Result<AtomHandle, GiveUp> {
        let handle = u32::try_from(self.atoms.len())
            .map(AtomHandle)
            .map_err(|_| GiveUp::new("euf: atom handle space exhausted"))?;
        self.atoms.push(atom);
        Ok(handle)
    }

    fn attach_term(&mut self, ctx: &mut Ctx<'_>, term: TermId) -> Result<Option<ThVar>, GiveUp> {
        if ctx.terms().sort(term).is_uninterpreted() {
            self.elements.push(term);
        }
        Ok(None)
    }

    /// The kernel already sent the literal to the hub.
    fn assign(
        &mut self,
        _ctx: &mut Ctx<'_>,
        _atom: AtomHandle,
        _value: bool,
    ) -> Result<(), GiveUp> {
        Ok(())
    }

    fn propagate(&mut self, _ctx: &mut Ctx<'_>) -> Result<(), GiveUp> {
        Ok(())
    }

    fn can_propagate(&self) -> bool {
        false
    }

    /// Congruence is complete in the hub before any final check runs.
    fn final_check(&mut self, _ctx: &mut Ctx<'_>, _effort: Effort) -> Result<Final, GiveUp> {
        Ok(Final::Sat)
    }

    fn explain(&mut self, _ctx: &mut Ctx<'_>, _lit: TheoryLit, _token: u64) -> Option<Explanation> {
        None
    }

    fn push_scope(&mut self, _ctx: &mut Ctx<'_>) {}

    fn pop_scope(&mut self, _ctx: &mut Ctx<'_>, _n: u32) {}

    fn on_sat(&mut self, ctx: &mut Ctx<'_>) {
        self.classes.clear();
        for &term in &self.elements {
            if let Some(class) = ctx.class_of(term) {
                self.classes.insert(term, class);
            }
        }
    }

    /// No phase hints (the trait-default `phase()`), so the answers are
    /// constant — report a constant epoch, like the DL plug-in. Without
    /// this, the default `None` poisons the kernel's epoch fold and the
    /// phase re-seed skip never engages on lanes that include EUF.
    /// If this plug-in ever grows real phase hints, this must become a
    /// real generation counter over whatever they read.
    fn phase_epoch(&self) -> Option<u64> {
        Some(0)
    }

    fn model_value(&mut self, ctx: &mut Ctx<'_>, term: TermId) -> Option<TermId> {
        let class = *self.classes.get(&term)?;
        let sort = ctx.terms().sort(term).clone();
        Some(Self::element(ctx.terms_mut(), &sort, class))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The EUF plug-in never returns phase hints (the trait default
    /// `phase() -> None`), so its phase answers are constant. Its epoch
    /// must say so: the kernel folds plug-in epochs with `None` meaning
    /// "unknown", and a default-`None` here silently disables the
    /// kernel's phase re-seed skip on every UF lane.
    #[test]
    fn euf_phase_epoch_is_constant() {
        assert_eq!(EufPlugin::new().phase_epoch(), Some(0));
    }
}
