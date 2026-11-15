// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Handing atoms to their owners (design §3.3): the atoms known before the
//! search in canonical order (KC9), minted atoms before the SAT solver can
//! assign them, and the owner's handle kept for every assignment (KC3).

use ay_core::TermId;

use super::Kernel;
use crate::lra_lemmas::ite_links;
use crate::plugin::{GiveUp, ThId};

impl Kernel<'_> {
    /// Tell every owner about every atom known before the search, in the
    /// order of `vars` (canonical content order, KC9).
    pub(crate) fn internalize_in(&mut self, vars: &[u32]) -> Result<(), GiveUp> {
        for &var in vars {
            let entry = usize::try_from(var)
                .ok()
                .and_then(|v| self.atoms.entry(v))
                .ok_or_else(|| GiveUp::new("an ordered atom has no table entry"))?;
            self.internalize(var, entry.owner, entry.term)?;
        }
        Ok(())
    }

    /// Hand `term` to its owner and keep the handle it answers (KC3).
    fn internalize(&mut self, var: u32, owner: ThId, term: TermId) -> Result<(), GiveUp> {
        let handle = self
            .call(owner, None, |p, ctx| p.internalize_atom(ctx, term))
            .unwrap_or_else(|| Err(GiveUp::new("atom owner missing")))?;
        self.atoms.set_handle(var, handle);
        Ok(())
    }

    /// Start the search with the link definitions of the arithmetic ites
    /// `ites` (their atoms are minted at the first propagation).
    pub(crate) fn define_ite_links(&mut self, ites: &[TermId]) {
        for &ite in ites {
            let links = ite_links(self.terms, ite);
            self.effects.lemmas.extend(links);
        }
    }

    /// Minted atoms reach their owner before the SAT solver can assign them:
    /// this runs before the callback that minted them returns.
    pub(super) fn internalize_minted(&mut self) -> Result<(), GiveUp> {
        for (var, owner, term) in std::mem::take(&mut self.minted) {
            self.internalize(var, owner, term)?;
        }
        Ok(())
    }
}
