// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-purpose, producer-owned fresh BV64 identities; no solver authority.

use super::{Admission, ControlledTermInternError, Result, StoreRole};
use crate::term::{Sort, TermData, TermId, TermStore};
use std::mem::size_of;

mod names;
mod registry;
#[cfg(test)]
mod tests;

const PREFIX: &str = "__ay_range_pin!";

impl TermStore {
    /// Mint and register a fresh BV64 binder in this SAME producer arena.
    ///
    /// The caller supplies no visible name or identity. A bounded scan chooses
    /// above the original counter and every existing Var id or matching internal
    /// name in the entire arena/registry, including inactive and nested binders.
    /// An exhausted namespace refuses rather than wrapping or reusing a name.
    ///
    /// Borrow the SAME original progress/WorkBudget used for all later nodes.
    /// Constructor-origin ResourceLimit must be latched by that owner before
    /// retry. No grant, deadline, callback owner, reset or solver is created.
    /// This is DATA freshness, not a lambda/body typing or source certificate.
    /// Reservations, consumed counters and inert entries may remain on refusal;
    /// the final fence can revoke a committed handle after scratch disposal.
    pub fn try_fresh_bv64_binder_with_progress(
        &mut self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = self.fresh_bv64_controlled(&mut admission);
        let final_poll = admission.pay(0, 0);
        match (result, final_poll) {
            (Ok(id), Ok(())) => Ok(id),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }

    fn fresh_bv64_controlled(&mut self, admission: &mut Admission<'_>) -> Result<TermId> {
        if self.store_role != StoreRole::Producer {
            return Err(ControlledTermInternError::ReadOnlySnapshot);
        }
        let plan = names::scan(self, admission)?;
        let next = plan
            .candidate
            .checked_add(1)
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        // Three bounded String backings (scratch/registry/term) and their
        // headers/disposal are covered before the first owning copy.
        admission.pay(
            512,
            8 * (3 * (PREFIX.len() + 10 + size_of::<String>()) + 64),
        )?;
        let name = names::format(plan.candidate)?;
        let key = names::copy(&name)?;
        registry::reserve(self, plan.key_bytes, admission)?;
        let registry_bytes = key
            .capacity()
            .checked_add(size_of::<(TermId, Sort)>())
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        admission.pay(512, 0)?;
        self.controlled_registry_credit(registry_bytes)?;
        // A reserved identity is never rewound after any later refusal/drop.
        self.var_counter = next;
        let term = TermData::Var(name, plan.candidate);
        let sort = Sort::bitvec(64);
        let id = self.intern_controlled_validated(&term, &sort, admission)?;
        registry::probe(self, admission)?;
        admission.pay(512, 0)?;
        // reserve(1) and the complete freshness scan ensure no allocation or
        // replacement. No callback occurs between this insert and return.
        self.names.insert(key, (id, sort));
        // All scratch, including the original temporary Var String, drops
        // inside this function before the public method's terminal poll.
        Ok(id)
    }
}
