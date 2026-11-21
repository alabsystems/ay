// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Caller-owned metering for a newly minted typed Skolem choice definition.

use super::{shape, Admission, ControlledTermInternError, Result, StoreRole};
use crate::kani_compat::hash_table_cost as table;
use crate::{SkolemChoice, Sort, TermData, TermId, TermStore};
use std::mem::size_of;

#[cfg(test)]
mod tests;

fn limit() -> ControlledTermInternError {
    ControlledTermInternError::ResourceLimit
}

impl TermStore {
    /// Register a NEW Skolem constant and its exact typed choice definition.
    ///
    /// The caller must be the actual fresh-choice producer, or must have
    /// independently authenticated substitution, full-original freshness and
    /// dependency provenance. Like `mark_skolem_symbol`, this changes checker
    /// metadata; it does not prove a source assertion or grant a model value.
    /// The ordinary checker still authenticates the finished proof.
    ///
    /// No existing registration is adopted/overwritten. Actual table geometry,
    /// moved-key hashing, borrowed sort/name copies and reservations are paid
    /// before use under the caller's SAME cumulative owner. No budget is made
    /// here. Inert reservations, or the coherent new registration if the final
    /// cancellation fence refuses, may remain; no success escapes that fence.
    pub fn try_register_new_skolem_choice_with_progress(
        &mut self,
        witness: TermId,
        binder: &str,
        sort: &Sort,
        body: TermId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<(), ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = self.register_new_choice(witness, binder, sort, body, &mut admission);
        let terminal = admission.pay(0, 0);
        match (result, terminal) {
            (Ok(()), Ok(())) => Ok(()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }

    fn register_new_choice(
        &mut self,
        witness: TermId,
        binder: &str,
        sort: &Sort,
        body: TermId,
        admission: &mut Admission<'_>,
    ) -> Result<()> {
        if self.store_role != StoreRole::Producer {
            return Err(ControlledTermInternError::ReadOnlySnapshot);
        }
        admission.pay(2, 0)?;
        if self.entry_stamp(witness).is_none() || self.entry_stamp(body).is_none() {
            return Err(ControlledTermInternError::InvalidInput);
        }
        let TermData::Var(name, _) = self.get(witness) else {
            return Err(ControlledTermInternError::InvalidInput);
        };
        if binder.is_empty() || self.sort(body) != &Sort::Bool {
            return Err(ControlledTermInternError::InvalidInput);
        }
        let expected = shape::admit_owned_sort(sort, admission)?;
        let actual = shape::admit_owned_sort(self.sort(witness), admission)?;
        admission.pay(expected.work.checked_add(actual.work).ok_or_else(limit)?, 0)?;
        if self.sort(witness) != sort {
            return Err(ControlledTermInternError::InvalidInput);
        }
        admission.pay(
            table::string_lookup::<(String, ())>(
                self.skolem_symbols.allocation_size(),
                self.skolem_symbols.len(),
                name.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        admission.pay(
            table::fixed_lookup::<(TermId, SkolemChoice)>(
                self.skolem_choice.allocation_size(),
                self.skolem_choice.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        if self.skolem_symbols.contains(name) || self.skolem_choice.contains_key(&witness) {
            return Err(ControlledTermInternError::InvalidInput);
        }
        let generation = self
            .checker_visible_metadata_generation
            .checked_add(2)
            .ok_or_else(limit)?;
        admission.pay(
            name.len()
                .checked_add(binder.len())
                .and_then(|n| n.checked_add(expected.work))
                .ok_or_else(limit)?,
            name.len()
                .checked_add(binder.len())
                .and_then(|n| n.checked_add(expected.bytes))
                .and_then(|n| n.checked_add(size_of::<SkolemChoice>()))
                .ok_or_else(limit)?,
        )?;
        let name = copy_name(name)?;
        let choice = SkolemChoice {
            binder: copy_name(binder)?,
            sort: sort.clone(),
            body,
        };
        let symbols = table::reserve_one::<(String, ())>(
            self.skolem_symbols.allocation_size(),
            self.skolem_symbols.len(),
            self.skolem_symbols.capacity(),
        )
        .ok_or_else(limit)?;
        admission.pay(symbols.work, symbols.storage_bytes)?;
        if symbols.rehashes {
            admission.pay(
                table::iteration::<(String, ())>(
                    self.skolem_symbols.allocation_size(),
                    self.skolem_symbols.len(),
                )
                .ok_or_else(limit)?,
                0,
            )?;
            for key in &self.skolem_symbols {
                admission.pay(table::string_hash_payload(key.len()).ok_or_else(limit)?, 0)?;
            }
        }
        let choices = table::reserve_one::<(TermId, SkolemChoice)>(
            self.skolem_choice.allocation_size(),
            self.skolem_choice.len(),
            self.skolem_choice.capacity(),
        )
        .ok_or_else(limit)?;
        admission.pay(choices.work, choices.storage_bytes)?;
        self.true_memory_cache.set(0);
        self.skolem_symbols.try_reserve(1).map_err(|_| limit())?;
        self.skolem_choice.try_reserve(1).map_err(|_| limit())?;
        // Both actual insert probes are distinct from the earlier occupied
        // checks and may observe the newly reserved backing geometry.
        admission.pay(
            table::string_lookup::<(String, ())>(
                self.skolem_symbols.allocation_size(),
                self.skolem_symbols.len(),
                name.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        admission.pay(
            table::fixed_lookup::<(TermId, SkolemChoice)>(
                self.skolem_choice.allocation_size(),
                self.skolem_choice.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        admission.pay(0, 0)?;
        self.skolem_symbols.insert(name);
        self.skolem_choice.insert(witness, choice);
        self.checker_visible_metadata_generation = generation;
        Ok(())
    }
}

fn copy_name(name: &str) -> Result<String> {
    let mut owned = String::new();
    owned.try_reserve_exact(name.len()).map_err(|_| limit())?;
    owned.push_str(name);
    Ok(owned)
}
