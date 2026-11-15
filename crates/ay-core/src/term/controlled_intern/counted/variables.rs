// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::mem::size_of;

impl<O: TermConstructionAdmission> CountedTermBuilder<'_, '_, O> {
    /// Reuse only the exact declared name AND sort. No supplied numeric ID is
    /// admitted. Same-name/different-sort bindings remain distinct and stable
    /// during this session, even though the native names table is last-binding.
    /// A NEW session reuses only the current native binding: a hidden older
    /// sort gets a new identity, matching native redeclaration behavior. No
    /// cross-session typed-variable identity or fresh-query history independence
    /// is implied; a counted original-query converter uses one fresh session.
    pub fn variable(&mut self, name: &str, sort: &Sort) -> Result<TermId> {
        self.owner.admit(
            name.len()
                .checked_add(1)
                .ok_or_else(|| storage::work(self.owner))?,
            0,
        )?;
        sorts::visit(sort, self.owner, PayloadUse::Inspect)?;
        let hash = index::name_hash(name);
        if let Some(ids) = self.variables.get(hash, self.owner)? {
            for id in ids {
                self.owner.admit(1, 0)?;
                let entry = self
                    .store
                    .terms
                    .get(id.index())
                    .ok_or(CountedTermError::InvalidInput)?;
                if let TermData::Var(existing, _) = &entry.term {
                    self.owner.admit(
                        existing
                            .len()
                            .checked_add(name.len())
                            .ok_or_else(|| storage::work(self.owner))?,
                        0,
                    )?;
                    if existing == name && inspection::sort_equal(&entry.sort, sort, self.owner)? {
                        self.owner.check()?;
                        return Ok(*id);
                    }
                }
            }
        }
        let result = self.new_variable(hash, name, sort);
        self.owner.check()?;
        result
    }

    fn new_variable(&mut self, hash: u64, name: &str, sort: &Sort) -> Result<TermId> {
        let numeric = self.store.var_counter;
        let next = numeric
            .checked_add(1)
            .ok_or_else(|| storage::work(self.owner))?;
        let term_name = storage::text(name, self.owner)?;
        let key = storage::text(name, self.owner)?;
        let term_sort = sorts::copy(sort, self.owner)?;
        let registry_sort = sorts::copy(sort, self.owner)?;
        self.reserve_names()?;
        let registry_bytes = key
            .capacity()
            .checked_add(size_of::<(TermId, Sort)>())
            .ok_or_else(|| storage::storage(self.owner))?;
        self.store
            .controlled_registry_credit(registry_bytes)
            .map_err(|_| storage::storage(self.owner))?;
        // Identity is never rewound after a partial/refused construction.
        self.store.var_counter = next;
        let id = self.publish(TermData::Var(term_name, numeric), term_sort)?;
        self.variables.insert(hash, id, self.owner)?;
        self.owner.admit(
            name.len()
                .checked_add(1)
                .ok_or_else(|| storage::work(self.owner))?,
            0,
        )?;
        // Last-binding native compatibility; typed side-index retains both.
        let previous = self.store.names.insert(key, (id, registry_sort));
        if previous.is_none() {
            self.registry_name_bytes = self
                .registry_name_bytes
                .checked_add(name.len())
                .ok_or_else(|| storage::work(self.owner))?;
        }
        drop(previous);
        Ok(id)
    }

    fn reserve_names(&mut self) -> Result<()> {
        self.owner.admit(1, 0)?;
        if self.store.names.len() == self.store.names.capacity() {
            let old = self.store.names.allocation_size();
            let bytes = old
                .checked_mul(4)
                .and_then(|n| n.checked_add(4096))
                .ok_or_else(|| storage::storage(self.owner))?;
            let work = old
                .checked_add(self.registry_name_bytes)
                .and_then(|n| n.checked_add(self.store.names.len()))
                .ok_or_else(|| storage::work(self.owner))?;
            self.owner.admit(work, bytes)?;
        }
        self.store
            .names
            .try_reserve(1)
            .map_err(|_| storage::storage(self.owner))
    }
}
