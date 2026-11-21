// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded fresh function-name data. No frontend declaration/proof authority.

use super::{Admission, ControlledTermInternError as Error, StoreRole};
use crate::{
    kani_compat::hash_table_cost as table,
    term::{Sort, TermData, TermId, TermStore},
};

#[cfg(test)]
mod tests;

fn limit() -> Error {
    Error::ResourceLimit
}

fn different(name: &str, retained: &str, admission: &mut Admission<'_>) -> Result<bool, Error> {
    admission.pay(
        name.len()
            .checked_add(retained.len())
            .and_then(|n| n.checked_add(1))
            .ok_or_else(limit)?,
        0,
    )?;
    Ok(name != retained)
}

impl TermStore {
    /// Inspect every retained name before a source layer declares an owned
    /// function. A marker/name supplies no source or declaration authority.
    pub fn native_function_name_is_available_with_progress(
        &self,
        name: &str,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, Error> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        let result = self.available_function_name(name, &mut admission);
        admission.pay(0, 0)?;
        result
    }

    fn available_function_name(
        &self,
        name: &str,
        admission: &mut Admission<'_>,
    ) -> Result<bool, Error> {
        admission.pay(name.len().checked_add(1).ok_or_else(limit)?, 0)?;
        if self.store_role != StoreRole::Producer {
            return Err(Error::ReadOnlySnapshot);
        }
        if name.is_empty() {
            return Err(Error::InvalidInput);
        }
        admission.pay(
            table::string_lookup::<(String, ())>(
                self.declared_functions.allocation_size(),
                self.declared_functions.len(),
                name.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        if self.declared_functions.contains(name) {
            return Ok(false);
        }
        admission.pay(
            table::iteration::<(String, (TermId, Sort))>(
                self.names.allocation_size(),
                self.names.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        for retained in self.names.keys() {
            if !different(name, retained, admission)? {
                return Ok(false);
            }
        }
        admission.pay(
            table::iteration::<(String, ())>(
                self.skolem_symbols.allocation_size(),
                self.skolem_symbols.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        for retained in &self.skolem_symbols {
            if !different(name, retained, admission)? {
                return Ok(false);
            }
        }
        admission.pay(self.terms.len(), 0)?;
        for entry in &self.terms {
            match &entry.term {
                TermData::Var(retained, _) => {
                    if !different(name, retained, admission)? {
                        return Ok(false);
                    }
                }
                TermData::App(symbol, _) => {
                    if !different(name, symbol.name(), admission)? {
                        return Ok(false);
                    }
                }
                TermData::Let(bindings, _) => {
                    admission.pay(bindings.len(), 0)?;
                    for (retained, _) in bindings {
                        if !different(name, retained, admission)? {
                            return Ok(false);
                        }
                    }
                }
                TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
                    admission.pay(bindings.len(), 0)?;
                    for (retained, _) in bindings {
                        if !different(name, retained, admission)? {
                            return Ok(false);
                        }
                    }
                }
                TermData::Const(_) | TermData::Not(_) | TermData::Ite(..) => {}
            }
        }
        Ok(true)
    }

    /// Reserve a previously unused exact identity in the existing declared-UF
    /// metadata. Source registration remains the frontend's separate job. All
    /// allocations/probes precede the final callback; no callback follows the
    /// committed marker. Refusal may retain capacity, never a source binding.
    pub fn try_register_new_function_name_with_progress(
        &mut self,
        name: &str,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), Error> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        if !self.available_function_name(name, &mut admission)? {
            return Err(Error::InvalidInput);
        }
        let cost = table::reserve_one::<(String, ())>(
            self.declared_functions.allocation_size(),
            self.declared_functions.len(),
            self.declared_functions.capacity(),
        )
        .ok_or_else(limit)?;
        admission.pay(cost.work, cost.storage_bytes)?;
        if cost.rehashes {
            admission.pay(
                table::iteration::<(String, ())>(
                    self.declared_functions.allocation_size(),
                    self.declared_functions.len(),
                )
                .ok_or_else(limit)?,
                0,
            )?;
            for retained in &self.declared_functions {
                admission.pay(
                    table::string_hash_payload(retained.len()).ok_or_else(limit)?,
                    0,
                )?;
            }
        }
        self.declared_functions
            .try_reserve(1)
            .map_err(|_| limit())?;
        admission.pay(name.len().checked_add(1).ok_or_else(limit)?, name.len())?;
        let mut owned = String::new();
        owned.try_reserve_exact(name.len()).map_err(|_| limit())?;
        owned.push_str(name);
        admission.pay(
            table::string_lookup::<(String, ())>(
                self.declared_functions.allocation_size(),
                self.declared_functions.len(),
                name.len(),
            )
            .ok_or_else(limit)?,
            0,
        )?;
        admission.pay(0, 0)?;
        self.controlled_registry_credit(owned.capacity())?;
        self.declared_functions.insert(owned);
        Ok(())
    }
}
