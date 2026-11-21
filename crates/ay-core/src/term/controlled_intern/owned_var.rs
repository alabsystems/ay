// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fresh producer DATA with caller-owned names, never declaration authority.

use super::{fresh::registry, shape, Admission, ControlledTermInternError, Result, StoreRole};
use crate::term::{Sort, TermData, TermId, TermStore};
use std::mem::size_of;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
enum Name<'a> {
    Prefix(&'a str),
    Exact(&'a str),
}

fn limit() -> ControlledTermInternError {
    ControlledTermInternError::ResourceLimit
}

impl TermStore {
    /// Construct a fresh variable without declaring a source/model symbol.
    ///
    /// The nonwrapping serial is above all retained Var IDs and all matching
    /// names, including raw applications and lexical binder lists. This scans
    /// the SAME producer arena, never creates a resource owner, and prices raw
    /// names, physical sorts, collisions and reservations before copies/work.
    /// Reservations, consumed serials and inert entries can remain on refusal;
    /// a terminal cancellation never returns a handle. No source or proof
    /// authority is created. Public arbitrary-Var interning remains refused.
    pub fn try_fresh_var_with_progress(
        &mut self,
        prefix: &str,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, ControlledTermInternError> {
        self.owned_var_with_progress(Name::Prefix(prefix), sort, progress)
    }

    /// Construct a fresh numeric Var under an EXACT previously unused name.
    /// This context-free operation is data freshness only: its caller must
    /// independently register and authenticate any source declaration.
    pub fn try_fresh_owned_named_var_with_progress(
        &mut self,
        name: &str,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, ControlledTermInternError> {
        self.owned_var_with_progress(Name::Exact(name), sort, progress)
    }

    fn owned_var_with_progress(
        &mut self,
        name: Name<'_>,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<TermId> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = self.owned_var(name, sort, &mut admission);
        // All temporary names/sorts have dropped before this terminal fence.
        let terminal = admission.pay(0, 0);
        match (result, terminal) {
            (Ok(id), Ok(())) => Ok(id),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }

    fn owned_var(
        &mut self,
        requested: Name<'_>,
        sort: &Sort,
        admission: &mut Admission<'_>,
    ) -> Result<TermId> {
        if self.store_role != StoreRole::Producer {
            return Err(ControlledTermInternError::ReadOnlySnapshot);
        }
        let mut cost = shape::admit_owned_sort(sort, admission)?;
        let mut serial = self.var_counter;
        let mut key_bytes = 0usize;
        // Raw allocated buckets, not live length: sparse/tombstone scans count.
        registry::probe(self, admission)?;
        for name in self.names.keys() {
            key_bytes = key_bytes
                .checked_add(name.len())
                .and_then(|n| n.checked_add(1))
                .ok_or_else(limit)?;
            inspect_name(requested, name, &mut serial, admission)?;
        }
        // A registered Skolem identity can exist before a corresponding App
        // or Var. Fresh data must not inherit that checker-visible provenance.
        admission.pay(self.skolem_symbols.allocation_size(), 0)?;
        for name in &self.skolem_symbols {
            inspect_name(requested, name, &mut serial, admission)?;
        }
        for entry in &self.terms {
            admission.pay(1, 0)?;
            match &entry.term {
                TermData::Var(name, id) => {
                    serial = serial.max(id.checked_add(1).ok_or_else(limit)?);
                    inspect_name(requested, name, &mut serial, admission)?;
                }
                TermData::App(symbol, _) => {
                    inspect_name(requested, symbol.name(), &mut serial, admission)?;
                }
                TermData::Let(bindings, _) => {
                    admission.pay(bindings.len(), 0)?;
                    for (name, _) in bindings {
                        inspect_name(requested, name, &mut serial, admission)?;
                    }
                }
                TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
                    admission.pay(bindings.len(), 0)?;
                    for (name, _) in bindings {
                        inspect_name(requested, name, &mut serial, admission)?;
                    }
                }
                TermData::Const(_) | TermData::Not(_) | TermData::Ite(..) => {}
            }
        }
        let next = serial.checked_add(1).ok_or_else(limit)?;
        let base = match requested {
            Name::Prefix(prefix) | Name::Exact(prefix) => prefix,
        };
        let width = base.len().checked_add(11).ok_or_else(limit)?;
        // Names: formatted scratch, registry key, interned Var, disposal.
        // Sort: names registry plus the separately priced term-store copy.
        admission.pay(
            width
                .checked_mul(8)
                .and_then(|w| w.checked_add(cost.work.checked_mul(2)?))
                .ok_or_else(limit)?,
            width
                .checked_add(size_of::<String>())
                .and_then(|b| b.checked_mul(8))
                .and_then(|b| b.checked_add(cost.bytes.checked_mul(2)?))
                .ok_or_else(limit)?,
        )?;
        let name = format_name(requested, serial, width)?;
        let key = copy_text(&name)?;
        let registry_sort = sort.clone();
        registry::reserve(self, key_bytes, admission)?;
        let bytes = key
            .capacity()
            .checked_add(size_of::<(TermId, Sort)>())
            .and_then(|b| b.checked_add(cost.bytes.saturating_sub(size_of::<Sort>())))
            .ok_or_else(limit)?;
        self.controlled_registry_credit(bytes)?;
        // Dynamic name hashing and equality/copy pricing precedes the common
        // controlled interner, whose fixed fee alone would not cover this name.
        admission.pay(name.len().checked_add(1).ok_or_else(limit)?, 0)?;
        cost.work = cost.work.checked_add(name.len()).ok_or_else(limit)?;
        cost.bytes = cost.bytes.checked_add(name.len()).ok_or_else(limit)?;
        self.var_counter = next;
        let term = TermData::Var(name, serial);
        let id = self.intern_controlled_validated(&term, sort, Some(&cost), admission)?;
        registry::insert_probe(self, &key, admission)?;
        // All allocation and original-name scans precede this coherent insert.
        self.names.insert(key, (id, registry_sort));
        Ok(id)
    }
}

fn inspect_name(
    requested: Name<'_>,
    existing: &str,
    serial: &mut u32,
    admission: &mut Admission<'_>,
) -> Result<()> {
    let base = match requested {
        Name::Prefix(prefix) | Name::Exact(prefix) => prefix,
    };
    admission.pay(
        existing
            .len()
            .checked_add(base.len())
            .and_then(|n| n.checked_add(1))
            .ok_or_else(limit)?,
        0,
    )?;
    match requested {
        Name::Exact(name) => {
            if name.is_empty() || name == existing {
                return Err(ControlledTermInternError::InvalidInput);
            }
        }
        Name::Prefix(prefix) => {
            if let Some(suffix) = existing
                .strip_prefix(prefix)
                .and_then(|s| s.strip_prefix('_'))
            {
                if !suffix.is_empty()
                    && suffix.len() <= 10
                    && suffix.bytes().all(|byte| byte.is_ascii_digit())
                {
                    if let Ok(value) = suffix.parse::<u32>() {
                        *serial = (*serial).max(value.checked_add(1).ok_or_else(limit)?);
                    }
                }
            }
        }
    }
    Ok(())
}

fn copy_text(text: &str) -> Result<String> {
    let mut copy = String::new();
    copy.try_reserve_exact(text.len()).map_err(|_| limit())?;
    copy.push_str(text);
    Ok(copy)
}

fn format_name(name: Name<'_>, serial: u32, width: usize) -> Result<String> {
    use std::fmt::Write;
    let base = match name {
        Name::Prefix(prefix) | Name::Exact(prefix) => prefix,
    };
    if matches!(name, Name::Exact("")) {
        return Err(ControlledTermInternError::InvalidInput);
    }
    let mut result = String::new();
    result.try_reserve_exact(width).map_err(|_| limit())?;
    result.push_str(base);
    if matches!(name, Name::Prefix(_)) {
        write!(&mut result, "_{serial}").map_err(|_| limit())?;
    }
    Ok(result)
}
