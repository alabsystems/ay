// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Atomic nonadopting native function registration under the caller's owner.

use super::super::{Context, DeclarationId, DeclarationKind, SymbolBindingOrigin, SymbolInfo};
use super::native_owned_constant::{
    resources::{self, Gate},
    NativeOwnedConstantError as Error,
};
use ay_core::{kani_compat::hash_table_cost as table, Sort};
use std::mem::size_of;

type Result<T> = std::result::Result<T, Error>;

impl Context {
    /// Price the actual context lookups used by the public live-sort adapter
    /// BEFORE it copies any resolved nominal payload. No sort/source grant is
    /// produced by this preflight; the adapter still authenticates ownership.
    #[doc(hidden)]
    pub fn admit_native_function_sort_context_with_progress(
        &self,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize, usize) -> bool,
    ) -> Result<()> {
        self.native_function_sort_context(sort, &mut Gate::new(progress), 1)
    }

    fn native_function_sort_context(
        &self,
        sort: &Sort,
        gate: &mut Gate<'_>,
        depth: usize,
    ) -> Result<()> {
        gate.pay(1, 0, depth)?;
        let name = match sort {
            Sort::Uninterpreted(name) => Some(name.as_str()),
            Sort::Datatype(data) => Some(data.name.as_str()),
            Sort::Array(array) => {
                self.native_function_sort_context(&array.index_sort, gate, depth + 1)?;
                self.native_function_sort_context(&array.element_sort, gate, depth + 1)?;
                None
            }
            Sort::Seq(element) => {
                self.native_function_sort_context(element, gate, depth + 1)?;
                None
            }
            _ => None,
        };
        if let Some(name) = name {
            let lookup = table::string_lookup::<(String, Sort)>(
                self.sort_defs.allocation_size(),
                self.sort_defs.len(),
                name.len(),
            )
            .ok_or(Error::ResourceLimit)?;
            let scan = table::iteration::<(String, Sort)>(
                self.sort_defs.allocation_size(),
                self.sort_defs.len(),
            )
            .ok_or(Error::ResourceLimit)?;
            gate.pay(
                lookup
                    .checked_mul(4)
                    .and_then(|n| n.checked_add(scan.checked_mul(2)?))
                    .ok_or(Error::ResourceLimit)?,
                0,
                depth,
            )?;
            let mut found = self.sort_defs.get(name);
            for live in self.sort_defs.values() {
                gate.pay(name.len().saturating_add(1).saturating_mul(2), 0, depth)?;
                if found.is_none() && matches!(live, Sort::Uninterpreted(core) if core == name) {
                    found = Some(live);
                }
            }
            if let Some(Sort::Uninterpreted(core)) = found {
                let lookup = table::string_lookup::<(String, Vec<String>)>(
                    self.datatypes.allocation_size(),
                    self.datatypes.len(),
                    core.len(),
                )
                .ok_or(Error::ResourceLimit)?
                .checked_add(
                    table::string_lookup::<(String, ())>(
                        self.live_datatype_carriers.allocation_size(),
                        self.live_datatype_carriers.len(),
                        core.len(),
                    )
                    .ok_or(Error::ResourceLimit)?,
                )
                .ok_or(Error::ResourceLimit)?;
                gate.pay(lookup.checked_mul(4).ok_or(Error::ResourceLimit)?, 0, depth)?;
            }
        }
        Ok(())
    }

    /// Register one exact new engine signature globally to assertion scopes.
    /// Both caller source/engine sorts and API/event copies must already be
    /// admitted. This retains the existing native constant-backed shape for
    /// zero arity, and never adopts a constructor, alias or old signature.
    /// No callback/allocation follows the last core/frontend fence.
    #[doc(hidden)]
    pub fn try_register_native_owned_function_with_progress(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: &Sort,
        progress: &mut dyn FnMut(usize, usize, usize) -> bool,
    ) -> Result<DeclarationId> {
        let mut gate = Gate::new(progress);
        let checks = super::super::RESERVED_OP_NAMES
            .len()
            .saturating_mul(2)
            .saturating_add(super::super::EXCLUDED_DECLARABLE_OP_NAMES.len())
            .saturating_add(super::super::INTERNAL_NAMESPACES.len().saturating_mul(2))
            .saturating_add(128);
        gate.pay(name.len().saturating_add(1).saturating_mul(checks), 0, 0)?;
        if name.is_empty()
            || ay_core::is_smtlib_reserved_word(name)
            || super::super::is_reserved_symbol(name)
            || super::super::is_builtin_operator_name(name)
        {
            return Err(Error::InvalidName);
        }
        self.admit_owned_constant_name(name, &mut gate)?;
        // This explicit metered scan also covers engine-only Vars, raw Apps,
        // lexical binders and retained Skolem/function names absent from Context.
        let available = self
            .terms
            .native_function_name_is_available_with_progress(name, &mut |w, b| {
                gate.pay(w, b, 0).is_ok()
            })
            .map_err(|error| match error {
                ay_core::term::ControlledTermInternError::ResourceLimit => Error::ResourceLimit,
                _ => Error::Occupied,
            })?;
        if !available {
            return Err(Error::Occupied);
        }
        // Actual lowerings were checked through the public adapter. Repeat
        // exact ENGINE ownership admission, with table-layout prices for every
        // borrowed lookup and scan before source copies.
        for sort in domain.iter().chain(std::iter::once(range)) {
            self.native_function_sort_context(sort, &mut gate, 1)?;
            resources::admit_sort(self, sort, &mut gate, 1)?;
        }
        resources::reserve_map(&mut self.symbols, &mut gate)?;
        resources::reserve_set(&mut self.declaration_core_identities_used, &mut gate)?;
        let key = resources::copy_text(name, &mut gate)?;
        let reservation = resources::copy_text(name, &mut gate)?;
        gate.pay(
            domain.len(),
            domain
                .len()
                .checked_mul(size_of::<Sort>())
                .and_then(|n| {
                    n.checked_add(
                        domain
                            .len()
                            .checked_mul(size_of::<super::super::PublicSort>())?,
                    )
                })
                .ok_or(Error::ResourceLimit)?,
            0,
        )?;
        let mut arguments = Vec::new();
        let mut public_arguments = Vec::new();
        arguments
            .try_reserve_exact(domain.len())
            .map_err(|_| Error::ResourceLimit)?;
        public_arguments
            .try_reserve_exact(domain.len())
            .map_err(|_| Error::ResourceLimit)?;
        for sort in domain {
            arguments.push(resources::copy_sort(sort, &mut gate, 1)?);
            public_arguments.push(resources::copy_public_sort(sort, &mut gate, 1)?);
        }
        let result = resources::copy_sort(range, &mut gate, 1)?;
        let public_result = resources::copy_public_sort(range, &mut gate, 1)?;
        gate.pay(8, size_of::<SymbolInfo>().saturating_add(128), 0)?;
        let mut info = SymbolInfo::fresh_with_binding_origin(
            None,
            result,
            arguments,
            public_result,
            public_arguments,
            None,
            DeclarationKind::Uninterpreted,
            SymbolBindingOrigin::NativeApiDeclaration,
        );
        let identity = info.declaration_id().clone();
        resources::admit_macro_invalidation(self, &mut gate)?;
        resources::probe_map(&self.symbols, name, &mut gate)?;
        resources::probe_set(&self.declaration_core_identities_used, name, &mut gate)?;
        if domain.is_empty() {
            info.term = Some(
                self.terms
                    .try_fresh_owned_named_var_with_progress(name, range, &mut |w, b| {
                        gate.pay(w, b, 0).is_ok()
                    })
                    .map_err(|error| match error {
                        ay_core::term::ControlledTermInternError::ResourceLimit => {
                            Error::ResourceLimit
                        }
                        _ => Error::Occupied,
                    })?,
            );
            gate.pay(0, 0, 0)?;
        } else {
            self.terms
                .try_register_new_function_name_with_progress(name, &mut |w, b| {
                    gate.pay(w, b, 0).is_ok()
                })
                .map_err(|error| match error {
                    ay_core::term::ControlledTermInternError::ResourceLimit => Error::ResourceLimit,
                    _ => Error::Occupied,
                })?;
        }
        // All source/API map and event capacities/copies precede this fence;
        // registration itself creates no law, assumption or member fact.
        self.advance_source_revision();
        self.declaration_core_identities_used.insert(reservation);
        self.symbols.insert(key, info);
        Ok(identity)
    }
}
