// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controlled allocation AND registration of one nonadopting native constant.

use super::super::{Context, DeclarationKind, PublicSort, SymbolBindingOrigin, SymbolInfo};
use ay_core::{Sort, TermId};
use std::mem::size_of;

pub(in crate::elaborate::commands) mod resources;
use resources::{copy_public_sort, copy_sort, copy_text, Gate};

/// Allocation-free refusal; a caller keeps its original resource diagnostic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeOwnedConstantError {
    /// The original callback refused work, storage, depth or cancellation.
    ResourceLimit,
    /// The supplied declaration identity already denotes a retained object.
    Occupied,
    /// A reserved or empty declaration identity is not an owned source name.
    InvalidName,
    /// An unsupported or currently unowned engine sort was requested.
    UnsupportedSort,
}

type Result<T> = std::result::Result<T, NativeOwnedConstantError>;

impl Context {
    /// Paid availability inspection for DATA freshness, not a declaration or
    /// source grant. A frontend function can exist before any core App does.
    #[doc(hidden)]
    pub fn native_fresh_data_name_is_available_with_progress(
        &self,
        name: &str,
        progress: &mut dyn FnMut(usize, usize, usize) -> bool,
    ) -> Result<bool> {
        match self.admit_owned_constant_name(name, &mut Gate::new(progress)) {
            Ok(()) => Ok(true),
            Err(NativeOwnedConstantError::Occupied) => Ok(false),
            Err(error) => Err(error),
        }
    }

    /// Allocate and register a genuinely new native Var through ONE caller
    /// owner. Accepts exact current ENGINE sorts, never a supplied term, alias
    /// or zero-arity App. Only this coherent construction earns native source
    /// provenance. Native declarations remain global to assertion scopes.
    ///
    /// The callback must retain its own sticky limits/deadline/interrupt. This
    /// method creates none. Reservations/serials/inert core entries may remain
    /// on refusal, but no source binding or handle is published. The final
    /// admission fence follows all owned copies and precedes an allocation-free
    /// source commit. Existing cache invalidation/destruction is not a new
    /// source-copy operation or an allocator/RSS timing guarantee.
    #[doc(hidden)]
    pub fn try_register_native_owned_constant_with_progress(
        &mut self,
        name: &str,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize, usize) -> bool,
    ) -> Result<TermId> {
        let mut gate = Gate::new(progress);
        let name_checks = super::super::RESERVED_OP_NAMES
            .len()
            .saturating_mul(2)
            .saturating_add(super::super::EXCLUDED_DECLARABLE_OP_NAMES.len())
            .saturating_add(super::super::INTERNAL_NAMESPACES.len().saturating_mul(2))
            .saturating_add(128);
        gate.pay(
            name.len().saturating_add(1).saturating_mul(name_checks),
            0,
            0,
        )?;
        if name.is_empty()
            || ay_core::is_smtlib_reserved_word(name)
            || super::super::is_reserved_symbol(name)
            || super::super::is_builtin_operator_name(name)
        {
            return Err(NativeOwnedConstantError::InvalidName);
        }
        resources::admit_sort(self, sort, &mut gate, 1)?;
        self.admit_owned_constant_name(name, &mut gate)?;

        // Price the actual two affected maps only. No whole-context clone or
        // datatype-group N² footprint is used for a constant declaration.
        resources::reserve_map(&mut self.symbols, &mut gate)?;
        resources::reserve_set(&mut self.declaration_core_identities_used, &mut gate)?;
        let key = copy_text(name, &mut gate)?;
        let reservation = copy_text(name, &mut gate)?;
        let engine = copy_sort(sort, &mut gate, 1)?;
        gate.pay(8, size_of::<SymbolInfo>().saturating_add(128), 0)?;
        let public_sort = copy_public_sort(sort, &mut gate, 1)?;
        let mut info = SymbolInfo::fresh_with_binding_origin(
            None,
            engine,
            Vec::new(),
            public_sort,
            Vec::new(),
            None,
            DeclarationKind::Uninterpreted,
            SymbolBindingOrigin::NativeApiDeclaration,
        );
        // Prepay sparse macro-cache disposal/lookup data, not repeated symbol
        // definitions or scope snapshots. No cache value is cloned.
        resources::admit_macro_invalidation(self, &mut gate)?;
        let term = self
            .terms
            .try_fresh_owned_named_var_with_progress(name, sort, &mut |w, b| {
                gate.pay(w, b, 0).is_ok()
            })
            .map_err(|error| match error {
                ay_core::term::ControlledTermInternError::InvalidInput => {
                    NativeOwnedConstantError::Occupied
                }
                ay_core::term::ControlledTermInternError::UnsupportedFragment
                | ay_core::term::ControlledTermInternError::ReadOnlySnapshot => {
                    NativeOwnedConstantError::UnsupportedSort
                }
                _ => NativeOwnedConstantError::ResourceLimit,
            })?;
        info.term = Some(term);
        // All hashes/probes, capacity and copies were admitted before this
        // fence. The exclusive Context borrow prevents source rebinding.
        resources::probe_map(&self.symbols, name, &mut gate)?;
        resources::probe_set(&self.declaration_core_identities_used, name, &mut gate)?;
        gate.pay(0, 0, 0)?;
        self.advance_source_revision();
        self.declaration_core_identities_used.insert(reservation);
        self.symbols.insert(key, info);
        // No frame has this identity (verified below), so pop cannot delete or
        // restore over it. No saved SymbolInfo is adopted or silently cloned.
        Ok(term)
    }

    pub(in crate::elaborate::commands) fn admit_owned_constant_name(
        &self,
        name: &str,
        gate: &mut Gate<'_>,
    ) -> Result<()> {
        macro_rules! absent {
            ($table:expr) => {{
                let table = &$table;
                resources::probe_map(table, name, gate)?;
                if table.contains_key(name) {
                    return Err(NativeOwnedConstantError::Occupied);
                }
            }};
        }
        macro_rules! absent_set {
            ($table:expr) => {{
                let table = &$table;
                resources::probe_set(table, name, gate)?;
                if table.contains(name) {
                    return Err(NativeOwnedConstantError::Occupied);
                }
            }};
        }
        absent!(self.symbols);
        absent!(self.overloaded_symbols);
        absent!(self.datatype_member_symbols);
        absent!(self.fun_defs);
        absent!(self.adopted_macro_interps);
        absent!(self.adopted_macro_declaration_ids);
        absent!(self.constructors);
        absent!(self.dt_internal_surface);
        absent!(self.sort_defs);
        absent!(self.public_sort_defs);
        absent!(self.parametric_sort_defs);
        absent!(self.parametric_datatypes);
        absent!(self.datatypes);
        absent!(self.monomorphic_datatype_decs);
        absent!(self.parametric_datatype_ids);
        absent!(self.parametric_instance_args);
        absent!(self.nominal_sort_surfaces);
        absent!(self.nullary_ctor_terms);
        absent!(self.ctor_selectors);
        absent!(self.ctor_selector_info);
        absent!(self.named_terms);
        absent_set!(self.internal_symbols);
        absent_set!(self.recursive_fun_names);
        absent_set!(self.live_datatype_carriers);
        absent_set!(self.map_sort_synonyms);
        absent_set!(self.sort_parameters);
        absent_set!(self.declaration_core_identities_used);
        absent_set!(self.sort_core_identities_used);
        // Schematic families can have NO monomorphic symbol or core App yet.
        // Inspect only borrowed names and physical edges, before any copy.
        gate.pay(self.polymorphic_declarations.len(), 0, 0)?;
        for declaration in &self.polymorphic_declarations {
            gate.pay(
                declaration
                    .name
                    .len()
                    .saturating_add(name.len())
                    .saturating_add(1),
                0,
                0,
            )?;
            if declaration.name == name {
                return Err(NativeOwnedConstantError::Occupied);
            }
        }
        gate.pay(self.parametric_datatypes.allocation_size(), 0, 0)?;
        for declaration in self.parametric_datatypes.values() {
            gate.pay(declaration.constructors.len(), 0, 0)?;
            for constructor in &declaration.constructors {
                gate.pay(
                    constructor
                        .name
                        .len()
                        .saturating_add(name.len())
                        .saturating_add(4),
                    0,
                    0,
                )?;
                if constructor.name == name
                    || name.strip_prefix("is-") == Some(constructor.name.as_str())
                {
                    return Err(NativeOwnedConstantError::Occupied);
                }
                gate.pay(constructor.selectors.len(), 0, 0)?;
                for selector in &constructor.selectors {
                    gate.pay(
                        selector
                            .name
                            .len()
                            .saturating_add(name.len())
                            .saturating_add(1),
                        0,
                        0,
                    )?;
                    if selector.name == name {
                        return Err(NativeOwnedConstantError::Occupied);
                    }
                }
            }
        }
        // Even an empty saved binding is occupation: a global declaration must
        // not fill/adopt it and later be restored away by assertion pop.
        gate.pay(self.scopes.len(), 0, 0)?;
        for frame in &self.scopes {
            absent!(frame.symbols);
            gate.pay(
                frame
                    .named_terms
                    .len()
                    .saturating_add(frame.polymorphic_declarations.len())
                    .saturating_add(frame.fun_defs.len())
                    .saturating_add(frame.constructors.len())
                    .saturating_add(frame.sort_defs.len())
                    .saturating_add(frame.parametric_datatypes.len()),
                0,
                0,
            )?;
            for declaration in frame
                .named_terms
                .iter()
                .chain(&frame.polymorphic_declarations)
                .chain(&frame.fun_defs)
                .chain(&frame.constructors)
                .chain(&frame.sort_defs)
                .chain(&frame.parametric_datatypes)
            {
                gate.pay(
                    declaration
                        .len()
                        .saturating_add(name.len())
                        .saturating_add(1),
                    0,
                    0,
                )?;
                if declaration == name {
                    return Err(NativeOwnedConstantError::Occupied);
                }
            }
            gate.pay(frame.datatypes.len(), 0, 0)?;
            for (core, surface) in &frame.datatypes {
                gate.pay(
                    core.len()
                        .saturating_add(surface.len())
                        .saturating_add(name.len())
                        .saturating_add(2),
                    0,
                    0,
                )?;
                if core == name || surface == name {
                    return Err(NativeOwnedConstantError::Occupied);
                }
            }
        }
        Ok(())
    }
}
