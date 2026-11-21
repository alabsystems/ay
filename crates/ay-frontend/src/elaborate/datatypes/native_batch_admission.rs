// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrow existing metadata before the native monomorphic group's scratch
//! context, signature copies, registry growth or scope-snapshot copies occur.

use std::mem::{size_of, size_of_val};

use crate::elaborate::{Context, PublicSort};
use ay_core::Sort;

enum Payload<'a> {
    Core(&'a Sort),
    Public(&'a PublicSort),
}

fn payload(root: Payload<'_>, charge: &mut dyn FnMut(usize, usize, usize) -> bool) -> bool {
    // The stack's capacity is charged before every growth. Every occurrence,
    // rather than only unique nodes, pays for the recursive Clone below.
    let mut pending = Vec::new();
    if !push(&mut pending, (root, 1), charge) {
        return false;
    }
    while let Some((value, depth)) = pending.pop() {
        if !charge(1, size_of::<Sort>() + size_of::<PublicSort>(), depth) {
            return false;
        }
        match value {
            Payload::Core(sort) => match sort {
                Sort::Bool
                | Sort::Int
                | Sort::Real
                | Sort::String
                | Sort::RegLan
                | Sort::BitVec(_)
                | Sort::FloatingPoint(..)
                | Sort::Char => {}
                Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                    if !charge(name.len().saturating_add(1), name.len(), depth) {
                        return false;
                    }
                }
                Sort::Array(array) => {
                    if !push(
                        &mut pending,
                        (Payload::Core(&array.index_sort), depth + 1),
                        charge,
                    ) || !push(
                        &mut pending,
                        (Payload::Core(&array.element_sort), depth + 1),
                        charge,
                    ) {
                        return false;
                    }
                }
                Sort::Seq(element) => {
                    if !push(&mut pending, (Payload::Core(element), depth + 1), charge) {
                        return false;
                    }
                }
                Sort::Datatype(datatype) => {
                    if !charge(
                        datatype
                            .name
                            .len()
                            .saturating_add(datatype.constructors.len()),
                        datatype.name.len(),
                        depth,
                    ) {
                        return false;
                    }
                    for constructor in &datatype.constructors {
                        if !charge(
                            constructor
                                .name
                                .len()
                                .saturating_add(constructor.fields.len()),
                            constructor
                                .name
                                .len()
                                .saturating_add(size_of_val(constructor)),
                            depth,
                        ) {
                            return false;
                        }
                        for field in &constructor.fields {
                            if !charge(
                                field.name.len().saturating_add(1),
                                field.name.len().saturating_add(size_of_val(field)),
                                depth,
                            ) || !push(
                                &mut pending,
                                (Payload::Core(&field.sort), depth + 1),
                                charge,
                            ) {
                                return false;
                            }
                        }
                    }
                }
                _ => return false,
            },
            Payload::Public(sort) => match sort {
                PublicSort::Core(sort) => {
                    if !push(&mut pending, (Payload::Core(sort), depth + 1), charge) {
                        return false;
                    }
                }
                PublicSort::Array(a, b) => {
                    if !push(&mut pending, (Payload::Public(a), depth + 1), charge)
                        || !push(&mut pending, (Payload::Public(b), depth + 1), charge)
                    {
                        return false;
                    }
                }
                PublicSort::Seq(element)
                | PublicSort::FiniteSet(element)
                | PublicSort::AmbiguousSet(element) => {
                    if !push(&mut pending, (Payload::Public(element), depth + 1), charge) {
                        return false;
                    }
                }
                PublicSort::Unknown => {}
                _ => return false,
            },
        }
    }
    true
}

fn push<T>(
    pending: &mut Vec<T>,
    value: T,
    charge: &mut dyn FnMut(usize, usize, usize) -> bool,
) -> bool {
    if pending.len() == pending.capacity() {
        let capacity = pending.capacity().saturating_mul(2).max(4);
        if !charge(pending.len(), capacity.saturating_mul(size_of::<T>()), 0)
            || pending.try_reserve_exact(capacity - pending.len()).is_err()
        {
            return false;
        }
    }
    pending.push(value);
    true
}

impl Context {
    /// Admit the existing source footprint for a monomorphic native group.
    /// This read-only resource seam grants no source/declaration authority.
    /// Schematic contexts need a separately transactional instantiation route:
    /// their ordinary refresh can fail after a declaration has committed.
    #[doc(hidden)]
    pub fn admit_native_monomorphic_datatype_group(
        &self,
        group_work: usize,
        group_storage: usize,
        new_members: usize,
        charge: &mut dyn FnMut(usize, usize, usize) -> bool,
    ) -> bool {
        if !self.parametric_sort_defs.is_empty()
            || !self.parametric_datatypes.is_empty()
            || !self.parametric_datatype_ids.is_empty()
            || !self.sort_parameters.is_empty()
            || !self.polymorphic_declarations.is_empty()
        {
            return false;
        }
        if !charge(self.scopes.len().saturating_add(1), 0, 0) {
            return false;
        }
        let scoped_capacity = self
            .scopes
            .iter()
            .map(|frame| frame.symbols.capacity())
            .fold(0usize, usize::saturating_add);
        let capacities = [
            self.sort_defs.capacity(),
            self.public_sort_defs.capacity(),
            self.symbols.capacity(),
            self.overloaded_symbols.capacity(),
            self.datatype_member_symbols.capacity(),
            self.declaration_core_identities_used.capacity(),
            self.sort_core_identities_used.capacity(),
            self.nominal_sort_surfaces.capacity(),
            self.constructors.capacity(),
            self.ctor_selectors.capacity(),
            self.ctor_selector_info.capacity(),
            self.dt_internal_surface.capacity(),
            self.datatypes.capacity(),
            self.live_datatype_carriers.capacity(),
            self.monomorphic_datatype_decs.capacity(),
            self.fun_defs.capacity(),
            scoped_capacity,
        ]
        .into_iter()
        .fold(0usize, usize::saturating_add);
        let slots = capacities
            .saturating_add(new_members.saturating_mul(8))
            .saturating_add(32);
        // Hash table moves, worst-case probes/private-name collision retries,
        // and the same new declarations retained in every assertion snapshot.
        let scope_copies = self.scopes.len().saturating_add(8);
        let multiplier = slots.saturating_mul(slots).saturating_mul(scope_copies);
        if !charge(
            capacities.saturating_mul(2),
            capacities
                .saturating_mul(4)
                .saturating_mul(size_of::<(String, super::super::SymbolInfo)>().saturating_add(1))
                .saturating_add(65_536),
            0,
        ) || !charge(
            group_work.saturating_mul(multiplier),
            group_storage
                .saturating_mul(slots)
                .saturating_mul(scope_copies)
                .saturating_mul(8),
            0,
        ) {
            return false;
        }
        for name in self
            .declaration_core_identities_used
            .iter()
            .chain(self.sort_core_identities_used.iter())
            .chain(self.nominal_sort_surfaces.keys())
            .chain(self.constructors.keys())
            .chain(self.ctor_selectors.keys())
            .chain(self.ctor_selector_info.keys())
            .chain(self.dt_internal_surface.keys())
            .chain(self.datatypes.keys())
            .chain(self.live_datatype_carriers.iter())
            .chain(self.monomorphic_datatype_decs.keys())
            .chain(self.fun_defs.keys())
        {
            // Rehashing moves retained entries but re-reads every key byte.
            if !charge(name.len().saturating_add(1).saturating_mul(slots), 0, 0) {
                return false;
            }
        }
        let copies = slots
            .saturating_mul(scope_copies)
            .saturating_mul(new_members.saturating_add(8));
        for (name, sort) in &self.sort_defs {
            if !charge(name.len().saturating_add(1), name.len(), 0)
                || !payload(Payload::Core(sort), &mut |w, b, d| {
                    charge(w.saturating_mul(copies), b.saturating_mul(copies), d)
                })
            {
                return false;
            }
        }
        for (name, sort) in &self.public_sort_defs {
            if !charge(name.len().saturating_add(1), name.len(), 0)
                || !payload(Payload::Public(sort), &mut |w, b, d| {
                    charge(w.saturating_mul(copies), b.saturating_mul(copies), d)
                })
            {
                return false;
            }
        }
        // The narrow preflight context above clones sort maps, NOT symbol
        // maps. Hash table growth moves SymbolInfo headers; it does not clone
        // every retained signature for every old slot. Native global member
        // registration clones only the affected live/snapshot primary rows,
        // at most once per incoming member in each scope. Existing overload
        // Vec growth likewise moves headers. The table-growth/header fees
        // above remain unchanged, as does the full lookup/comparison WORK
        // multiplier. Keep old-sort storage pricing separate: an input field
        // can expand the same existing sort alias at multiple occurrences.
        let signature_storage_copies = scope_copies.saturating_mul(new_members.saturating_add(8));
        let scoped_signatures = self.scopes.iter().flat_map(|frame| {
            frame.symbols.values().flat_map(|state| {
                state
                    .primary
                    .iter()
                    .chain(state.overloads.iter().flatten())
                    .map(move |info| (&state.name, info))
            })
        });
        for (name, info) in self
            .native_input_symbol_storage_iter()
            .chain(scoped_signatures)
        {
            if !charge(
                name.len()
                    .saturating_add(info.arg_sorts.len())
                    .saturating_add(info.public_arg_sorts.len())
                    .saturating_mul(copies),
                name.len()
                    .saturating_add(size_of_val(info))
                    .saturating_mul(signature_storage_copies),
                0,
            ) {
                return false;
            }
            if let Some(internal) = &info.internal_name {
                if !charge(
                    internal.len().saturating_mul(copies),
                    internal.len().saturating_mul(signature_storage_copies),
                    0,
                ) {
                    return false;
                }
            }
            if !payload(Payload::Core(&info.sort), &mut |w, b, d| {
                charge(
                    w.saturating_mul(copies),
                    b.saturating_mul(signature_storage_copies),
                    d,
                )
            }) || !payload(Payload::Public(&info.public_sort), &mut |w, b, d| {
                charge(
                    w.saturating_mul(copies),
                    b.saturating_mul(signature_storage_copies),
                    d,
                )
            }) {
                return false;
            }
            for sort in &info.arg_sorts {
                if !payload(Payload::Core(sort), &mut |w, b, d| {
                    charge(
                        w.saturating_mul(copies),
                        b.saturating_mul(signature_storage_copies),
                        d,
                    )
                }) {
                    return false;
                }
            }
            for sort in &info.public_arg_sorts {
                if !payload(Payload::Public(sort), &mut |w, b, d| {
                    charge(
                        w.saturating_mul(copies),
                        b.saturating_mul(signature_storage_copies),
                        d,
                    )
                }) {
                    return false;
                }
            }
        }
        charge(0, 0, 0)
    }
}
