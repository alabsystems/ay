// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource-only accounting for the existing positive projection lookup.

use super::{Context, DeclarationId, SymbolInfo};
use ay_core::kani_compat::hash_table_cost as table;

/// A prepaid physical lookup envelope. This is neither a source binding nor a
/// declaration receipt; only the existing declaration checker grants either.
#[derive(Clone, Copy, Debug)]
pub struct ProjectionLookupFootprint {
    geometry: [usize; 8],
    work: usize,
}

impl ProjectionLookupFootprint {
    /// Work already debited by the producing progress callback. A consumer
    /// repeating the lookup must debit its same original owner again.
    #[must_use]
    pub fn work(&self) -> usize {
        self.work
    }

    /// Allocation geometry only. Semantic/source currency is separate.
    #[must_use]
    pub fn matches_storage(&self, context: &Context) -> bool {
        self.geometry == geometry(context)
    }
}

fn geometry(context: &Context) -> [usize; 8] {
    [
        context.symbols.allocation_size(),
        context.symbols.len(),
        context.overloaded_symbols.allocation_size(),
        context.overloaded_symbols.len(),
        context.adopted_macro_declaration_ids.allocation_size(),
        context.adopted_macro_declaration_ids.len(),
        context.internal_symbols.allocation_size(),
        context.internal_symbols.len(),
    ]
}

impl Context {
    /// Debit actual sparse backing scans, small-table mirrors, physical
    /// overload-vector visits and String hashes BEFORE the existing projection
    /// checker performs its scans/copies. Payload/type validity remains owed.
    /// No allowance, stop owner or source authority is created here.
    pub fn admit_projection_lookup_work_with_progress(
        &self,
        incoming_bytes: usize,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<ProjectionLookupFootprint> {
        let original = geometry(self);
        let mut work = 0usize;
        let mut pay = |amount: usize| {
            let next = work.checked_add(amount)?;
            if !progress(amount, 0) {
                return None;
            }
            work = next;
            Some(())
        };
        // Several exact-identity/kind checks traverse the semantic iterator.
        // Four complete scans bound that existing fixed lookup sequence.
        let scans = table::iteration::<(String, SymbolInfo)>(original[0], original[1])?
            .checked_add(table::iteration::<(String, Vec<SymbolInfo>)>(
                original[2],
                original[3],
            )?)?
            .checked_add(table::iteration::<(String, DeclarationId)>(
                original[4],
                original[5],
            )?)?;
        pay(scans.checked_mul(4)?)?;
        let mut widest = incoming_bytes;
        for (surface, info) in &self.symbols {
            widest = widest.max(surface.len());
            let identity = self.symbol_identity_name(surface, info);
            let name_work = surface
                .len()
                .checked_add(identity.len())?
                .checked_add(incoming_bytes)?
                .checked_add(1)?;
            let lookup = table::string_lookup::<(String, Vec<SymbolInfo>)>(
                original[2],
                original[3],
                surface.len(),
            )?;
            pay(name_work.checked_add(lookup)?.checked_mul(4)?)?;
        }
        for (surface, infos) in &self.overloaded_symbols {
            widest = widest.max(surface.len());
            // Admit the physical vector BEFORE visiting any member, even if
            // every signature has identical strings and no selected match.
            pay(infos.len().checked_mul(4)?.checked_add(surface.len())?)?;
            for info in infos {
                let identity = self.symbol_identity_name(surface, info);
                let bytes = identity
                    .len()
                    .checked_add(surface.len())?
                    .checked_add(incoming_bytes)?
                    .checked_add(1)?;
                pay(bytes.checked_mul(4)?)?;
            }
        }
        // The selected source surface may be wider than its private core id.
        // Existing admission hashes that exact surface in these two tables.
        pay(table::string_lookup::<(String, Vec<SymbolInfo>)>(
            original[2],
            original[3],
            widest,
        )?)?;
        pay(table::string_lookup::<(String, ())>(
            original[6],
            original[7],
            widest,
        )?)?;
        pay(0)?;
        (geometry(self) == original).then_some(ProjectionLookupFootprint {
            geometry: original,
            work,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context(count: usize) -> Context {
        let mut context = Context::new();
        for index in 0..count {
            let commands = crate::parse(&format!("(declare-const source_{index} Int)")).unwrap();
            context.process_command(&commands[0]).unwrap();
        }
        context
    }

    #[test]
    fn symbolic_projection_lookup_cost_pays_actual_sparse_backing_and_physical_overloads() {
        let dense = context(16);
        let mut sparse = context(96);
        for index in 16..96 {
            sparse.symbols.remove(&format!("source_{index}"));
        }
        let dense_fee = dense
            .admit_projection_lookup_work_with_progress(12, &mut |_, _| true)
            .unwrap();
        let sparse_fee = sparse
            .admit_projection_lookup_work_with_progress(12, &mut |_, _| true)
            .unwrap();
        assert!(sparse.symbols.allocation_size() > dense.symbols.allocation_size());
        assert!(sparse_fee.work() > dense_fee.work());
        let (key, info) = sparse.symbols.iter().next().unwrap();
        let key = key.clone();
        let info = info.clone();
        sparse.overloaded_symbols.insert(key, vec![info; 257]);
        let mut debit = 0;
        let overload_fee = sparse
            .admit_projection_lookup_work_with_progress(12, &mut |work, _| {
                debit += work;
                true
            })
            .unwrap();
        assert_eq!(debit, overload_fee.work());
        assert!(overload_fee.work() > sparse_fee.work());
        assert!(!sparse_fee.matches_storage(&sparse));
    }

    #[test]
    fn symbolic_projection_lookup_cost_refusal_does_not_mutate_or_mint_a_binding() {
        let context = context(4);
        let source = context.source_context_stamp();
        let terms = context.terms.snapshot_stamp();
        let before = geometry(&context);
        let mut calls = 0;
        assert!(context
            .admit_projection_lookup_work_with_progress(12, &mut |_, _| {
                calls += 1;
                calls < 3
            })
            .is_none());
        assert_eq!(before, geometry(&context));
        assert_eq!(terms, context.terms.snapshot_stamp());
        assert_eq!(source, context.source_context_stamp());
        let empty = Context::new();
        let zero = empty
            .admit_projection_lookup_work_with_progress(0, &mut |_, _| true)
            .unwrap();
        let wide = empty
            .admit_projection_lookup_work_with_progress(1_000_000, &mut |_, _| true)
            .unwrap();
        assert!(zero.work() > 0 && wide.work() > zero.work());
    }
}
