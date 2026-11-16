// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native symbol registration with explicit binding provenance.

use super::{Context, SymbolInfo};
use crate::elaborate::{DeclarationKind, PublicSort, SymbolBindingOrigin};
use ay_core::{Sort, TermId};

impl Context {
    /// Preflight the existing native-global adoption operation for a scalar
    /// Bool/BV constant. This reserves metadata only; registration still uses
    /// the canonical binding/provenance method and creates no new term.
    pub fn reserve_native_global_constant_adoption(
        &mut self,
        name: &str,
        term: TermId,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<(), ay_core::term::CountedTermError> {
        use ay_core::term::CountedTermError;
        owner.admit(name.len(), 0)?;
        if !matches!(self.terms.sort(term), Sort::Bool | Sort::BitVec(_))
            || self.has_symbol_binding(name)
        {
            return Err(CountedTermError::InvalidInput);
        }
        if self.symbols.len() == self.symbols.capacity() {
            owner.admit(self.symbols.allocation_size(), 0)?;
            for key in self.symbols.keys() {
                owner.admit(key.len(), 0)?;
            }
        }
        ay_core::term::reserve_map_counted(&mut self.symbols, 1, owner)?;
        let work = self
            .scopes
            .len()
            .checked_mul(
                name.len()
                    .checked_add(1)
                    .ok_or(CountedTermError::InvalidInput)?,
            )
            .ok_or(CountedTermError::InvalidInput)?;
        // Replacement snapshots clone only this scalar SymbolInfo: its
        // argument vectors/internal-name are empty; the fresh declaration's
        // Arc marker is shared, not reallocated per scope.
        owner.admit(work, 2 * size_of::<usize>())?;
        owner.check()?;
        Ok(())
    }
    pub(super) fn register_symbol_with_internal_name(
        &mut self,
        name: String,
        term: TermId,
        sort: Sort,
        internal_name: Option<String>,
    ) {
        self.register_symbol_with_internal_name_and_origin(
            name,
            term,
            sort,
            internal_name,
            SymbolBindingOrigin::Other,
        );
    }

    pub(super) fn register_symbol_with_internal_name_and_origin(
        &mut self,
        name: String,
        term: TermId,
        sort: Sort,
        internal_name: Option<String>,
        binding_origin: SymbolBindingOrigin,
    ) {
        let public_sort = PublicSort::from_engine(&sort);
        let info = SymbolInfo::fresh_with_binding_origin(
            Some(term),
            sort,
            vec![],
            public_sort,
            vec![],
            internal_name,
            DeclarationKind::Uninterpreted,
            binding_origin,
        );
        if self.global_declarations_enabled() {
            self.propagate_global_symbol_replacement_to_snapshots(&name, &info);
        } else {
            self.track_scoped_symbol(&name);
        }
        self.symbols.insert(name, info);
        self.advance_source_revision();
    }
}
