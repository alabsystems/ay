// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native symbol registration with explicit binding provenance.

use super::{Context, SymbolInfo};
use crate::elaborate::{DeclarationKind, PublicSort, SymbolBindingOrigin};
use ay_core::{Sort, TermId};

impl Context {
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
