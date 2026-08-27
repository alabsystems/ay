// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Instance-aware datatype-term inspection for selector generation.

use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId};

use super::SelectorList;
use crate::executor::Executor;

impl Executor {
    /// Resolve a constructor's field sorts for one datatype instance.
    pub(super) fn selector_signature_in(
        &self,
        dt_name: &str,
        ctor_name: &str,
    ) -> Option<SelectorList> {
        self.ctx.constructor_selector_info_in(dt_name, ctor_name)
    }

    /// The datatype instance name of `term`, when it has a datatype sort.
    pub(super) fn dt_name_of(&self, term: TermId) -> Option<String> {
        match self.ctx.terms.sort(term) {
            Sort::Uninterpreted(name) => Some(name.clone()),
            Sort::Datatype(datatype) => Some(datatype.name.clone()),
            _ => None,
        }
    }

    /// Whether `term` is an application of a declared datatype constructor.
    pub(super) fn term_is_constructor_app(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::App(Symbol::Named(name), _) if self.ctx.is_constructor(name).is_some()
        )
    }
}
