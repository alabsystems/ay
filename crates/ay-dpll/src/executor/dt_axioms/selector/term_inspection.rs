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

    /// [`Self::dt_name_of`] for `dt_term`, one side of the equality `eq`, or
    /// `None` when the two sides of `eq` differ in sort. Raw `mk_app`
    /// interning admits such an `=` (store residue that no assertion owns);
    /// it relates nothing, so a whole-store scan must not read `dt_term` as a
    /// value of the other side's datatype and mint `(is-C dt_term)` for it.
    pub(super) fn dt_name_of_equality_side(&self, eq: TermId, dt_term: TermId) -> Option<String> {
        let TermData::App(_, args) = self.ctx.terms.get(eq) else {
            return None;
        };
        if args.len() != 2 || self.ctx.terms.sort(args[0]) != self.ctx.terms.sort(args[1]) {
            return None;
        }
        self.dt_name_of(dt_term)
    }

    /// Whether `term` is an application of a declared datatype constructor.
    pub(super) fn term_is_constructor_app(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::App(Symbol::Named(name), _) if self.ctx.is_constructor(name).is_some()
        )
    }
}

#[cfg(test)]
mod tests;
