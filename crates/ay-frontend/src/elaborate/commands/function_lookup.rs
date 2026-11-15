// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed source ownership for complete function-model extraction.

use super::Context;
use crate::elaborate::DeclarationKind;
use ay_core::Sort;

impl Context {
    /// Borrow the unique live direct-source ordinary function signature.
    ///
    /// The decoded name must identify exactly one declaration, not an
    /// overloaded family, native registration, alias, datatype member or
    /// genuine `define-fun`. A declared UF subsequently adopted as a macro
    /// remains eligible only under its exact original declaration identity.
    /// No declaration metadata or model authority is created or mutated.
    /// Callers must bound and authenticate the borrowed sorts for their own
    /// supported model fragment before recursively comparing or copying them.
    #[must_use]
    pub fn source_function_for_model(&self, name: &str) -> Option<(&[Sort], &Sort)> {
        let [info] = self.symbol_candidates(name)? else {
            return None;
        };
        if !info.is_direct_source_declaration()
            || info.declaration_kind() != DeclarationKind::Uninterpreted
            || self.is_internal_symbol(name)
        {
            return None;
        }
        match self.adopted_macro_interp(name) {
            Some((_, body)) => {
                if self.adopted_macro_declaration_ids.get(name) != Some(info.declaration_id()) {
                    return None;
                }
                self.terms.entry_stamp(*body)?;
            }
            None if self.is_defined_fun(name)
                || self.adopted_macro_declaration_ids.contains_key(name) =>
            {
                return None
            }
            None => {}
        }
        if info.arg_sorts.is_empty() {
            self.terms.entry_stamp(info.term?)?;
        }
        Some((&info.arg_sorts, &info.sort))
    }
}

#[cfg(test)]
mod tests;
