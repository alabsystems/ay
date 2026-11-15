// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only lookup of a parsed constant's exact elaborated value carrier.

use super::Context;
use crate::elaborate::DeclarationKind;
use ay_core::{Sort, TermId};

impl Context {
    /// Resolve a decoded source name to its unique live nullary declaration.
    ///
    /// This does not parse SMT text, elaborate a new term, or expose mutable
    /// declaration metadata. Definitions, aliases, native registrations and
    /// solver-internal symbols are not direct source declarations. A bounded
    /// overload family is inspected before choosing a nullary signature; two
    /// nullary signatures are ambiguous even when only one is source-owned.
    ///
    /// The result can be a constructor application: parsed single-constructor
    /// datatype constants undergo eager product elimination. Callers must
    /// authenticate the returned borrowed sort against the live term's sort
    /// before extracting a value. This lookup grants no SAT/model authority.
    #[must_use]
    pub fn source_constant_for_value(&self, name: &str) -> Option<(TermId, &Sort)> {
        let candidates = self.symbol_candidates(name)?;
        if candidates.len() > 4096 || self.is_defined_fun(name) || self.is_internal_symbol(name) {
            return None;
        }
        let mut nullary = candidates.iter().filter(|info| info.arg_sorts.is_empty());
        let info = nullary.next()?;
        if nullary.next().is_some()
            || !info.is_direct_source_declaration()
            || info.declaration_kind() != DeclarationKind::Uninterpreted
            || self.adopted_macro_interp(name).is_some()
        {
            return None;
        }
        let term = info.term?;
        self.terms.entry_stamp(term)?;
        Some((term, &info.sort))
    }
}

#[cfg(test)]
mod tests;
