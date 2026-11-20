// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed original syntax of uniquely owned, nonrecursive source macros.

use super::{Context, ParsedTerm};
use crate::elaborate::DeclarationKind;

impl Context {
    /// Borrow a nullary body introduced by an ordinary source `define-fun`.
    ///
    /// Recursive functions, adopted equations, overloaded signatures and native
    /// registrations do not confer this authority, and neither does a `:named`
    /// label, although it binds a nullary definition too. A caller may assume
    /// `(= NAME BODY)` for the body returned here, and pinned carcara 1.1.0,
    /// run without `--apply-function-defs`, holds that premise for a
    /// `define-fun` only: it expands a label wherever the label is used, so
    /// the same assume reads `(= BODY BODY)` and matches no premise. MEASURED
    /// on `(assert (! (< x 3) :named a))`, `(assert (not a))` under
    /// `--strict-proofs`: with labels admitted here the document assumed
    /// `(= a (< x 3))`, was stamped `trust_free=yes`, and carcara rejected it.
    ///
    /// The returned body retains source syntax, including operations the
    /// elaborator would fold. Callers must bound expansion before copying it,
    /// preserve declaration identities, and independently check any resulting
    /// proof. This lookup changes no source state and grants no authority to
    /// assume an arbitrary body.
    #[must_use]
    pub fn source_nullary_definition_for_proof(&self, name: &str) -> Option<&ParsedTerm> {
        let [info] = self.symbol_candidates(name)? else {
            return None;
        };
        // The constant-time refusals come first. `effective_declaration_kind`
        // scans every live symbol, and a caller that walks the whole symbol
        // table (`nullary_definition_premises`, run during UNSAT proof
        // assembly) made that scan quadratic in the symbol count: every
        // `:named` label is a `Defined` nullary binding, so with 17,653 labels
        // one proof assembly spent over 10 s here and the reduced-core recheck
        // of the SMT-COMP unsat-core track ran out of its budget (AY-SMT-4).
        // The predicate is a conjunction of side-effect-free tests, so the
        // order changes the cost only, never the answer.
        if info.declaration_kind() != DeclarationKind::Defined
            || info.is_named_label()
            || !info.arg_sorts.is_empty()
            || self.is_recursive_fun(name)
            || self.is_internal_symbol(name)
            || self.adopted_macro_interp(name).is_some()
            || self.effective_declaration_kind(info.declaration_id())
                != Some(DeclarationKind::Defined)
        {
            return None;
        }
        let (parameters, result, body) = self.fun_defs.get(name)?;
        (parameters.is_empty() && result == &info.sort).then_some(body)
    }
}

#[cfg(test)]
mod tests;
