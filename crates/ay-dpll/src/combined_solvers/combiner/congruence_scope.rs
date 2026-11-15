// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Context-scoped congruence for verification combiners
//! (#combiner-verify-scope).

use ay_core::TermId;

use super::TheoryCombiner;

impl TheoryCombiner<'_> {
    /// Register EUF congruence only over the subterm closure of `roots`.
    ///
    /// Verification only: the soundness verifier re-checks a fixed literal set
    /// and needs no congruence over applications outside it. Must be called on
    /// a fresh combiner, before any atom is registered or asserted; afterwards
    /// it is ignored and the combiner keeps its full-store registration.
    pub(crate) fn scope_congruence_to_roots(&mut self, roots: impl IntoIterator<Item = TermId>) {
        self.euf.scope_func_apps_to_roots(roots);
    }

    /// Whether the EUF registers congruence over a verification scope only.
    #[cfg(test)]
    pub(crate) fn has_congruence_scope(&self) -> bool {
        self.euf.has_func_app_scope()
    }
}
