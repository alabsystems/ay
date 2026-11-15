// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Congruence-registration scope for verification instances
//! (#combiner-verify-scope).
//!
//! A verification solver asserts a handful of literals and reads one verdict.
//! Registering every function application of the whole term store makes its
//! initialization O(|store|) hashing and congruence-table work, and every
//! merge then walks parent lists that mostly point at unrelated terms. The
//! scope limits that registration to the subterm closure of the terms the
//! verifier will assert (see the `func_app_scope` field docs for why the
//! congruence closure over that subterm-closed set decides their EUF
//! (un)satisfiability).

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{TermId, TermStore};

use crate::solver::EufSolver;

/// The subterm closure of `roots`, as raw term indices.
pub(crate) fn subterm_closure(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> HashSet<u32> {
    let mut reachable: HashSet<u32> = HashSet::default();
    let mut stack: Vec<TermId> = roots.into_iter().collect();
    while let Some(term) = stack.pop() {
        if !reachable.insert(term.0) {
            continue;
        }
        for child in terms.children(term) {
            stack.push(child);
        }
    }
    reachable
}

/// The scope's term ids in ascending order, i.e. the order in which a full
/// `term_ids()` scan filtered by scope membership visits them.
pub(crate) fn ascending_scope_ids(scope: &HashSet<u32>, store_len: usize) -> Vec<TermId> {
    let mut ids: Vec<TermId> = scope
        .iter()
        .map(|&raw| TermId(raw))
        .filter(|term| term.index() < store_len)
        .collect();
    ids.sort_unstable();
    ids
}

impl EufSolver<'_> {
    /// Restrict congruence registration to the subterm closure of `roots`
    /// WITHOUT entering verify-only mode: Nelson-Oppen reason vectors are still
    /// built, so a combined verification solver can keep sharing equalities.
    ///
    /// Only for fresh verification instances. Once the e-graph has been
    /// initialized the scope can no longer change what was registered, so the
    /// call is then ignored and the solver keeps its full registration.
    ///
    /// NEVER call this on a solve-path solver: congruence over applications
    /// outside the scope is then simply missing, so the solver can call a
    /// set of literals satisfiable that is not (see the `func_app_scope`
    /// field docs). The solver only decides literals whose terms all lie in
    /// the scope, which a verifier guarantees by passing exactly the terms it
    /// asserts.
    pub fn scope_func_apps_to_roots(&mut self, roots: impl IntoIterator<Item = TermId>) {
        if self.func_apps_init || self.enodes_init {
            return;
        }
        self.func_app_scope = Some(subterm_closure(self.terms, roots));
    }

    /// Whether congruence registration is restricted to a verification scope.
    #[must_use]
    pub fn has_func_app_scope(&self) -> bool {
        self.func_app_scope.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_core::Sort;

    fn registered(solver: &EufSolver<'_>) -> Vec<(u32, u64, Vec<u32>)> {
        solver
            .func_apps
            .iter()
            .map(|meta| (meta.term_id, meta.func_hash, meta.args.clone()))
            .collect()
    }

    /// `f(x) f(y) g(f(x)) h(x, y) f(g(f(x)))`, and the context root
    /// `(= g(f(x)) f(y))` whose closure holds the first three only.
    fn store() -> (TermStore, TermId) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let fx = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
        let fy = terms.mk_app(Symbol::named("f"), [y], Sort::Int);
        let gfx = terms.mk_app(Symbol::named("g"), [fx], Sort::Int);
        let _hxy = terms.mk_app(Symbol::named("h"), [x, y], Sort::Int);
        let _fgfx = terms.mk_app(Symbol::named("f"), [gfx], Sort::Int);
        let root = terms.mk_app(Symbol::named("="), [gfx, fy], Sort::Bool);
        (terms, root)
    }

    /// The scoped registration is the full registration filtered to the
    /// scope: the same applications, metadata and order, and the same as a
    /// verify-only scoped solver's.
    #[test]
    fn scoped_registration_is_the_full_registration_filtered_to_the_scope() {
        let (terms, root) = store();
        let mut full = EufSolver::new(&terms);
        full.init_func_apps();
        let mut scoped = EufSolver::new(&terms);
        scoped.scope_func_apps_to_roots([root]);
        assert!(scoped.has_func_app_scope());
        scoped.init_func_apps();
        let closure = subterm_closure(&terms, [root]);
        let expected: Vec<_> = registered(&full)
            .into_iter()
            .filter(|(term, _, _)| closure.contains(term))
            .collect();
        assert_eq!(registered(&scoped), expected);
        assert_eq!(expected.len(), 3);
        assert_eq!(registered(&full).len(), 5);
        let mut verify_scoped = EufSolver::new(&terms).verify_only_scoped([root]);
        verify_scoped.init_func_apps();
        assert_eq!(registered(&verify_scoped), expected);
    }

    /// Negative twin: a scope requested after the e-graph registered its
    /// applications is ignored rather than leaving a half-scoped e-graph.
    #[test]
    fn a_scope_requested_after_initialization_is_ignored() {
        let (terms, root) = store();
        let mut solver = EufSolver::new(&terms);
        solver.init_func_apps();
        solver.scope_func_apps_to_roots([root]);
        assert!(!solver.has_func_app_scope());
        assert_eq!(registered(&solver).len(), 5);
    }
}
