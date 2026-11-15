// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Route-local live roots for array axiom generation after substitution.

use super::{reachable_term_set, Executor, HashSet, TermId};

impl Executor {
    /// Replace the generator scope with the actual assertion/assumption DAG.
    /// The caller restores the returned scope after its complete array phase.
    /// Restoration-only substitution sources are deliberately not roots here.
    pub(in crate::executor) fn begin_live_array_axiom_scope(
        &mut self,
        extra_roots: &[TermId],
    ) -> Option<(HashSet<TermId>, usize)> {
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);
        let reachable = reachable_term_set(&self.ctx.terms, &roots);
        let start_len = self.ctx.terms.len();
        self.array_axiom_scope.replace((reachable, start_len))
    }

    /// Admit a genuinely generated axiom (or a required auxiliary negation),
    /// including older hash-consed descendants reused by its construction.
    /// Newly allocated terms already pass the scope watermark, but old reused
    /// terms need this exact root closure. Each node is retained once per scope.
    pub(super) fn include_array_axiom_scope_root(&mut self, root: TermId) {
        let Some((reachable, _)) = &mut self.array_axiom_scope else {
            return;
        };
        let mut pending = vec![root];
        while let Some(term) = pending.pop() {
            if reachable.insert(term) {
                pending.extend(self.ctx.terms.children(term));
            }
        }
    }

    /// A nested fixpoint may have installed its own incremental scope. Once
    /// it restores the caller's scope, keep any generated assertion roots live
    /// there too, including descendants reusing pre-watermark term identities.
    pub(super) fn include_current_array_assertions_in_scope(&mut self) {
        if self.array_axiom_scope.is_none() {
            return;
        }
        for root in self.ctx.assertions.clone() {
            self.include_array_axiom_scope_root(root);
        }
    }
}

#[cfg(test)]
mod tests;
