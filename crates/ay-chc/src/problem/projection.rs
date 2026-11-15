// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Registry-only support for a private, Safe-candidate argument projection.

use super::ChcProblem;

impl ChcProblem {
    /// Narrow a cloned candidate's signatures, retaining every other registry.
    ///
    /// The caller must rewrite every live predicate occurrence using the same
    /// position maps before solving. This operation grants no equivalence or
    /// counterexample authority. On interruption the partially modified clone
    /// must be discarded; the original problem remains the proof boundary.
    pub(crate) fn project_predicate_signatures(
        &mut self,
        kept: &[Vec<usize>],
        poll: &mut dyn FnMut() -> bool,
    ) -> Option<()> {
        if !poll() || kept.len() != self.predicates.len() {
            return None;
        }
        for (predicate, positions) in self.predicates.iter().zip(kept) {
            if !poll() {
                return None;
            }
            let mut previous = None;
            for &position in positions {
                if !poll()
                    || position >= predicate.arg_sorts.len()
                    || previous.is_some_and(|previous| previous >= position)
                {
                    return None;
                }
                previous = Some(position);
            }
        }
        if !poll() {
            return None;
        }
        // Pruned query identities remain interpreted by the original registry.
        // This existing snapshot operation is opaque, so bracket its work.
        self.preserve_pruned_query_source();
        if !poll() {
            return None;
        }
        for (predicate, positions) in self.predicates.iter_mut().zip(kept) {
            if !poll() {
                return None;
            }
            let mut sorts = Vec::new();
            sorts.try_reserve_exact(positions.len()).ok()?;
            for &position in positions {
                if !poll() {
                    return None;
                }
                sorts.push(predicate.arg_sorts.get(position)?.clone());
            }
            predicate.arg_sorts = sorts;
        }
        poll().then_some(())
    }
}
