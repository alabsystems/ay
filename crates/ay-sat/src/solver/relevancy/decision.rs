// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Solver {
    /// Real Scheme-A frontier decision. Empty candidates are rechecked by the
    /// model gate; admission refusal is handled outside this infallible kernel.
    /// Ordinary and counted policies supply storage, never a different frontier
    /// or branching algorithm.
    pub(in crate::solver) fn pick_relevancy_frontier_decision_with<
        P: decision_admission::Policy,
    >(
        &mut self,
        policy: &mut P,
    ) -> Option<Variable> {
        let mut frontier = std::mem::take(&mut self.relevancy_frontier);
        let any_relevant = policy.sync(&mut frontier, self);
        #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
        if frontier.take_debug_check() {
            frontier.debug_assert_members_exact();
            self.debug_assert_relevancy_frontier_exact_with(
                frontier.buf(),
                any_relevant,
                policy.reference(),
            );
        }
        let result = if any_relevant {
            self.pick_domain_restricted_decision(
                frontier.buf(),
                Some(frontier.members()),
                policy.skipped(),
            )
        } else {
            None
        };
        self.relevancy_frontier = frontier;
        self.note_relevancy_selection(result);
        result
    }
}
