// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Transactional checkpoints for the shared propagation replay plan.

impl PlanCx<'_> {
    /// Chain length to roll back to if the current candidate fails.
    fn mark(&self) -> usize {
        self.chain.steps.len()
    }

    /// Remove a failed candidate's steps and every memo entry naming them.
    /// Negative memo entries remain valid, and `in_progress` is empty between
    /// candidate attempts by the planner's scope discipline.
    fn rollback(&mut self, mark: usize) {
        self.chain.steps.truncate(mark);
        let stale = |id: &ProofId| (id.0 as usize) >= mark;
        self.clause_memo.retain(|_, id| !stale(id));
        self.eq_memo.retain(|_, result| match result {
            Some(EqRes::Changed { id, .. }) => !stale(id),
            Some(EqRes::Unchanged) | None => true,
        });
        if self.false_taut.as_ref().is_some_and(stale) {
            self.false_taut = None;
        }
    }
}
