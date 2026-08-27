// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `result_mapping.rs` to preserve item paths.

fn installed_model_satisfies_roots(executor: &Executor, roots: &[TermId]) -> bool {
    executor.last_model.as_ref().is_some_and(|model| {
        roots
            .iter()
            .copied()
            .all(|root| matches!(executor.evaluate_term(model, root), EvalValue::Bool(true)))
    })
}

/// Identity of the exact model atomically installed from a checked
/// same-`Context` ground solve.
///
/// This token binds both the derived root window and the installed model
/// object.  Cloning or replacing the model, changing public query/source
/// authority, or rolling back/reusing any term slot makes it stale.
#[must_use = "an installed checked ground model must be consumed by its theorem"]
#[derive(Debug)]
pub(in crate::executor) struct InstalledCheckedGroundModel {
    scope: CheckedSameContextGroundScope,
    model_epoch: crate::executor::model::QuantifiedGrantModelEpoch,
}

impl InstalledCheckedGroundModel {
    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        self.scope.is_current(executor)
            && executor
                .last_model
                .as_ref()
                .is_some_and(|model| model.carries_quantified_grant_model(&self.model_epoch))
    }

    pub(in crate::executor) fn consume(self, executor: &mut Executor) -> bool {
        !executor.should_abort_theory_loop() && self.is_current(executor)
    }
}
