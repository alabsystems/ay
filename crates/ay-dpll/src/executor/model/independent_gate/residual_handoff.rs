// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Move residual witness data, then recheck the changed model's original query.

use super::*;
use ay_model_check::{CompletedArrayAssignment, ModelConfirmation};

pub(super) struct Completion {
    roots: Vec<TermId>,
    assignments: Vec<CompletedArrayAssignment>,
}

fn refused() -> GateVerdict {
    GateVerdict::CannotConfirm {
        reason: "residual array handoff or full original model replay was refused".to_owned(),
    }
}

// The read-only view must stay borrowed through extraction. These are the
// same external-stop and memory predicates as should_abort_theory_loop, with
// no attempt to preempt a model callback or install a new resource allowance.
fn live(exec: &Executor) -> bool {
    exec.evaluation_stop_origin().is_none()
        && exec.external_stop_reason().is_none()
        && !exec.term_memory_exceeded()
        && !crate::memory::memory_exceeded(exec.memory_limit)
        && !ay_sys::process_memory_exceeded()
        && exec
            .last_model
            .as_ref()
            .is_none_or(|model| model.residual_arrays_are_current(&exec.ctx))
}

pub(super) fn extract(
    exec: &Executor,
    checked: ModelConfirmation<'_>,
    retained: Option<&mut Option<Vec<CompletedArrayAssignment>>>,
) -> GateVerdict {
    let (verdict, completion) = checked.into_parts();
    if exec.evaluation_stop_origin().is_some() {
        return refused();
    }
    let Some(retained) = retained else {
        // Immutable verdict-only callers keep their existing behavior.
        return verdict;
    };
    if !live(exec) {
        return refused();
    }
    let Some(completion) = completion else {
        return verdict;
    };
    if !matches!(verdict, GateVerdict::ConfirmedSat) {
        return refused();
    }
    let Some(assignments) = completion.into_assignments() else {
        return refused();
    };
    if !live(exec) {
        return refused();
    }
    *retained = Some(assignments);
    verdict
}

pub(super) fn capture(
    exec: &Executor,
    confirmation: Option<&QuantifiedModelConfirmation>,
) -> (GateVerdict, Option<Completion>) {
    if !live(exec) {
        return (refused(), None);
    }
    let Ok(roots) = independent_gate_query_roots(exec) else {
        return (refused(), None);
    };
    let mut assignments = None;
    let verdict = {
        let _caches = GateViewCacheSession::new();
        exec.confirm_sat_with_independent_gate_retaining(
            confirmation,
            &roots,
            Some(&mut assignments),
        )
    };
    // The borrowed view, evaluator and extraction scratch are gone. No reset
    // of the solve deadline or cancellation flag occurred between phases.
    if !live(exec) {
        return (refused(), None);
    }
    let completion = assignments.map(|assignments| Completion { roots, assignments });
    (verdict, completion)
}

fn invalidate_shared_caches() {
    // A nested fresh session alone would restore the stale outer session on
    // Drop. Replace that ambient slot at the model-mutation boundary too.
    ACTIVE_VIEW_CACHES.with(|slot| {
        let mut active = slot.borrow_mut();
        if active.is_some() {
            *active = Some(SharedViewCaches::fresh());
        }
    });
}

pub(super) fn install_and_replay(
    exec: &mut Executor,
    verdict: GateVerdict,
    completion: Option<Completion>,
) -> GateVerdict {
    if exec.publish_evaluation_stop()
        || exec.should_abort_theory_loop()
        || exec
            .last_model
            .as_ref()
            .is_some_and(|model| !model.residual_arrays_are_current(&exec.ctx))
    {
        return refused();
    }
    let Some(Completion { roots, assignments }) = completion else {
        return verdict;
    };
    if !matches!(verdict, GateVerdict::ConfirmedSat) {
        return refused();
    }
    // These values are DATA from one (possibly narrowed) initial check, not
    // authority for any different model. Revoke every model-relative grant.
    exec.last_model_validated = false;
    exec.clear_quantified_sat_authority();
    invalidate_shared_caches();
    if exec.publish_evaluation_stop() || exec.should_abort_theory_loop() {
        return refused();
    }
    let Some(model) = exec.last_model.as_mut() else {
        return refused();
    };
    if model
        .install_residual_arrays(&exec.ctx, assignments)
        .is_err()
    {
        return refused();
    }
    if exec.publish_evaluation_stop() || exec.should_abort_theory_loop() {
        return refused();
    }
    let verdict = {
        let _caches = GateViewCacheSession::new();
        let Some(model) = exec.last_model.as_ref() else {
            return refused();
        };
        let view = IndependentModelView::new(exec, model);
        if view.ensure_def_index().is_err() {
            return refused();
        }
        // Preserve the exact ordered UNFILTERED snapshot selected before the
        // first check; no certificate narrows this residual-disabled replay.
        ay_model_check::confirm_completed_model(&exec.ctx.terms, &view, &roots)
    };
    drop(roots);
    if exec.publish_evaluation_stop() || exec.should_abort_theory_loop() {
        return refused();
    }
    // The established array/DT validation handoff also accepts independent
    // confirmation as model-validation evidence. Here it covers every original
    // root under the installed model, with residual recovery disabled.
    if matches!(verdict, GateVerdict::ConfirmedSat) {
        exec.last_model_validated = true;
    }
    verdict
}

#[cfg(test)]
mod tests;
