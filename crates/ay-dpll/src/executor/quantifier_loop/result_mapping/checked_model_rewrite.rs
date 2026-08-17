// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared model-bound authority core for independently replayed exact rewrites.

use ay_core::TermId;

use super::{installed_model_satisfies_roots, CheckedGroundScope};
use crate::executor::model::{self, Model, QuantifiedGrantModelEpoch};
use crate::executor::Executor;

#[must_use = "a checked exact-rewrite SAT authority must be consumed or discarded"]
#[derive(Debug)]
pub(super) struct CheckedModelRewriteSatAuthority {
    scope: CheckedGroundScope,
    model_epoch: QuantifiedGrantModelEpoch,
}

impl CheckedModelRewriteSatAuthority {
    pub(super) fn for_current(
        executor: &mut Executor,
        roots: &[TermId],
        rewritten_model_roots: &[TermId],
        diagnostic_name: &'static str,
    ) -> Option<Self> {
        if roots.is_empty()
            || rewritten_model_roots.is_empty()
            || executor.should_abort_theory_loop()
            || model::scoped_term_evaluation_override_active()
        {
            trace_decline(diagnostic_name, "empty roots or external stop");
            return None;
        }

        let predecessor = executor.last_model.take();
        let mut candidate = predecessor.clone().unwrap_or_else(Model::empty);
        let completed = model::with_isolated_eval_memo(|| {
            executor.complete_quantified_output_model_before_seal(&mut candidate, roots)
        });
        if !completed
            || executor.should_abort_theory_loop()
            || model::scoped_term_evaluation_override_active()
        {
            trace_decline(diagnostic_name, "output-safe completion declined");
            restore_model(executor, predecessor);
            return None;
        }

        executor.last_model = Some(candidate);
        model::eval_memo_clear();
        let accepted = model::with_isolated_eval_memo(|| {
            !executor.should_abort_theory_loop()
                && !model::scoped_term_evaluation_override_active()
                && installed_model_satisfies_roots(executor, rewritten_model_roots)
        });
        if !accepted {
            trace_decline(diagnostic_name, "retained model failed rewritten roots");
            restore_model(executor, predecessor);
            return None;
        }

        let scope = CheckedGroundScope::capture(executor, roots);
        if executor.should_abort_theory_loop() || model::scoped_term_evaluation_override_active() {
            restore_model(executor, predecessor);
            return None;
        }
        let Some(installed) = executor.last_model.as_mut() else {
            restore_model(executor, predecessor);
            return None;
        };
        let model_epoch = installed.seal_quantified_grant_model();
        trace_accept(diagnostic_name);
        Some(Self { scope, model_epoch })
    }

    pub(super) fn into_current_roots(
        self,
        executor: &mut Executor,
    ) -> Option<(Box<[TermId]>, QuantifiedGrantModelEpoch)> {
        let current = !executor.should_abort_theory_loop()
            && !model::scoped_term_evaluation_override_active()
            && self
                .scope
                .is_current_for(executor, self.scope.roots.as_ref())
            && executor.last_model.as_ref().is_some_and(|installed| {
                installed.carries_quantified_grant_model(&self.model_epoch)
            });
        current.then_some((self.scope.roots, self.model_epoch))
    }
}

fn restore_model(executor: &mut Executor, predecessor: Option<Model>) {
    executor.last_model = predecessor;
    model::eval_memo_clear();
}

fn trace_decline(name: &str, reason: &str) {
    if ay_core::misc_cli_flags().debug_cert {
        eprintln!("CERT/{name}: decline ({reason})");
    }
}

fn trace_accept(name: &str) {
    if ay_core::misc_cli_flags().debug_cert {
        eprintln!("CERT/{name}: sealed exact retained model");
    }
}
