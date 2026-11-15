// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Preserve the established semantic phase order after iterative safety preflight.
//! Each underlying validator remains opaque; these are cooperative phase polls.

use super::*;
use crate::ChcResult;

pub(in crate::ground_derivation::artifact) fn validate_source_semantics(
    problem: &ChcProblem,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    for validator in [
        ChcProblem::validate_live_clause_actions,
        ChcProblem::validate_live_background_theory_expressions,
        ChcProblem::validate_live_predicate_applications,
        ChcProblem::validate_live_typed_function_applications,
    ] {
        semantic_phase(|| validator(problem), control)?;
    }
    semantic_phase(
        || {
            // Pruned-query provenance is intentionally excluded: neither the
            // authenticated hashes nor live clause ordinals include it.
            let expressions = problem.clauses().iter().flat_map(|clause| {
                let head_arguments = match &clause.head {
                    crate::ClauseHead::Predicate(_, arguments) => arguments.as_slice(),
                    crate::ClauseHead::False => &[],
                };
                clause
                    .body
                    .constraint
                    .iter()
                    .chain(
                        clause
                            .body
                            .predicates
                            .iter()
                            .flat_map(|(_, arguments)| arguments),
                    )
                    .chain(head_arguments)
            });
            crate::smt::executor_adapter::collect_uninterpreted_function_declarations_for_exprs(
                expressions,
            )
            .map(|_| ())
        },
        control,
    )?;
    control.poll().map_err(interruption_error)
}

fn semantic_phase(
    validate: impl FnOnce() -> ChcResult<()>,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let result = catch_unwind(AssertUnwindSafe(validate));
    // Observe refusal before mapping an opaque operation's ordinary failure or
    // panic, so cancellation can never become malformed-source evidence.
    control.poll().map_err(interruption_error)?;
    result
        .map_err(|_| {
            error(
                ChcGroundDerivationArtifactErrorReason::ValidationPanicked,
                "bounded live source validation panicked",
            )
        })?
        .map_err(|source_error| {
            error(
                ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem,
                source_error.to_string(),
            )
        })
}
