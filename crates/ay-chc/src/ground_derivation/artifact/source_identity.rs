// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Same source identity limits as the wire format, with cooperative node/edge polls.
//! Native ground-derivation validation instead admits against the finite
//! `NATIVE_WHOLE_SOURCE_WORK` envelope without the wire canonical-sort charge.
//! Recursive sort derivation and the subsequent semantic validators retain opaque
//! work; this module does not promise a wall-clock or allocation envelope.

use super::{
    error, interruption_error, ChcExpr, ChcGroundDerivationArtifactError,
    ChcGroundDerivationArtifactErrorReason, ChcProblem, ChcSort, GroundValidationControl,
};
use crate::ground_derivation::{
    CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH, CHC_GROUND_DERIVATION_MAX_SOURCE_WORK,
};
use std::panic::{catch_unwind, AssertUnwindSafe};

mod expressions;
mod sorts;
mod validation;
pub(super) use validation::validate_source_semantics;
#[cfg(test)]
mod tests;

use sorts::{
    preflight_source_identity_sort_multiplied, source_bitvector_width_work, PricedDatatypes,
};

fn source_identity_error(message: impl Into<String>) -> ChcGroundDerivationArtifactError {
    error(
        ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded,
        message,
    )
}

/// Finite whole-problem envelope for NATIVE ground-derivation validation.
///
/// The wire limit prices the artifact's canonical identity: every node's
/// rendered ancestry, then a `x (1 + log2 items)` comparison sort of it
/// (`proof_metadata::normalization::text` sorts clauses, predicates and
/// children). Native validation never renders or orders that identity, yet
/// 50696b148 put this preflight, wire limit included, in front of native
/// `validate_ground_derivation`. Every native ground check then failed closed
/// on problem size alone, even for clauses no derivation selects: the
/// identical 9-step hub-analogue derivation validates with 85 `(_ BitVec 8)`
/// clauses and is rejected with 90, and 80-100-rule model-checker-consumer units need an
/// estimated 20-40x the wire limit. Native mode therefore skips the
/// comparison-sort charge and admits against 64x the wire limit.
///
/// It must stay FINITE: this pass and the live validators behind it
/// (`ChcProblem::validate_live_*`, the ordinary-UF collector) walk expression
/// TREES while `ChcExpr` children are `Arc`s that substitution and `let`
/// expansion keep shared on purpose, and `validate_ground_derivation` cannot
/// be cancelled. An unbounded envelope would unfold a DAG without limit (cf.
/// 25e6683cf). At >= 128 units per occurrence this walks at most ~2M
/// occurrences before refusing.
const NATIVE_WHOLE_SOURCE_WORK: usize = CHC_GROUND_DERIVATION_MAX_SOURCE_WORK * 64;

/// Whole-problem work envelope of this preflight run: the wire limit, or the
/// native one inside `GroundValidationControl::with_native_whole_source_scope`.
fn whole_source_work_limit(control: &GroundValidationControl<'_>) -> usize {
    if control.native_whole_source() {
        NATIVE_WHOLE_SOURCE_WORK
    } else {
        CHC_GROUND_DERIVATION_MAX_SOURCE_WORK
    }
}

fn charge_source_identity_work(
    control: &mut GroundValidationControl<'_>,
    work: &mut usize,
    amount: usize,
) -> Result<(), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let limit = whole_source_work_limit(control);
    *work = work
        .checked_add(amount)
        .filter(|work| *work <= limit)
        .ok_or_else(|| source_identity_error("whole-problem source identity exceeds work bound"))?;
    Ok(())
}

pub(super) fn preflight_problem_source_identity(
    control: &mut GroundValidationControl<'_>,
    problem: &ChcProblem,
) -> Result<(), ChcGroundDerivationArtifactError> {
    preflight(control, problem, false).map(|_| ())
}

/// Structural accounting is shared with playback and native validation. Only a
/// wire caller carrying the remaining grant into both canonical sorts can
/// replace the original conservative all-nodes reservation.
pub(super) fn preflight(
    control: &mut GroundValidationControl<'_>,
    problem: &ChcProblem,
    metered_wire: bool,
) -> Result<Option<usize>, ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let mut work = 0usize;
    let mut priced = PricedDatatypes::default();
    preflight_declarations(control, problem, &mut work, &mut priced)?;
    let expression_nodes =
        expressions::preflight_expressions(control, problem, &mut work, &mut priced)?;
    let sort_items = expression_nodes
        .max(problem.predicates().len())
        .max(problem.clauses().len())
        .max(problem.datatype_defs().len())
        .max(problem.action_names().len());
    let sort_rounds = sort_items.checked_sub(1).map_or(0, |maximum_index| {
        usize::BITS as usize - maximum_index.leading_zeros() as usize
    });
    // Native validation never orders the wire identity (see
    // `NATIVE_WHOLE_SOURCE_WORK`), so it is not charged for that sort. The
    // charge call below, and so its poll ordinal, is unchanged.
    let sort_rounds = if control.native_whole_source() {
        0
    } else {
        sort_rounds
    };
    let sort_work = work
        .checked_mul(sort_rounds)
        .ok_or_else(|| source_identity_error("whole-problem canonical sort work overflow"))?;
    let remaining = whole_source_work_limit(control) - work;
    if metered_wire && sort_work > remaining {
        control.poll().map_err(interruption_error)?;
        return Ok(Some(remaining));
    }
    charge_source_identity_work(control, &mut work, sort_work)?;
    control.poll().map_err(interruption_error)?;
    Ok(None)
}

fn preflight_declarations(
    control: &mut GroundValidationControl<'_>,
    problem: &ChcProblem,
    work: &mut usize,
    priced: &mut PricedDatatypes,
) -> Result<(), ChcGroundDerivationArtifactError> {
    for predicate in problem.predicates() {
        charge_source_identity_work(control, work, 64)?;
        charge_source_identity_work(
            control,
            work,
            predicate
                .name
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("predicate name work overflow"))?,
        )?;
        charge_source_identity_work(
            control,
            work,
            predicate
                .arg_sorts
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("predicate signature work overflow"))?,
        )?;
        for sort in &predicate.arg_sorts {
            preflight_source_identity_sort_multiplied(control, sort, work, 2, priced)?;
        }
    }
    for action_name in problem.action_names() {
        charge_source_identity_work(control, work, 32)?;
        charge_source_identity_work(
            control,
            work,
            action_name
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("action name work overflow"))?,
        )?;
    }
    for (datatype_name, constructors) in problem.datatype_defs() {
        charge_source_identity_work(control, work, 64)?;
        charge_source_identity_work(
            control,
            work,
            datatype_name
                .len()
                .checked_mul(2)
                .ok_or_else(|| source_identity_error("datatype name work overflow"))?,
        )?;
        for (constructor_name, selectors) in constructors {
            charge_source_identity_work(
                control,
                work,
                constructor_name
                    .len()
                    .checked_mul(2)
                    .ok_or_else(|| source_identity_error("constructor name work overflow"))?,
            )?;
            for (selector_name, sort) in selectors {
                charge_source_identity_work(
                    control,
                    work,
                    selector_name
                        .len()
                        .checked_mul(2)
                        .ok_or_else(|| source_identity_error("selector name work overflow"))?,
                )?;
                preflight_source_identity_sort_multiplied(control, sort, work, 2, priced)?;
            }
        }
    }
    Ok(())
}
