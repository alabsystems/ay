// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Untrusted scalar observations of original nested arrays and records.
//! Original composite arguments remain present; only original-source replay
//! may certify the universally pulled-back interpretation.

mod access;
mod budget;
mod candidate;
mod classify;
mod layout;
mod names;
pub(super) mod replay;
mod rewrite;
#[cfg(test)]
mod tests;

use super::source_premises::{self, SourceControl};
use crate::quantified::QuantifiedChcProblem;
use crate::{ChcSort, InvariantModel};
use ay_core::time::Instant;
pub(super) use layout::Layout;

#[derive(Debug)]
pub(super) struct ObservationModel {
    pub(super) layout: Layout,
    pub(super) model: InvariantModel,
}

/// Composite cells and wide array state use original-source observations, not
/// the legacy flat ghost certificate. Admission remains the registry's job.
pub(super) fn requires_observations(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<bool> {
    Some(classify::source(problem, control)? != classify::Shape::Flat)
}

#[cfg(test)]
pub(in crate::transform::array_ghost_pairs) fn test_candidates(
    problem: &QuantifiedChcProblem,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<(
    crate::ChcProblem,
    ay_core::kani_compat::DetHashMap<
        crate::PredicateId,
        Vec<super::candidate_model::CandidateAtom>,
    >,
)> {
    let raw = rewrite::problem(problem, layout, control)?;
    let pools = candidate::pools(problem, &raw, layout, control)?;
    Some((raw, pools))
}

pub(super) fn try_model(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<ObservationModel> {
    let layout = Layout::analyze(problem, control)?;
    let raw = rewrite::problem(problem, &layout, control)?;
    let canonical = layout.canonical_map(control)?;
    let pools = candidate::pools(problem, &raw, &layout, control)?;
    budget::final_model(&raw, &layout, &pools, control)?;
    // Preparation and synthesis spend the same absolute source envelope. The
    // remaining half is reserved for independent original-source discharge.
    let now = Instant::now();
    let deadline = now.checked_add(control.deadline.saturating_duration_since(now) / 2)?;
    control.poll()?;
    let model = super::candidate_houdini::try_seeded_model(
        &raw,
        canonical,
        pools,
        deadline,
        control.cancellation,
    )?
    .model;
    control.poll()?;
    Some(ObservationModel { layout, model })
}
