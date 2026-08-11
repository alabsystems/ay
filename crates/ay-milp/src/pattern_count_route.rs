// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact admission for an identical-block PB pattern-count quotient.
//!
//! This module consumes an exact MILP-to-PB translation plus an opaque, exactly
//! verified block partition from `ay-pb-core`, then accounts for every PB
//! variable, row, and objective term.  It admits only a common local-row
//! multiset and full-block nonnegative packing links.  A bounded exact projected
//! frontier and count master solve that quotient; a compact artifact replays the
//! full verification and solve without trusting serialized frontier state.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use ay_pb_core::{
    enumerate_projected_patterns_with_limits, solve_projected_pattern_count_with_limits,
    verify_ordered_block_partition_with_deadline, PbConstraint, PbInstance, PbLit, PbObjective,
    PbRel, PbTerm, ProjectedPatternCountLimits, ProjectedPatternDecline, ProjectedPatternFrontier,
    ProjectedPatternLimits, ProjectedPatternResource, VerifiedBlockPartition,
    VerifiedBlockPartitionDecline,
};

use crate::pb_translate::{PbInequality, PbRoutePlan};

const MAX_PATTERN_BLOCKS: usize = 16;
const MAX_PATTERN_BLOCK_WIDTH: usize = 96;
const MAX_PATTERN_LOCAL_ROWS: usize = 512;
const MAX_PATTERN_LINKING_ROWS: usize = 32;
const MAX_PATTERN_TERMS: usize = 50_000;
const MAX_PATTERN_SIGNATURE_STATES: usize = 262_144;
const MAX_PATTERN_CLASSIFICATION_WORK: usize = 1_000_000;
const MAX_PATTERN_PLAN_ROWS: usize = 8_192;
const MAX_PATTERN_ROW_TERMS: usize = 8_192;
const PATTERN_PROCESS_MEMORY_PERCENT: usize = 90;

/// One canonical local PB inequality in common block-coordinate order.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PatternLocalConstraint {
    pub(crate) terms: Vec<(u32, i128)>,
    pub(crate) rhs: i128,
}

/// One exact nonnegative packing resource `usage(x) <= capacity`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternPackingResource {
    pub(crate) usage: Vec<(u32, i128)>,
    pub(crate) capacity: i128,
}

/// Complete exact quotient data.  Block variables are zero-based PB ids; every
/// block vector shares the coordinate order used by local rows, resources, and
/// the objective.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternCountQuotient {
    pub(crate) blocks: Vec<Vec<u32>>,
    pub(crate) local_constraints: Vec<PatternLocalConstraint>,
    pub(crate) packing_resources: Vec<PatternPackingResource>,
    pub(crate) local_objective: Vec<i128>,
    pub(crate) signature_states: usize,
}

/// Compact, model-bound replay artifact for an exact pattern-count optimum.
///
/// The ordered blocks use the core PB convention (one-based variable ids).
/// They are proposals, not trusted authority: replay rebuilds the current PB
/// instance, exactly verifies this complete partition, reclassifies every row
/// and objective term, and regenerates the frontier and count-master optimum.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternCountOptimalityCertificate {
    pub(crate) blocks: Vec<Vec<u32>>,
    pub(crate) pb_value: i128,
}

/// Exact optimal PB assignment reconstructed from the count master.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternCountSolution {
    pub(crate) assignment: Vec<bool>,
    pub(crate) pb_value: i128,
    pub(crate) certificate: PatternCountOptimalityCertificate,
}

/// Stage-aware outcome of trying the exact pattern-count route.
///
/// `VerifiedDeclined` means the ordered partition was proved exact before the
/// stricter packing quotient declined. `Admitted` means full quotient
/// classification completed. Both have earned one fresh structural fallback
/// slice; a globally non-matching `Declined` model has not.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PatternCountSolveAttempt {
    Declined(PatternCountDecline),
    VerifiedDeclined(PatternCountDecline),
    Admitted(Result<Option<PatternCountSolution>, PatternCountDecline>),
}

impl PatternCountSolveAttempt {
    pub(crate) fn earns_fresh_fallback(&self) -> bool {
        matches!(self, Self::VerifiedDeclined(_) | Self::Admitted(_))
    }
}

/// Typed, fail-closed reason exact classification, solving, or replay declined.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PatternCountDecline {
    Deadline,
    ResourceLimit,
    ArithmeticOverflow,
    InvalidPlan,
    InvalidPartition,
    ConstantConstraint,
    AsymmetricLocalRows,
    PartialLinkingRow,
    AsymmetricLinkingRow,
    UnsupportedLinkingRow,
    AsymmetricObjective,
    InvalidQuotient,
    VerificationFailed,
}

/// Verify a proposed full ordered partition, classify the current exact plan,
/// and solve its identical-block count quotient under bounded default limits.
///
/// `Ok(None)` is a complete infeasibility result for the verified quotient.
/// Every non-complete computation declines; no partial frontier or incumbent is
/// returned as an optimum.
pub(crate) fn try_solve_exact_pattern_count(
    plan: &PbRoutePlan,
    blocks: &[Vec<u32>],
    deadline: Option<Instant>,
) -> Result<Option<PatternCountSolution>, PatternCountDecline> {
    match attempt_solve_exact_pattern_count(plan, blocks, deadline) {
        PatternCountSolveAttempt::Declined(reason)
        | PatternCountSolveAttempt::VerifiedDeclined(reason) => Err(reason),
        PatternCountSolveAttempt::Admitted(result) => result,
    }
}

/// Stage-aware one-shot entry point used by production route budgeting.
pub(crate) fn attempt_solve_exact_pattern_count(
    plan: &PbRoutePlan,
    blocks: &[Vec<u32>],
    deadline: Option<Instant>,
) -> PatternCountSolveAttempt {
    attempt_solve_exact_pattern_count_with_deadlines(plan, blocks, deadline, deadline)
}

fn attempt_solve_exact_pattern_count_with_deadlines(
    plan: &PbRoutePlan,
    blocks: &[Vec<u32>],
    admission_deadline: Option<Instant>,
    solve_deadline: Option<Instant>,
) -> PatternCountSolveAttempt {
    if pattern_process_memory_exceeded() {
        return PatternCountSolveAttempt::Declined(PatternCountDecline::ResourceLimit);
    }
    if let Err(reason) = preflight_pattern_count_plan(plan, blocks, admission_deadline) {
        return PatternCountSolveAttempt::Declined(reason);
    }
    let instance = match core_instance_from_plan(plan, admission_deadline) {
        Ok(instance) => instance,
        Err(reason) => return PatternCountSolveAttempt::Declined(reason),
    };
    let partition =
        match verify_ordered_block_partition_with_deadline(&instance, blocks, admission_deadline) {
            Ok(Some(partition)) => partition,
            Ok(None) => {
                return PatternCountSolveAttempt::Declined(PatternCountDecline::InvalidPartition)
            }
            Err(reason) => {
                return PatternCountSolveAttempt::Declined(map_partition_decline(reason));
            }
        };
    let quotient = match classify_exact_block_quotient(plan, &partition, admission_deadline) {
        Ok(quotient) => quotient,
        Err(reason) => return PatternCountSolveAttempt::VerifiedDeclined(reason),
    };
    PatternCountSolveAttempt::Admitted(solve_exact_pattern_count(plan, &quotient, solve_deadline))
}

fn preflight_pattern_count_plan(
    plan: &PbRoutePlan,
    blocks: &[Vec<u32>],
    deadline: Option<Instant>,
) -> Result<(), PatternCountDecline> {
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    if usize::try_from(plan.num_constraints).ok() != Some(plan.constraints.len()) {
        return Err(PatternCountDecline::InvalidPlan);
    }
    if plan.constraints.len() > MAX_PATTERN_PLAN_ROWS {
        return Err(PatternCountDecline::ResourceLimit);
    }

    let block_count = blocks.len();
    if block_count < 2 {
        return Err(PatternCountDecline::InvalidPartition);
    }
    if block_count > MAX_PATTERN_BLOCKS {
        return Err(PatternCountDecline::ResourceLimit);
    }
    let block_width = blocks[0].len();
    if block_width == 0 {
        return Err(PatternCountDecline::InvalidPartition);
    }
    if block_width > MAX_PATTERN_BLOCK_WIDTH {
        return Err(PatternCountDecline::ResourceLimit);
    }
    let variable_count =
        usize::try_from(plan.num_vars).map_err(|_| PatternCountDecline::ResourceLimit)?;
    if block_count
        .checked_mul(block_width)
        .ok_or(PatternCountDecline::ResourceLimit)?
        != variable_count
    {
        return Err(PatternCountDecline::InvalidPartition);
    }

    // This bounded coverage bitmap prevents a malformed proposal from paying
    // for a full core-instance clone merely to be rejected by exact verification.
    let mut covered = vec![false; variable_count];
    let mut block_work = 0usize;
    for block in blocks {
        if block.len() != block_width {
            return Err(PatternCountDecline::InvalidPartition);
        }
        for &variable in block {
            if block_work & 0x3f == 0 && expired(deadline) {
                return Err(PatternCountDecline::Deadline);
            }
            block_work = block_work
                .checked_add(1)
                .ok_or(PatternCountDecline::ResourceLimit)?;
            let variable = variable
                .checked_sub(1)
                .and_then(|value| usize::try_from(value).ok())
                .filter(|&value| value < variable_count)
                .ok_or(PatternCountDecline::InvalidPartition)?;
            if std::mem::replace(&mut covered[variable], true) {
                return Err(PatternCountDecline::InvalidPartition);
            }
        }
    }
    if covered.iter().any(|&value| !value) {
        return Err(PatternCountDecline::InvalidPartition);
    }

    let mut raw_terms = 0usize;
    for (row_index, row) in plan.constraints.iter().enumerate() {
        if row_index & 0x3f == 0 && expired(deadline) {
            return Err(PatternCountDecline::Deadline);
        }
        if row.terms.len() > MAX_PATTERN_ROW_TERMS {
            return Err(PatternCountDecline::ResourceLimit);
        }
        raw_terms = raw_terms
            .checked_add(row.terms.len())
            .ok_or(PatternCountDecline::ResourceLimit)?;
        if raw_terms > MAX_PATTERN_TERMS {
            return Err(PatternCountDecline::ResourceLimit);
        }
        for (term_index, &(variable, _)) in row.terms.iter().enumerate() {
            if term_index & 0x3f == 0 && expired(deadline) {
                return Err(PatternCountDecline::Deadline);
            }
            if variable as usize >= variable_count {
                return Err(PatternCountDecline::InvalidPlan);
            }
        }
    }
    if let Some(objective) = &plan.objective {
        raw_terms = raw_terms
            .checked_add(objective.terms.len())
            .ok_or(PatternCountDecline::ResourceLimit)?;
        if raw_terms > MAX_PATTERN_TERMS {
            return Err(PatternCountDecline::ResourceLimit);
        }
        for (term_index, &(variable, _)) in objective.terms.iter().enumerate() {
            if term_index & 0x3f == 0 && expired(deadline) {
                return Err(PatternCountDecline::Deadline);
            }
            if variable as usize >= variable_count {
                return Err(PatternCountDecline::InvalidPlan);
            }
        }
    }
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    Ok(())
}

/// Solve one already-classified quotient and independently recheck the lifted
/// full PB assignment and exact integer objective against `plan`.
fn solve_exact_pattern_count(
    plan: &PbRoutePlan,
    quotient: &PatternCountQuotient,
    deadline: Option<Instant>,
) -> Result<Option<PatternCountSolution>, PatternCountDecline> {
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    validate_quotient_shape(plan, quotient, deadline)?;
    let (local_instance, resources, capacities) = local_pattern_problem(quotient, deadline)?;
    let frontier =
        enumerate_projected_patterns_with_deadline(&local_instance, &resources, deadline)?;
    let Some(count_solution) = solve_projected_pattern_count_with_deadline(
        &frontier,
        quotient.blocks.len(),
        &capacities,
        deadline,
    )?
    else {
        return Ok(None);
    };

    let assignment =
        reconstruct_assignment(plan, quotient, &frontier, &count_solution.pattern_indices)?;
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    if !plan.satisfies(&assignment) {
        return Err(PatternCountDecline::VerificationFailed);
    }
    let pb_value = plan
        .objective
        .as_ref()
        .map_or(Some(0), |objective| objective.value_at(&assignment))
        .ok_or(PatternCountDecline::VerificationFailed)?;
    if pb_value != count_solution.cost {
        return Err(PatternCountDecline::VerificationFailed);
    }
    let blocks = quotient
        .blocks
        .iter()
        .map(|block| {
            block
                .iter()
                .map(|&variable| {
                    variable
                        .checked_add(1)
                        .ok_or(PatternCountDecline::ResourceLimit)
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some(PatternCountSolution {
        assignment,
        pb_value,
        certificate: PatternCountOptimalityCertificate { blocks, pb_value },
    }))
}

/// Replay a compact pattern-count optimum against the caller's current plan.
///
/// The certificate carries neither a trusted frontier nor a trusted assignment.
/// Replay regenerates both deterministically after exact block verification and
/// full quotient classification, then compares the claimed exact PB value.
pub(crate) fn verify_pattern_count_optimality(
    plan: &PbRoutePlan,
    certificate: &PatternCountOptimalityCertificate,
    deadline: Option<Instant>,
) -> Result<PatternCountSolution, PatternCountDecline> {
    let replayed = try_solve_exact_pattern_count(plan, &certificate.blocks, deadline)?
        .ok_or(PatternCountDecline::VerificationFailed)?;
    if replayed.pb_value != certificate.pb_value {
        return Err(PatternCountDecline::VerificationFailed);
    }
    Ok(replayed)
}

fn core_instance_from_plan(
    plan: &PbRoutePlan,
    deadline: Option<Instant>,
) -> Result<PbInstance, PatternCountDecline> {
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    let variable_count =
        usize::try_from(plan.num_vars).map_err(|_| PatternCountDecline::ResourceLimit)?;
    if usize::try_from(plan.num_constraints).ok() != Some(plan.constraints.len()) {
        return Err(PatternCountDecline::InvalidPlan);
    }
    let mut constraints = Vec::with_capacity(plan.constraints.len());
    for (row_index, row) in plan.constraints.iter().enumerate() {
        if row_index & 0x3f == 0 && expired(deadline) {
            return Err(PatternCountDecline::Deadline);
        }
        let mut terms = Vec::with_capacity(row.terms.len());
        for (term_index, &(variable, coefficient)) in row.terms.iter().enumerate() {
            if term_index & 0x3f == 0 && expired(deadline) {
                return Err(PatternCountDecline::Deadline);
            }
            if variable as usize >= variable_count {
                return Err(PatternCountDecline::InvalidPlan);
            }
            terms.push(PbTerm {
                coeff: coefficient,
                lits: vec![PbLit {
                    var: variable
                        .checked_add(1)
                        .ok_or(PatternCountDecline::ResourceLimit)?,
                    negated: false,
                }],
            });
        }
        constraints.push(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: row.rhs,
        });
    }
    let objective = if let Some(objective) = &plan.objective {
        let mut terms = Vec::with_capacity(objective.terms.len());
        for (term_index, &(variable, coefficient)) in objective.terms.iter().enumerate() {
            if term_index & 0x3f == 0 && expired(deadline) {
                return Err(PatternCountDecline::Deadline);
            }
            if variable as usize >= variable_count {
                return Err(PatternCountDecline::InvalidPlan);
            }
            terms.push(PbTerm {
                coeff: coefficient,
                lits: vec![PbLit {
                    var: variable
                        .checked_add(1)
                        .ok_or(PatternCountDecline::ResourceLimit)?,
                    negated: false,
                }],
            });
        }
        Some(PbObjective { terms })
    } else {
        None
    };
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    Ok(PbInstance {
        num_vars: plan.num_vars,
        num_constraints: plan.num_constraints,
        constraints,
        objective,
    })
}

fn validate_quotient_shape(
    plan: &PbRoutePlan,
    quotient: &PatternCountQuotient,
    deadline: Option<Instant>,
) -> Result<(), PatternCountDecline> {
    let block_count = quotient.blocks.len();
    let block_width = quotient.blocks.first().map_or(0, Vec::len);
    if !(2..=MAX_PATTERN_BLOCKS).contains(&block_count)
        || block_width == 0
        || block_width > MAX_PATTERN_BLOCK_WIDTH
        || quotient.local_constraints.len() > MAX_PATTERN_LOCAL_ROWS
        || quotient.packing_resources.len() > MAX_PATTERN_LINKING_ROWS
        || quotient.local_objective.len() != block_width
    {
        return Err(PatternCountDecline::InvalidQuotient);
    }
    let variable_count =
        usize::try_from(plan.num_vars).map_err(|_| PatternCountDecline::ResourceLimit)?;
    if block_count
        .checked_mul(block_width)
        .ok_or(PatternCountDecline::ResourceLimit)?
        != variable_count
    {
        return Err(PatternCountDecline::InvalidQuotient);
    }
    let mut covered = vec![false; variable_count];
    let mut term_count = quotient.local_objective.len();
    for (block_index, block) in quotient.blocks.iter().enumerate() {
        if block_index & 0x7 == 0 && expired(deadline) {
            return Err(PatternCountDecline::Deadline);
        }
        if block.len() != block_width {
            return Err(PatternCountDecline::InvalidQuotient);
        }
        for &variable in block {
            let variable = usize::try_from(variable)
                .ok()
                .filter(|&value| value < variable_count)
                .ok_or(PatternCountDecline::InvalidQuotient)?;
            if std::mem::replace(&mut covered[variable], true) {
                return Err(PatternCountDecline::InvalidQuotient);
            }
        }
    }
    if covered.iter().any(|&value| !value) {
        return Err(PatternCountDecline::InvalidQuotient);
    }

    for row in &quotient.local_constraints {
        term_count = term_count
            .checked_add(row.terms.len())
            .ok_or(PatternCountDecline::ResourceLimit)?;
        validate_coordinate_terms(&row.terms, block_width, false)?;
    }
    let mut signature_states = 1usize;
    for resource in &quotient.packing_resources {
        if expired(deadline) {
            return Err(PatternCountDecline::Deadline);
        }
        if resource.capacity < 0 {
            return Err(PatternCountDecline::InvalidQuotient);
        }
        term_count = term_count
            .checked_add(resource.usage.len())
            .ok_or(PatternCountDecline::ResourceLimit)?;
        validate_coordinate_terms(&resource.usage, block_width, true)?;
        let radix = usize::try_from(resource.capacity)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or(PatternCountDecline::ResourceLimit)?;
        signature_states = signature_states
            .checked_mul(radix)
            .ok_or(PatternCountDecline::ResourceLimit)?;
        if signature_states > MAX_PATTERN_SIGNATURE_STATES {
            return Err(PatternCountDecline::ResourceLimit);
        }
    }
    if term_count > MAX_PATTERN_TERMS || signature_states != quotient.signature_states {
        return Err(PatternCountDecline::InvalidQuotient);
    }
    Ok(())
}

fn validate_coordinate_terms(
    terms: &[(u32, i128)],
    block_width: usize,
    require_positive: bool,
) -> Result<(), PatternCountDecline> {
    if terms.is_empty() {
        return Err(PatternCountDecline::InvalidQuotient);
    }
    let mut previous = None;
    for &(coordinate, coefficient) in terms {
        let coordinate = usize::try_from(coordinate)
            .ok()
            .filter(|&value| value < block_width)
            .ok_or(PatternCountDecline::InvalidQuotient)?;
        if previous.is_some_and(|value| coordinate <= value)
            || coefficient == 0
            || (require_positive && coefficient < 0)
        {
            return Err(PatternCountDecline::InvalidQuotient);
        }
        previous = Some(coordinate);
    }
    Ok(())
}

fn local_pattern_problem(
    quotient: &PatternCountQuotient,
    deadline: Option<Instant>,
) -> Result<(PbInstance, Vec<ProjectedPatternResource>, Vec<i128>), PatternCountDecline> {
    let block_width = quotient.blocks.first().map_or(0, Vec::len);
    let num_vars = u32::try_from(block_width).map_err(|_| PatternCountDecline::ResourceLimit)?;
    let num_constraints = u32::try_from(quotient.local_constraints.len())
        .map_err(|_| PatternCountDecline::ResourceLimit)?;
    let constraints = quotient
        .local_constraints
        .iter()
        .map(|row| {
            Ok(PbConstraint {
                terms: local_terms(&row.terms)?,
                rel: PbRel::Ge,
                rhs: row.rhs,
            })
        })
        .collect::<Result<Vec<_>, PatternCountDecline>>()?;
    let objective = PbObjective {
        terms: quotient
            .local_objective
            .iter()
            .enumerate()
            .filter(|&(_, &coefficient)| coefficient != 0)
            .map(|(coordinate, &coefficient)| {
                Ok(PbTerm {
                    coeff: coefficient,
                    lits: vec![PbLit {
                        var: u32::try_from(coordinate)
                            .ok()
                            .and_then(|value| value.checked_add(1))
                            .ok_or(PatternCountDecline::ResourceLimit)?,
                        negated: false,
                    }],
                })
            })
            .collect::<Result<Vec<_>, PatternCountDecline>>()?,
    };
    let mut resources = Vec::with_capacity(quotient.packing_resources.len());
    let mut capacities = Vec::with_capacity(quotient.packing_resources.len());
    for resource in &quotient.packing_resources {
        if expired(deadline) {
            return Err(PatternCountDecline::Deadline);
        }
        resources.push(ProjectedPatternResource {
            expression: PbObjective {
                terms: local_terms(&resource.usage)?,
            },
            minimum: 0,
            maximum: resource.capacity,
        });
        capacities.push(resource.capacity);
    }
    Ok((
        PbInstance {
            num_vars,
            num_constraints,
            constraints,
            objective: Some(objective),
        },
        resources,
        capacities,
    ))
}

fn local_terms(terms: &[(u32, i128)]) -> Result<Vec<PbTerm>, PatternCountDecline> {
    terms
        .iter()
        .map(|&(coordinate, coefficient)| {
            Ok(PbTerm {
                coeff: coefficient,
                lits: vec![PbLit {
                    var: coordinate
                        .checked_add(1)
                        .ok_or(PatternCountDecline::ResourceLimit)?,
                    negated: false,
                }],
            })
        })
        .collect()
}

fn reconstruct_assignment(
    plan: &PbRoutePlan,
    quotient: &PatternCountQuotient,
    frontier: &ProjectedPatternFrontier,
    pattern_indices: &[u32],
) -> Result<Vec<bool>, PatternCountDecline> {
    if pattern_indices.len() != quotient.blocks.len() {
        return Err(PatternCountDecline::VerificationFailed);
    }
    let variable_count =
        usize::try_from(plan.num_vars).map_err(|_| PatternCountDecline::ResourceLimit)?;
    let mut assignment = vec![false; variable_count];
    let mut assigned = vec![false; variable_count];
    for (block, &pattern_index) in quotient.blocks.iter().zip(pattern_indices) {
        let pattern = usize::try_from(pattern_index)
            .ok()
            .and_then(|index| frontier.patterns.get(index))
            .ok_or(PatternCountDecline::VerificationFailed)?;
        if pattern.assignment.len() != block.len() {
            return Err(PatternCountDecline::VerificationFailed);
        }
        for (&variable, &value) in block.iter().zip(&pattern.assignment) {
            let variable = usize::try_from(variable)
                .ok()
                .filter(|&index| index < variable_count)
                .ok_or(PatternCountDecline::VerificationFailed)?;
            if std::mem::replace(&mut assigned[variable], true) {
                return Err(PatternCountDecline::VerificationFailed);
            }
            assignment[variable] = value;
        }
    }
    if assigned.iter().any(|&value| !value) {
        return Err(PatternCountDecline::VerificationFailed);
    }
    Ok(assignment)
}

fn enumerate_projected_patterns_with_deadline(
    instance: &PbInstance,
    resources: &[ProjectedPatternResource],
    deadline: Option<Instant>,
) -> Result<ProjectedPatternFrontier, PatternCountDecline> {
    let mut limits = ProjectedPatternLimits::default();
    limits.memory_budget_bytes = process_clamped_memory_budget(limits.memory_budget_bytes);
    let mut memory_stopped = false;
    enumerate_projected_patterns_with_limits(instance, resources, limits, || {
        if expired(deadline) {
            return true;
        }
        memory_stopped = pattern_process_memory_exceeded();
        memory_stopped
    })
    .map_err(|decline| map_projection_decline_with_memory(decline, memory_stopped))
}

fn solve_projected_pattern_count_with_deadline(
    frontier: &ProjectedPatternFrontier,
    block_count: usize,
    capacities: &[i128],
    deadline: Option<Instant>,
) -> Result<Option<ay_pb_core::ProjectedPatternCountSolution>, PatternCountDecline> {
    // The frontier remains live while the count master allocates. Re-read the
    // process footprint here so this phase is charged only against the actual
    // remaining main `--memory` envelope, not a second independent default.
    let mut limits = ProjectedPatternCountLimits::default();
    limits.memory_budget_bytes = process_clamped_memory_budget(limits.memory_budget_bytes);
    let mut memory_stopped = false;
    solve_projected_pattern_count_with_limits(frontier, block_count, capacities, limits, || {
        if expired(deadline) {
            return true;
        }
        memory_stopped = pattern_process_memory_exceeded();
        memory_stopped
    })
    .map_err(|decline| map_projection_decline_with_memory(decline, memory_stopped))
}

fn process_clamped_memory_budget(default_budget: u64) -> u64 {
    clamp_memory_budget(
        default_budget,
        ay_sys::get_process_memory_limit(),
        ay_sys::current_live_bytes().max(ay_sys::current_footprint_bytes()),
    )
}

fn clamp_memory_budget(default_budget: u64, process_limit: usize, current_bytes: usize) -> u64 {
    if process_limit == 0 {
        return default_budget;
    }
    let ceiling =
        (process_limit as u128).saturating_mul(PATTERN_PROCESS_MEMORY_PERCENT as u128) / 100;
    let remaining = ceiling.saturating_sub(current_bytes as u128);
    default_budget.min(u64::try_from(remaining).unwrap_or(u64::MAX))
}

fn pattern_process_memory_exceeded() -> bool {
    // The phase budgets reserve the final 10% of the process cap. Apply that
    // same threshold before the bounded core clone/classification and while
    // the DPs run. The test-only second predicate exercises this route with
    // ay-sys's thread-local force hook without adding a second footprint
    // syscall to production polling.
    let exceeded = ay_sys::process_memory_exceeded_at_percent(PATTERN_PROCESS_MEMORY_PERCENT);
    #[cfg(test)]
    let exceeded = exceeded || ay_sys::process_memory_exceeded();
    exceeded
}

fn map_projection_decline_with_memory(
    decline: ProjectedPatternDecline,
    memory_stopped: bool,
) -> PatternCountDecline {
    if memory_stopped && matches!(decline, ProjectedPatternDecline::Interrupted) {
        PatternCountDecline::ResourceLimit
    } else {
        map_projection_decline(decline)
    }
}

fn map_projection_decline(decline: ProjectedPatternDecline) -> PatternCountDecline {
    match decline {
        ProjectedPatternDecline::Interrupted => PatternCountDecline::Deadline,
        ProjectedPatternDecline::ArithmeticOverflow => PatternCountDecline::ArithmeticOverflow,
        ProjectedPatternDecline::ResourceLimit | ProjectedPatternDecline::MemoryLimit => {
            PatternCountDecline::ResourceLimit
        }
        ProjectedPatternDecline::UnsupportedStructure => PatternCountDecline::InvalidQuotient,
        ProjectedPatternDecline::VerificationFailed => PatternCountDecline::VerificationFailed,
        _ => PatternCountDecline::InvalidQuotient,
    }
}

fn map_partition_decline(decline: VerifiedBlockPartitionDecline) -> PatternCountDecline {
    match decline {
        VerifiedBlockPartitionDecline::Deadline => PatternCountDecline::Deadline,
        VerifiedBlockPartitionDecline::ResourceLimit => PatternCountDecline::ResourceLimit,
        VerifiedBlockPartitionDecline::UnsupportedStructure => PatternCountDecline::InvalidPlan,
        _ => PatternCountDecline::InvalidPartition,
    }
}

/// Classify a translated PB plan as identical local blocks coupled only by
/// bounded nonnegative packing rows.  The verified partition supplies only a
/// total coordinate layout: this function deliberately rechecks the current
/// `plan` in full and never treats automorphisms of `partition.source()` as
/// authority for current-plan semantics.
pub(crate) fn classify_exact_block_quotient(
    plan: &PbRoutePlan,
    partition: &VerifiedBlockPartition<'_>,
    deadline: Option<Instant>,
) -> Result<PatternCountQuotient, PatternCountDecline> {
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    if plan.num_constraints as usize != plan.constraints.len() {
        return Err(PatternCountDecline::InvalidPlan);
    }
    let mut work = 0usize;
    // The partition is a bounded search hint whose automorphisms are bound to
    // `partition.source()`.  This classifier deliberately takes no semantic
    // authority from that source: it reaccounts every variable, row, and
    // objective term in `plan` below.  Reusing the variable layout with a
    // changed plan can therefore only produce a fresh exact quotient or a
    // typed decline; it cannot reuse an old automorphism proof as authority.

    let block_count = partition.block_count();
    let block_width = partition.block_width();
    if !(2..=MAX_PATTERN_BLOCKS).contains(&block_count)
        || block_width == 0
        || block_width > MAX_PATTERN_BLOCK_WIDTH
    {
        return Err(PatternCountDecline::ResourceLimit);
    }
    let variable_count =
        usize::try_from(plan.num_vars).map_err(|_| PatternCountDecline::ResourceLimit)?;
    if block_count
        .checked_mul(block_width)
        .ok_or(PatternCountDecline::ResourceLimit)?
        != variable_count
    {
        return Err(PatternCountDecline::InvalidPartition);
    }

    let mut blocks = Vec::with_capacity(block_count);
    let mut location = vec![None; variable_count];
    for (block, source) in partition.blocks().iter().enumerate() {
        charge(&mut work, source.len(), deadline)?;
        if source.len() != block_width {
            return Err(PatternCountDecline::InvalidPartition);
        }
        let mut mapped = Vec::with_capacity(block_width);
        for (coordinate, &variable) in source.iter().enumerate() {
            let zero_based = variable
                .checked_sub(1)
                .and_then(|value| usize::try_from(value).ok())
                .filter(|&value| value < variable_count)
                .ok_or(PatternCountDecline::InvalidPartition)?;
            if location[zero_based].replace((block, coordinate)).is_some() {
                return Err(PatternCountDecline::InvalidPartition);
            }
            mapped.push(u32::try_from(zero_based).map_err(|_| PatternCountDecline::ResourceLimit)?);
        }
        blocks.push(mapped);
    }
    if location.iter().any(Option::is_none) {
        return Err(PatternCountDecline::InvalidPartition);
    }

    let total_terms = plan
        .constraints
        .iter()
        .try_fold(0usize, |count, row| count.checked_add(row.terms.len()))
        .and_then(|count| {
            count.checked_add(
                plan.objective
                    .as_ref()
                    .map_or(0, |objective| objective.terms.len()),
            )
        })
        .ok_or(PatternCountDecline::ResourceLimit)?;
    if total_terms > MAX_PATTERN_TERMS {
        return Err(PatternCountDecline::ResourceLimit);
    }

    let mut local_by_block = vec![Vec::new(); block_count];
    let mut packing_resources = Vec::new();
    let mut signature_states = 1usize;
    for (row_index, row) in plan.constraints.iter().enumerate() {
        if row_index & 0x3f == 0 && expired(deadline) {
            return Err(PatternCountDecline::Deadline);
        }
        let canonical = canonical_terms(row, variable_count, &mut work, deadline)?;
        if canonical.is_empty() {
            // Exact cancellation leaves `0 >= rhs`. A nonpositive right-hand
            // side is a proved tautology and contributes no quotient row. A
            // positive side is a proved contradiction, but this optimum-only
            // route has no infeasibility artifact yet, so it declines instead
            // of exporting an uncertified empty-master claim.
            if row.rhs <= 0 {
                continue;
            }
            return Err(PatternCountDecline::ConstantConstraint);
        }
        let mut touched = BTreeSet::new();
        for &(variable, _) in &canonical {
            let (block, _) =
                location[variable as usize].ok_or(PatternCountDecline::InvalidPartition)?;
            touched.insert(block);
        }
        if touched.len() == 1 {
            let block = touched
                .first()
                .copied()
                .ok_or(PatternCountDecline::ConstantConstraint)?;
            let mut terms = canonical
                .into_iter()
                .map(|(variable, coefficient)| {
                    let (_, coordinate) =
                        location[variable as usize].ok_or(PatternCountDecline::InvalidPartition)?;
                    Ok((
                        u32::try_from(coordinate)
                            .map_err(|_| PatternCountDecline::ResourceLimit)?,
                        coefficient,
                    ))
                })
                .collect::<Result<Vec<_>, PatternCountDecline>>()?;
            terms.sort_unstable_by_key(|&(coordinate, _)| coordinate);
            local_by_block[block].push(PatternLocalConstraint {
                terms,
                rhs: row.rhs,
            });
            if local_by_block[block].len() > MAX_PATTERN_LOCAL_ROWS {
                return Err(PatternCountDecline::ResourceLimit);
            }
            continue;
        }
        if touched.len() != block_count {
            return Err(PatternCountDecline::PartialLinkingRow);
        }
        if packing_resources.len() >= MAX_PATTERN_LINKING_ROWS {
            return Err(PatternCountDecline::ResourceLimit);
        }

        let mut by_block = vec![Vec::new(); block_count];
        for (variable, coefficient) in canonical {
            let (block, coordinate) =
                location[variable as usize].ok_or(PatternCountDecline::InvalidPartition)?;
            by_block[block].push((
                u32::try_from(coordinate).map_err(|_| PatternCountDecline::ResourceLimit)?,
                coefficient,
            ));
        }
        for terms in &mut by_block {
            terms.sort_unstable_by_key(|&(coordinate, _)| coordinate);
        }
        if by_block[1..].iter().any(|terms| terms != &by_block[0]) {
            return Err(PatternCountDecline::AsymmetricLinkingRow);
        }
        if row.rhs > 0 || by_block[0].iter().any(|&(_, coefficient)| coefficient >= 0) {
            return Err(PatternCountDecline::UnsupportedLinkingRow);
        }
        let capacity = row
            .rhs
            .checked_neg()
            .ok_or(PatternCountDecline::ArithmeticOverflow)?;
        let usage = by_block[0]
            .iter()
            .map(|&(coordinate, coefficient)| {
                coefficient
                    .checked_neg()
                    .map(|value| (coordinate, value))
                    .ok_or(PatternCountDecline::ArithmeticOverflow)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let radix = usize::try_from(capacity)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or(PatternCountDecline::ResourceLimit)?;
        signature_states = signature_states
            .checked_mul(radix)
            .ok_or(PatternCountDecline::ResourceLimit)?;
        if signature_states > MAX_PATTERN_SIGNATURE_STATES {
            return Err(PatternCountDecline::ResourceLimit);
        }
        packing_resources.push(PatternPackingResource { usage, capacity });
    }

    for rows in &mut local_by_block {
        rows.sort_unstable();
    }
    if local_by_block[1..]
        .iter()
        .any(|rows| rows != &local_by_block[0])
    {
        return Err(PatternCountDecline::AsymmetricLocalRows);
    }

    let mut objective_by_block = vec![vec![0i128; block_width]; block_count];
    if let Some(objective) = &plan.objective {
        let mut canonical = BTreeMap::new();
        for (index, &(variable, coefficient)) in objective.terms.iter().enumerate() {
            if index & 0x3f == 0 && expired(deadline) {
                return Err(PatternCountDecline::Deadline);
            }
            charge(&mut work, 1, deadline)?;
            let variable = usize::try_from(variable)
                .ok()
                .filter(|&value| value < variable_count)
                .ok_or(PatternCountDecline::InvalidPlan)?;
            let next = canonical
                .get(&variable)
                .copied()
                .unwrap_or(0i128)
                .checked_add(coefficient)
                .ok_or(PatternCountDecline::ArithmeticOverflow)?;
            if next == 0 {
                canonical.remove(&variable);
            } else {
                canonical.insert(variable, next);
            }
        }
        for (variable, coefficient) in canonical {
            let (block, coordinate) =
                location[variable].ok_or(PatternCountDecline::InvalidPartition)?;
            objective_by_block[block][coordinate] = coefficient;
        }
    }
    if objective_by_block[1..]
        .iter()
        .any(|objective| objective != &objective_by_block[0])
    {
        return Err(PatternCountDecline::AsymmetricObjective);
    }
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }

    Ok(PatternCountQuotient {
        blocks,
        local_constraints: local_by_block.into_iter().next().unwrap_or_default(),
        packing_resources,
        local_objective: objective_by_block.into_iter().next().unwrap_or_default(),
        signature_states,
    })
}

fn canonical_terms(
    row: &PbInequality,
    variable_count: usize,
    work: &mut usize,
    deadline: Option<Instant>,
) -> Result<Vec<(u32, i128)>, PatternCountDecline> {
    let mut canonical = BTreeMap::new();
    for (index, &(variable, coefficient)) in row.terms.iter().enumerate() {
        if index & 0x3f == 0 && expired(deadline) {
            return Err(PatternCountDecline::Deadline);
        }
        charge(work, 1, deadline)?;
        let variable_index = usize::try_from(variable)
            .ok()
            .filter(|&value| value < variable_count)
            .ok_or(PatternCountDecline::InvalidPlan)?;
        let next = canonical
            .get(&variable)
            .copied()
            .unwrap_or(0i128)
            .checked_add(coefficient)
            .ok_or(PatternCountDecline::ArithmeticOverflow)?;
        if next == 0 {
            canonical.remove(&variable);
        } else {
            canonical.insert(variable, next);
        }
        let _ = variable_index;
    }
    Ok(canonical.into_iter().collect())
}

fn charge(
    work: &mut usize,
    amount: usize,
    deadline: Option<Instant>,
) -> Result<(), PatternCountDecline> {
    if expired(deadline) {
        return Err(PatternCountDecline::Deadline);
    }
    *work = work
        .checked_add(amount)
        .ok_or(PatternCountDecline::ResourceLimit)?;
    if *work > MAX_PATTERN_CLASSIFICATION_WORK {
        return Err(PatternCountDecline::ResourceLimit);
    }
    Ok(())
}

fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_pb_core::{
        verify_all_constraints, verify_ordered_block_partition_with_deadline, PbConstraint,
        PbInstance, PbLit, PbObjective, PbRel, PbTerm,
    };
    use num_rational::BigRational;

    use crate::pb_translate::{translate, PbRoutePlan};
    use crate::{Model, Sense};

    fn fixture_plan() -> PbRoutePlan {
        let mut model = Model::default();
        let blocks: Vec<_> = (0..3)
            .map(|_| [model.add_binary_col(), model.add_binary_col()])
            .collect();
        for block in &blocks {
            model.add_row(1.0, f64::INFINITY, &[(block[0], 1.0), (block[1], 2.0)]);
            model.add_row(f64::NEG_INFINITY, 1.0, &[(block[0], 1.0), (block[1], -1.0)]);
        }
        model.add_row(
            f64::NEG_INFINITY,
            2.0,
            &blocks
                .iter()
                .map(|block| (block[0], 1.0))
                .collect::<Vec<_>>(),
        );
        model.add_row(
            f64::NEG_INFINITY,
            1.0,
            &blocks
                .iter()
                .map(|block| (block[1], 1.0))
                .collect::<Vec<_>>(),
        );
        model.set_objective(
            &blocks
                .iter()
                .flat_map(|block| [(block[0], 3.0), (block[1], -2.0)])
                .collect::<Vec<_>>(),
            Sense::Minimize,
        );
        translate(&model, None).expect("fixture translates exactly")
    }

    fn core_instance(plan: &PbRoutePlan) -> PbInstance {
        let constraints = plan
            .constraints
            .iter()
            .map(|row| PbConstraint {
                terms: row
                    .terms
                    .iter()
                    .map(|&(variable, coeff)| PbTerm {
                        coeff,
                        lits: vec![PbLit {
                            var: variable + 1,
                            negated: false,
                        }],
                    })
                    .collect(),
                rel: PbRel::Ge,
                rhs: row.rhs,
            })
            .collect();
        let objective = plan.objective.as_ref().map(|objective| PbObjective {
            terms: objective
                .terms
                .iter()
                .map(|&(variable, coeff)| PbTerm {
                    coeff,
                    lits: vec![PbLit {
                        var: variable + 1,
                        negated: false,
                    }],
                })
                .collect(),
        });
        PbInstance {
            num_vars: plan.num_vars,
            num_constraints: plan.num_constraints,
            constraints,
            objective,
        }
    }

    fn fixture() -> (PbRoutePlan, PbInstance) {
        let plan = fixture_plan();
        let instance = core_instance(&plan);
        (plan, instance)
    }

    fn detected_partition(instance: &PbInstance) -> VerifiedBlockPartition<'_> {
        verify_ordered_block_partition_with_deadline(
            instance,
            &[vec![1, 2], vec![3, 4], vec![5, 6]],
            None,
        )
        .expect("bounded exact verification")
        .expect("three identical blocks verified")
    }

    fn quotient_satisfies(quotient: &PatternCountQuotient, assignment: &[bool]) -> bool {
        let local = quotient.blocks.iter().all(|block| {
            quotient.local_constraints.iter().all(|row| {
                let lhs = row
                    .terms
                    .iter()
                    .fold(0i128, |sum, &(coordinate, coefficient)| {
                        if assignment[block[coordinate as usize] as usize] {
                            sum + coefficient
                        } else {
                            sum
                        }
                    });
                lhs >= row.rhs
            })
        });
        local
            && quotient.packing_resources.iter().all(|resource| {
                let usage = quotient.blocks.iter().fold(0i128, |total, block| {
                    total
                        + resource
                            .usage
                            .iter()
                            .fold(0i128, |sum, &(coordinate, coefficient)| {
                                if assignment[block[coordinate as usize] as usize] {
                                    sum + coefficient
                                } else {
                                    sum
                                }
                            })
                });
                usage <= resource.capacity
            })
    }

    fn quotient_objective(quotient: &PatternCountQuotient, assignment: &[bool]) -> i128 {
        quotient.blocks.iter().fold(0i128, |total, block| {
            total
                + quotient
                    .local_objective
                    .iter()
                    .enumerate()
                    .filter(|&(coordinate, _)| assignment[block[coordinate] as usize])
                    .map(|(_, &coefficient)| coefficient)
                    .sum::<i128>()
        })
    }

    fn sequential_blocks(block_count: usize, block_width: usize) -> Vec<Vec<u32>> {
        (0..block_count)
            .map(|block| {
                (0..block_width)
                    .map(|coordinate| {
                        u32::try_from(block * block_width + coordinate + 1)
                            .expect("small test variable")
                    })
                    .collect()
            })
            .collect()
    }

    fn brute_optimum(plan: &PbRoutePlan) -> Option<i128> {
        assert!(plan.num_vars <= 20);
        (0u64..(1u64 << plan.num_vars))
            .filter_map(|mask| {
                let assignment = (0..plan.num_vars)
                    .map(|variable| mask & (1 << variable) != 0)
                    .collect::<Vec<_>>();
                if !plan.satisfies(&assignment) {
                    return None;
                }
                plan.objective
                    .as_ref()
                    .map_or(Some(0), |objective| objective.value_at(&assignment))
            })
            .min()
    }

    #[test]
    fn quotient_is_exhaustively_equivalent_to_source_pb_plan() {
        let (plan, instance) = fixture();
        let partition = detected_partition(&instance);
        let quotient = classify_exact_block_quotient(&plan, &partition, None)
            .expect("identical packing quotient");
        assert_eq!(quotient.blocks.len(), 3);
        assert_eq!(quotient.blocks[0].len(), 2);
        assert_eq!(quotient.packing_resources.len(), 2);
        assert_eq!(quotient.signature_states, 6);

        for mask in 0u32..(1u32 << plan.num_vars) {
            let assignment: Vec<bool> = (0..plan.num_vars)
                .map(|bit| mask & (1 << bit) != 0)
                .collect();
            assert_eq!(
                quotient_satisfies(&quotient, &assignment),
                verify_all_constraints(&instance.constraints, &assignment),
                "feasibility mismatch for mask {mask:#x}"
            );
            let source_objective = plan
                .objective
                .as_ref()
                .and_then(|objective| objective.value_at(&assignment))
                .expect("objective evaluates");
            assert_eq!(quotient_objective(&quotient, &assignment), source_objective);
        }
    }

    #[test]
    fn changed_local_rhs_declines() {
        let (mut plan, instance) = fixture();
        let partition = detected_partition(&instance);
        plan.constraints[0].rhs += 1;
        assert_eq!(
            classify_exact_block_quotient(&plan, &partition, None),
            Err(PatternCountDecline::AsymmetricLocalRows)
        );
    }

    #[test]
    fn changed_linking_coefficient_and_partial_link_decline() {
        let (plan, instance) = fixture();
        let partition = detected_partition(&instance);
        let linking = plan.constraints.len() - 2;

        let mut asymmetric = plan.clone();
        asymmetric.constraints[linking].terms[0].1 -= 1;
        assert_eq!(
            classify_exact_block_quotient(&asymmetric, &partition, None),
            Err(PatternCountDecline::AsymmetricLinkingRow)
        );

        let mut partial = plan;
        partial.constraints[linking]
            .terms
            .retain(|&(variable, _)| variable != partition.blocks()[0][0] - 1);
        assert_eq!(
            classify_exact_block_quotient(&partial, &partition, None),
            Err(PatternCountDecline::PartialLinkingRow)
        );
    }

    #[test]
    fn automorphic_cross_row_orbit_is_not_mistaken_for_separable_links() {
        let mut model = Model::default();
        let variables: Vec<_> = (0..4).map(|_| model.add_binary_col()).collect();
        // Swapping blocks [0,1] and [2,3] exchanges these two rows, so the
        // complete row multiset has an exact block automorphism.  Neither row
        // is individually a sum of one common block contribution.
        model.add_row(
            f64::NEG_INFINITY,
            2.0,
            &[
                (variables[0], 1.0),
                (variables[1], 2.0),
                (variables[2], 2.0),
                (variables[3], 1.0),
            ],
        );
        model.add_row(
            f64::NEG_INFINITY,
            2.0,
            &[
                (variables[0], 2.0),
                (variables[1], 1.0),
                (variables[2], 1.0),
                (variables[3], 2.0),
            ],
        );
        let plan = translate(&model, None).expect("Boolean plan");
        let instance = core_instance(&plan);
        let partition = verify_ordered_block_partition_with_deadline(
            &instance,
            &[vec![1, 2], vec![3, 4]],
            None,
        )
        .expect("bounded exact verification")
        .expect("row orbit is an exact automorphism");
        assert_eq!(
            classify_exact_block_quotient(&plan, &partition, None),
            Err(PatternCountDecline::AsymmetricLinkingRow)
        );
    }

    #[test]
    fn lower_or_positive_linking_row_declines() {
        let (mut plan, instance) = fixture();
        let partition = detected_partition(&instance);
        let linking = plan.constraints.len() - 2;
        for (_, coefficient) in &mut plan.constraints[linking].terms {
            *coefficient = coefficient.abs();
        }
        plan.constraints[linking].rhs = 1;
        assert_eq!(
            classify_exact_block_quotient(&plan, &partition, None),
            Err(PatternCountDecline::UnsupportedLinkingRow)
        );
    }

    #[test]
    fn changed_objective_declines() {
        let (mut plan, instance) = fixture();
        let partition = detected_partition(&instance);
        plan.objective.as_mut().expect("objective").terms[0].1 += 1;
        assert_eq!(
            classify_exact_block_quotient(&plan, &partition, None),
            Err(PatternCountDecline::AsymmetricObjective)
        );
    }

    #[test]
    fn deadline_and_signature_resource_limits_decline() {
        let (plan, instance) = fixture();
        let partition = detected_partition(&instance);
        assert_eq!(
            classify_exact_block_quotient(&plan, &partition, Some(Instant::now())),
            Err(PatternCountDecline::Deadline)
        );

        let mut oversized = plan;
        let linking = oversized.constraints.len() - 1;
        oversized.constraints[linking].rhs = -262_144;
        assert_eq!(
            classify_exact_block_quotient(&oversized, &partition, None),
            Err(PatternCountDecline::ResourceLimit)
        );
    }

    #[test]
    fn process_memory_envelope_clamps_and_fails_closed() {
        assert_eq!(clamp_memory_budget(512, 0, usize::MAX), 512);
        assert_eq!(clamp_memory_budget(512, 1_000, 700), 200);
        assert_eq!(clamp_memory_budget(512, 1_000, 900), 0);
        assert_eq!(clamp_memory_budget(128, 1_000, 0), 128);

        struct ResetMemoryPressure;
        impl Drop for ResetMemoryPressure {
            fn drop(&mut self) {
                ay_sys::force_process_memory_exceeded_for_testing(false);
            }
        }

        ay_sys::force_process_memory_exceeded_for_testing(true);
        let _reset = ResetMemoryPressure;
        assert_eq!(
            attempt_solve_exact_pattern_count(&fixture_plan(), &sequential_blocks(3, 2), None),
            PatternCountSolveAttempt::Declined(PatternCountDecline::ResourceLimit)
        );
    }

    #[test]
    fn extreme_integer_and_constant_rows_are_handled_exactly() {
        let (plan, instance) = fixture();
        let partition = detected_partition(&instance);
        let linking = plan.constraints.len() - 1;

        let mut minimum_rhs = plan.clone();
        minimum_rhs.constraints[linking].rhs = i128::MIN;
        assert_eq!(
            classify_exact_block_quotient(&minimum_rhs, &partition, None),
            Err(PatternCountDecline::ArithmeticOverflow)
        );

        let mut minimum_coeff = plan.clone();
        for (_, coefficient) in &mut minimum_coeff.constraints[linking].terms {
            *coefficient = i128::MIN;
        }
        assert_eq!(
            classify_exact_block_quotient(&minimum_coeff, &partition, None),
            Err(PatternCountDecline::ArithmeticOverflow)
        );

        let expected = classify_exact_block_quotient(&plan, &partition, None)
            .expect("base quotient classifies");
        let mut cancelled = plan;
        cancelled.constraints.push(PbInequality {
            terms: vec![(0, 7), (0, -7)],
            rhs: 0,
        });
        cancelled.num_constraints += 1;
        assert_eq!(
            classify_exact_block_quotient(&cancelled, &partition, None),
            Ok(expected)
        );

        let last = cancelled.constraints.len() - 1;
        cancelled.constraints[last].rhs = 1;
        assert_eq!(
            classify_exact_block_quotient(&cancelled, &partition, None),
            Err(PatternCountDecline::ConstantConstraint)
        );
    }

    #[test]
    fn exact_empty_tautology_is_admitted_by_the_full_attempt() {
        let blocks = sequential_blocks(3, 2);
        let base = attempt_solve_exact_pattern_count(&fixture_plan(), &blocks, None);

        let mut with_tautology = fixture_plan();
        with_tautology.constraints.push(PbInequality {
            terms: Vec::new(),
            rhs: 0,
        });
        with_tautology.num_constraints += 1;
        let admitted = attempt_solve_exact_pattern_count(&with_tautology, &blocks, None);

        assert!(matches!(
            admitted,
            PatternCountSolveAttempt::Admitted(Ok(Some(_)))
        ));
        assert_eq!(admitted, base);

        let last = with_tautology.constraints.len() - 1;
        with_tautology.constraints[last].rhs = 1;
        assert_eq!(
            attempt_solve_exact_pattern_count(&with_tautology, &blocks, None),
            PatternCountSolveAttempt::VerifiedDeclined(PatternCountDecline::ConstantConstraint)
        );
    }

    #[test]
    fn radix_max_objective_offset_is_mapped_once() {
        let mut model = Model::default();
        let first = model.add_int_col(0.0, 2.0);
        let second = model.add_int_col(0.0, 2.0);
        model.add_row(f64::NEG_INFINITY, 2.0, &[(first, 1.0), (second, 1.0)]);
        model.set_objective(&[(first, 2.0), (second, 2.0)], Sense::Maximize);
        model.set_objective_offset(7.0);

        let plan = translate(&model, None).expect("bounded radix plan");
        assert_eq!(plan.num_vars, 4);
        let instance = core_instance(&plan);
        let partition = verify_ordered_block_partition_with_deadline(
            &instance,
            &[vec![1, 2], vec![3, 4]],
            None,
        )
        .expect("bounded exact verification")
        .expect("two radix blocks are identical");
        let quotient =
            classify_exact_block_quotient(&plan, &partition, None).expect("radix quotient");

        for mask in 0u32..16 {
            let assignment: Vec<bool> = (0..4).map(|bit| mask & (1 << bit) != 0).collect();
            assert_eq!(
                quotient_satisfies(&quotient, &assignment),
                plan.satisfies(&assignment),
                "radix feasibility mismatch for {mask:#x}"
            );
            if !plan.satisfies(&assignment) {
                continue;
            }
            let pb_value = plan
                .objective
                .as_ref()
                .and_then(|objective| objective.value_at(&assignment))
                .expect("PB objective");
            assert_eq!(quotient_objective(&quotient, &assignment), pb_value);
            let point = plan.lift(&assignment).expect("radix lift");
            model.check_point(&point).expect("source point");
            assert_eq!(
                plan.objective
                    .as_ref()
                    .expect("objective")
                    .map
                    .model_value(pb_value),
                model.objective_value_at(&point),
                "objective offset/direction must be applied exactly once"
            );
        }
    }

    #[test]
    fn source_model_witness_remains_exactly_checkable() {
        let (plan, instance) = fixture();
        let partition = detected_partition(&instance);
        let quotient = classify_exact_block_quotient(&plan, &partition, None).expect("quotient");
        let assignment = vec![true, false, true, false, false, true];
        assert_eq!(
            quotient_satisfies(&quotient, &assignment),
            plan.satisfies(&assignment)
        );
        let lifted = plan.lift(&assignment).expect("identity lift");
        assert_eq!(lifted.len(), assignment.len());
        assert!(lifted.iter().all(|value| {
            value == &BigRational::from_integer(0.into())
                || value == &BigRational::from_integer(1.into())
        }));
    }

    #[test]
    fn exact_count_solution_matches_bruteforce_and_replays() {
        let plan = fixture_plan();
        let blocks = sequential_blocks(3, 2);
        let solved = try_solve_exact_pattern_count(&plan, &blocks, None)
            .expect("bounded exact route")
            .expect("fixture is feasible");
        assert_eq!(Some(solved.pb_value), brute_optimum(&plan));
        assert!(plan.satisfies(&solved.assignment));
        assert_eq!(solved.certificate.blocks, blocks);
        assert_eq!(solved.certificate.pb_value, solved.pb_value);

        let replayed = verify_pattern_count_optimality(&plan, &solved.certificate, None)
            .expect("model-bound replay");
        assert_eq!(replayed, solved);
    }

    #[test]
    fn small_identical_block_family_matches_exhaustive_search() {
        for block_count in 2usize..=4 {
            for block_width in 1usize..=3 {
                let local_weight_sum = block_width * (block_width + 1) / 2;
                let resource_per_block: usize =
                    (0..block_width).map(|coordinate| 1 + coordinate % 2).sum();
                for local_rhs in 0..=local_weight_sum.min(3) {
                    for capacity in 0..=(block_count * resource_per_block).min(4) {
                        let mut model = Model::default();
                        let variables = (0..block_count)
                            .map(|_| {
                                (0..block_width)
                                    .map(|_| model.add_binary_col())
                                    .collect::<Vec<_>>()
                            })
                            .collect::<Vec<_>>();
                        for block in &variables {
                            let terms = block
                                .iter()
                                .enumerate()
                                .map(|(coordinate, &variable)| (variable, (coordinate + 1) as f64))
                                .collect::<Vec<_>>();
                            model.add_row(local_rhs as f64, f64::INFINITY, &terms);
                        }
                        let packing = variables
                            .iter()
                            .flat_map(|block| {
                                block.iter().enumerate().map(|(coordinate, &variable)| {
                                    (variable, (1 + coordinate % 2) as f64)
                                })
                            })
                            .collect::<Vec<_>>();
                        model.add_row(f64::NEG_INFINITY, capacity as f64, &packing);
                        let objective = variables
                            .iter()
                            .flat_map(|block| {
                                block.iter().enumerate().map(|(coordinate, &variable)| {
                                    let magnitude = (coordinate + 1) as f64;
                                    let coefficient = if coordinate & 1 == 0 {
                                        magnitude
                                    } else {
                                        -magnitude
                                    };
                                    (variable, coefficient)
                                })
                            })
                            .collect::<Vec<_>>();
                        model.set_objective(&objective, Sense::Minimize);

                        let plan = translate(&model, None).expect("small exact PB plan");
                        let blocks = sequential_blocks(block_count, block_width);
                        let solved = try_solve_exact_pattern_count(&plan, &blocks, None)
                            .expect("bounded pattern route");
                        let brute = brute_optimum(&plan);
                        assert_eq!(
                            solved.as_ref().map(|solution| solution.pb_value),
                            brute,
                            "blocks={block_count}, width={block_width}, rhs={local_rhs}, capacity={capacity}"
                        );
                        if let Some(solution) = solved {
                            assert!(plan.satisfies(&solution.assignment));
                            assert_eq!(
                                verify_pattern_count_optimality(&plan, &solution.certificate, None)
                                    .expect("deterministic replay")
                                    .pb_value,
                                solution.pb_value
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn exact_count_reports_complete_infeasibility() {
        let mut model = Model::default();
        let first = model.add_binary_col();
        let second = model.add_binary_col();
        model.add_row(1.0, f64::INFINITY, &[(first, 1.0)]);
        model.add_row(1.0, f64::INFINITY, &[(second, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(first, 1.0), (second, 1.0)]);
        let plan = translate(&model, None).expect("Boolean plan");
        assert_eq!(
            try_solve_exact_pattern_count(&plan, &[vec![1], vec![2]], None)
                .expect("complete exact solve"),
            None
        );
        assert_eq!(brute_optimum(&plan), None);
    }

    #[test]
    fn replay_rejects_block_value_and_model_tampering() {
        let plan = fixture_plan();
        let solution = try_solve_exact_pattern_count(&plan, &sequential_blocks(3, 2), None)
            .expect("bounded exact route")
            .expect("fixture feasible");

        let mut changed_value = solution.certificate.clone();
        changed_value.pb_value = changed_value
            .pb_value
            .checked_add(1)
            .expect("small fixture value");
        assert_eq!(
            verify_pattern_count_optimality(&plan, &changed_value, None),
            Err(PatternCountDecline::VerificationFailed)
        );

        let mut duplicate_variable = solution.certificate.clone();
        duplicate_variable.blocks[1][0] = duplicate_variable.blocks[0][0];
        assert_eq!(
            verify_pattern_count_optimality(&plan, &duplicate_variable, None),
            Err(PatternCountDecline::InvalidPartition)
        );

        let mut changed_plan = plan.clone();
        changed_plan
            .objective
            .as_mut()
            .expect("fixture objective")
            .terms[0]
            .1 += 1;
        assert!(
            verify_pattern_count_optimality(&changed_plan, &solution.certificate, None).is_err()
        );
    }

    #[test]
    fn solve_and_replay_deadlines_and_tampered_quotients_fail_closed() {
        let (plan, instance) = fixture();
        assert_eq!(
            try_solve_exact_pattern_count(&plan, &sequential_blocks(3, 2), Some(Instant::now())),
            Err(PatternCountDecline::Deadline)
        );

        let partition = detected_partition(&instance);
        let mut quotient =
            classify_exact_block_quotient(&plan, &partition, None).expect("valid exact quotient");
        quotient.signature_states += 1;
        assert_eq!(
            solve_exact_pattern_count(&plan, &quotient, None),
            Err(PatternCountDecline::InvalidQuotient)
        );
    }

    #[test]
    fn attempt_distinguishes_admitted_solve_decline_from_nonmatching_models() {
        let plan = fixture_plan();
        let blocks = sequential_blocks(3, 2);
        let post_admission_deadline = attempt_solve_exact_pattern_count_with_deadlines(
            &plan,
            &blocks,
            None,
            Some(Instant::now()),
        );
        assert_eq!(
            post_admission_deadline,
            PatternCountSolveAttempt::Admitted(Err(PatternCountDecline::Deadline))
        );
        assert!(post_admission_deadline.earns_fresh_fallback());

        let mut duplicate = blocks.clone();
        duplicate[1][0] = duplicate[0][0];
        let invalid_partition = attempt_solve_exact_pattern_count(&plan, &duplicate, None);
        assert_eq!(
            invalid_partition,
            PatternCountSolveAttempt::Declined(PatternCountDecline::InvalidPartition)
        );
        assert!(!invalid_partition.earns_fresh_fallback());

        let mut asymmetric_model = Model::default();
        let variables: Vec<_> = (0..4).map(|_| asymmetric_model.add_binary_col()).collect();
        asymmetric_model.add_row(
            f64::NEG_INFINITY,
            2.0,
            &[
                (variables[0], 1.0),
                (variables[1], 2.0),
                (variables[2], 2.0),
                (variables[3], 1.0),
            ],
        );
        asymmetric_model.add_row(
            f64::NEG_INFINITY,
            2.0,
            &[
                (variables[0], 2.0),
                (variables[1], 1.0),
                (variables[2], 1.0),
                (variables[3], 2.0),
            ],
        );
        let asymmetric_plan = translate(&asymmetric_model, None).expect("exact Boolean plan");
        let asymmetric =
            attempt_solve_exact_pattern_count(&asymmetric_plan, &[vec![1, 2], vec![3, 4]], None);
        assert_eq!(
            asymmetric,
            PatternCountSolveAttempt::VerifiedDeclined(PatternCountDecline::AsymmetricLinkingRow)
        );
        assert!(asymmetric.earns_fresh_fallback());
    }

    #[test]
    fn preflight_caps_and_expired_deadlines_decline_before_core_conversion() {
        let blocks = sequential_blocks(3, 2);
        let mut oversized_row = fixture_plan();
        oversized_row.constraints[0].terms = (0..=MAX_PATTERN_ROW_TERMS)
            .map(|index| ((index % 6) as u32, 1))
            .collect();
        assert_eq!(
            preflight_pattern_count_plan(&oversized_row, &blocks, None),
            Err(PatternCountDecline::ResourceLimit)
        );
        assert_eq!(
            attempt_solve_exact_pattern_count(&oversized_row, &blocks, None),
            PatternCountSolveAttempt::Declined(PatternCountDecline::ResourceLimit)
        );

        let mut oversized_total = fixture_plan();
        oversized_total.constraints = (0..7)
            .map(|_| PbInequality {
                terms: (0..8_000).map(|index| ((index % 6) as u32, 1)).collect(),
                rhs: 0,
            })
            .collect();
        oversized_total.num_constraints = oversized_total.constraints.len() as u32;
        assert_eq!(
            preflight_pattern_count_plan(&oversized_total, &blocks, None),
            Err(PatternCountDecline::ResourceLimit)
        );

        let oversized_partition = (0..=MAX_PATTERN_BLOCKS)
            .map(|index| vec![u32::try_from(index + 1).expect("small test id")])
            .collect::<Vec<_>>();
        let plan = fixture_plan();
        assert_eq!(
            preflight_pattern_count_plan(&plan, &oversized_partition, None),
            Err(PatternCountDecline::ResourceLimit)
        );

        let mut malformed = plan;
        malformed.num_constraints += 1;
        let expired = Some(Instant::now());
        assert_eq!(
            preflight_pattern_count_plan(&malformed, &blocks, expired),
            Err(PatternCountDecline::Deadline)
        );
        assert_eq!(
            core_instance_from_plan(&malformed, expired),
            Err(PatternCountDecline::Deadline)
        );
        assert_eq!(
            attempt_solve_exact_pattern_count(&malformed, &blocks, expired),
            PatternCountSolveAttempt::Declined(PatternCountDecline::Deadline)
        );
    }
}
