// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact bounded projection of a Boolean PB block onto packing signatures.
//!
//! The dynamic program is an ordered binary decision diagram over the exact
//! residual intervals of the block-local constraints.  A state also carries
//! the exact values of caller-selected resource expressions.  At a fixed
//! layer, two prefixes merge only when both pieces agree; among such prefixes
//! only the lower objective value is retained.  Consequently the terminal
//! frontier contains the cheapest locally feasible assignment for every
//! attainable resource signature.
//!
//! This is a bounded specialist, not an unbounded enumeration API.  Variable,
//! row, resource, state, transition, pattern, and memory caps are checked
//! before allocation or insertion.  Any unsupported term, overflow,
//! interruption, or exhausted envelope declines without returning a partial
//! frontier.

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;

use crate::{PbInstance, PbObjective, PbRel};

const DEFAULT_MAX_VARIABLES: usize = 128;
const DEFAULT_MAX_ROWS: usize = 512;
const DEFAULT_MAX_RESOURCES: usize = 32;
const DEFAULT_MAX_TERMS: usize = 50_000;
const DEFAULT_MAX_STATES: usize = 2_000_000;
const DEFAULT_MAX_TRANSITIONS: u64 = 100_000_000;
const DEFAULT_MAX_PATTERNS: usize = 262_144;
const DEFAULT_MEMORY_BUDGET_BYTES: u64 = 512 << 20;
const DEFAULT_MAX_BLOCKS: usize = 16;
const DEFAULT_MAX_SIGNATURE_STATES: usize = 262_144;
const DEFAULT_MAX_COUNT_TRANSITIONS: u64 = 160_000_000;
const DEFAULT_COUNT_MEMORY_BUDGET_BYTES: u64 = 256 << 20;

/// One exact resource expression retained in the projected signature.
///
/// Both bounds are inclusive.  A block pattern outside the interval cannot
/// participate in the caller's packing problem and is pruned during the DP.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectedPatternResource {
    /// Linear pseudo-Boolean expression whose exact value is projected.
    pub expression: PbObjective,
    /// Smallest retained value of the expression.
    pub minimum: i128,
    /// Largest retained value of the expression.
    pub maximum: i128,
}

/// Explicit resource envelope for projected-pattern generation and replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProjectedPatternLimits {
    /// Maximum number of Boolean variables in one local block.
    pub max_variables: usize,
    /// Maximum number of block-local constraints.
    pub max_rows: usize,
    /// Maximum number of projected resource expressions.
    pub max_resources: usize,
    /// Maximum raw terms across constraints, resources, and objective.
    pub max_terms: usize,
    /// Maximum total retained states across all variable layers.
    pub max_states: usize,
    /// Maximum exact state-cell and sparse-column transition work.
    pub max_transitions: u64,
    /// Maximum number of terminal resource signatures.
    pub max_patterns: usize,
    /// Maximum conservatively estimated live allocation.
    pub memory_budget_bytes: u64,
}

impl Default for ProjectedPatternLimits {
    fn default() -> Self {
        Self {
            max_variables: DEFAULT_MAX_VARIABLES,
            max_rows: DEFAULT_MAX_ROWS,
            max_resources: DEFAULT_MAX_RESOURCES,
            max_terms: DEFAULT_MAX_TERMS,
            max_states: DEFAULT_MAX_STATES,
            max_transitions: DEFAULT_MAX_TRANSITIONS,
            max_patterns: DEFAULT_MAX_PATTERNS,
            memory_budget_bytes: DEFAULT_MEMORY_BUDGET_BYTES,
        }
    }
}

/// Explicit resource envelope for combining an exact frontier across
/// interchangeable blocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProjectedPatternCountLimits {
    /// Maximum number of interchangeable blocks in the exact count master.
    pub max_blocks: usize,
    /// Maximum number of packing-resource dimensions.
    pub max_resources: usize,
    /// Maximum number of patterns accepted from the projected frontier.
    pub max_patterns: usize,
    /// Maximum mixed-radix packing states, including the all-zero state.
    pub max_signature_states: usize,
    /// Maximum dense-compatible state/pattern work charged across all layers.
    /// Sparse traversal is used only when its candidate bound is no larger.
    pub max_transitions: u64,
    /// Maximum conservatively estimated live allocation.
    pub memory_budget_bytes: u64,
}

impl Default for ProjectedPatternCountLimits {
    fn default() -> Self {
        Self {
            max_blocks: DEFAULT_MAX_BLOCKS,
            max_resources: DEFAULT_MAX_RESOURCES,
            max_patterns: DEFAULT_MAX_PATTERNS,
            max_signature_states: DEFAULT_MAX_SIGNATURE_STATES,
            max_transitions: DEFAULT_MAX_COUNT_TRANSITIONS,
            memory_budget_bytes: DEFAULT_COUNT_MEMORY_BUDGET_BYTES,
        }
    }
}

/// Typed, fail-closed reason no complete projected frontier was returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProjectedPatternDecline {
    /// A nonlinear, out-of-range, or inconsistent PB shape was supplied.
    UnsupportedStructure,
    /// Checked exact integer arithmetic overflowed.
    ArithmeticOverflow,
    /// A variable, row, resource, term, state, transition, or pattern cap fired.
    ResourceLimit,
    /// The conservative live-allocation estimate exceeded its budget.
    MemoryLimit,
    /// The caller requested interruption or its deadline expired.
    Interrupted,
    /// A supplied frontier failed exact model-bound replay.
    VerificationFailed,
}

/// Cheapest exact representative of one attainable resource signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectedPattern {
    /// Resource values in the caller-supplied expression order.
    pub signature: Vec<i128>,
    /// Exact value of the instance objective, including negated-literal constants.
    pub cost: i128,
    /// Full assignment in increasing PB variable order (`x1` at index zero).
    pub assignment: Vec<bool>,
}

/// Complete bounded projection of one local PB block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectedPatternFrontier {
    /// Declared number of Boolean variables in the source block.
    pub num_variables: u32,
    /// Cheapest pattern for every attainable signature, sorted lexicographically.
    pub patterns: Vec<ProjectedPattern>,
    /// Total retained DP states, including the root and terminal layer.
    pub retained_states: u64,
    /// Exact transition work charged while building the frontier.
    pub transition_work: u64,
}

/// Exact optimum of selecting one retained pattern for every interchangeable
/// block under componentwise packing capacities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectedPatternCountSolution {
    /// Sum of the selected per-block exact costs.
    pub cost: i128,
    /// Frontier pattern index chosen for each block.
    pub pattern_indices: Vec<u32>,
    /// Componentwise total resource usage of the selected patterns.
    pub used_resources: Vec<i128>,
    /// Dense-compatible state/pattern work charged by the exact count DP.
    /// This accounting is unchanged when a cheaper sparse traversal is used.
    pub transition_pairs: u64,
}

/// Enumerate the complete projected frontier under the default limits.
pub fn enumerate_projected_patterns_interruptible<F>(
    instance: &PbInstance,
    resources: &[ProjectedPatternResource],
    should_stop: F,
) -> Result<ProjectedPatternFrontier, ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    enumerate_projected_patterns_with_limits(
        instance,
        resources,
        ProjectedPatternLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized projected-frontier enumeration.
pub fn enumerate_projected_patterns_with_limits<F>(
    instance: &PbInstance,
    resources: &[ProjectedPatternResource],
    limits: ProjectedPatternLimits,
    mut should_stop: F,
) -> Result<ProjectedPatternFrontier, ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(ProjectedPatternDecline::Interrupted);
    }
    let problem = CanonicalProblem::detect(instance, resources, limits, &mut should_stop)?;
    problem.enumerate(limits, &mut should_stop)
}

/// Replay a frontier against the exact source block under the default limits.
///
/// Replay reconstructs the entire bounded frontier from the supplied PB
/// instance and compares every signature, cost, assignment, and accounting
/// field.  A frontier copied to another block or edited in transit fails.
pub fn verify_projected_pattern_frontier_interruptible<F>(
    instance: &PbInstance,
    resources: &[ProjectedPatternResource],
    frontier: &ProjectedPatternFrontier,
    should_stop: F,
) -> Result<(), ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    verify_projected_pattern_frontier_with_limits(
        instance,
        resources,
        frontier,
        ProjectedPatternLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized exact replay of a projected frontier.
pub fn verify_projected_pattern_frontier_with_limits<F>(
    instance: &PbInstance,
    resources: &[ProjectedPatternResource],
    frontier: &ProjectedPatternFrontier,
    limits: ProjectedPatternLimits,
    should_stop: F,
) -> Result<(), ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    let replayed =
        enumerate_projected_patterns_with_limits(instance, resources, limits, should_stop)?;
    if &replayed == frontier {
        Ok(())
    } else {
        Err(ProjectedPatternDecline::VerificationFailed)
    }
}

/// Solve the exact identical-block count master under the default limits.
///
/// The master enforces `sum(pattern counts) = block_count`: every layer adds
/// exactly one pattern. Resource totals use a deterministic dense/sparse
/// mixed-radix traversal. The sparse path is selected only when its
/// reachable-state candidate bound is no larger than the dense compatible-pair
/// work, while resource accounting retains the dense bound. Capacities and
/// retained pattern usages must be nonnegative and `usize`-representable.
pub fn solve_projected_pattern_count_interruptible<F>(
    frontier: &ProjectedPatternFrontier,
    block_count: usize,
    capacities: &[i128],
    should_stop: F,
) -> Result<Option<ProjectedPatternCountSolution>, ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    solve_projected_pattern_count_with_limits(
        frontier,
        block_count,
        capacities,
        ProjectedPatternCountLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized exact identical-block count master.
pub fn solve_projected_pattern_count_with_limits<F>(
    frontier: &ProjectedPatternFrontier,
    block_count: usize,
    capacities: &[i128],
    limits: ProjectedPatternCountLimits,
    mut should_stop: F,
) -> Result<Option<ProjectedPatternCountSolution>, ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(ProjectedPatternDecline::Interrupted);
    }
    let master = CountMaster::detect(frontier, block_count, capacities, limits, &mut should_stop)?;
    master.solve(frontier, limits, &mut should_stop)
}

/// Replay a count-master solution under the default limits.
pub fn verify_projected_pattern_count_solution_interruptible<F>(
    frontier: &ProjectedPatternFrontier,
    block_count: usize,
    capacities: &[i128],
    solution: &ProjectedPatternCountSolution,
    should_stop: F,
) -> Result<(), ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    verify_projected_pattern_count_solution_with_limits(
        frontier,
        block_count,
        capacities,
        solution,
        ProjectedPatternCountLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized replay of a count-master optimum.
pub fn verify_projected_pattern_count_solution_with_limits<F>(
    frontier: &ProjectedPatternFrontier,
    block_count: usize,
    capacities: &[i128],
    solution: &ProjectedPatternCountSolution,
    limits: ProjectedPatternCountLimits,
    should_stop: F,
) -> Result<(), ProjectedPatternDecline>
where
    F: FnMut() -> bool,
{
    let replayed = solve_projected_pattern_count_with_limits(
        frontier,
        block_count,
        capacities,
        limits,
        should_stop,
    )?;
    if replayed.as_ref() == Some(solution) {
        Ok(())
    } else {
        Err(ProjectedPatternDecline::VerificationFailed)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ResidualInterval {
    lower: i128,
    upper: i128,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PatternState {
    residual: Vec<ResidualInterval>,
    signature: Vec<i128>,
}

#[derive(Debug, Clone)]
struct FrontierEntry {
    state: PatternState,
    cost: i128,
    assignment: u128,
}

#[derive(Debug)]
struct CanonicalProblem {
    num_variables: usize,
    row_lower: Vec<i128>,
    row_upper: Vec<Option<i128>>,
    local_columns: Vec<Vec<(usize, i128)>>,
    resource_columns: Vec<Vec<(usize, i128)>>,
    resource_constant: Vec<i128>,
    resource_lower: Vec<i128>,
    resource_upper: Vec<i128>,
    objective: Vec<i128>,
    objective_constant: i128,
    canonical_bytes: u64,
}

#[derive(Debug)]
struct CountPattern {
    frontier_index: u32,
    signature_index: usize,
    coordinates: Vec<usize>,
    cost: i128,
}

#[derive(Debug)]
struct CountMaster {
    block_count: usize,
    capacities: Vec<usize>,
    strides: Vec<usize>,
    state_count: usize,
    patterns: Vec<CountPattern>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CountTraversal {
    Automatic,
    #[cfg(test)]
    Dense,
    #[cfg(test)]
    Sparse,
}

impl CountMaster {
    fn detect(
        frontier: &ProjectedPatternFrontier,
        block_count: usize,
        capacities: &[i128],
        limits: ProjectedPatternCountLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Self, ProjectedPatternDecline> {
        if block_count > limits.max_blocks
            || capacities.len() > limits.max_resources
            || frontier.patterns.len() > limits.max_patterns
            || usize::try_from(frontier.num_variables).unwrap_or(usize::MAX) > u128::BITS as usize
        {
            return Err(ProjectedPatternDecline::ResourceLimit);
        }
        check_count_preflight_memory(
            block_count,
            capacities.len(),
            frontier.patterns.len(),
            limits,
        )?;
        let capacities = capacities
            .iter()
            .map(|&capacity| {
                usize::try_from(capacity).map_err(|_| ProjectedPatternDecline::UnsupportedStructure)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut strides = Vec::with_capacity(capacities.len());
        let mut state_count = 1usize;
        for (resource, &capacity) in capacities.iter().enumerate() {
            if resource & 0xff == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            strides.push(state_count);
            state_count = state_count
                .checked_mul(
                    capacity
                        .checked_add(1)
                        .ok_or(ProjectedPatternDecline::ResourceLimit)?,
                )
                .ok_or(ProjectedPatternDecline::ResourceLimit)?;
            if state_count > limits.max_signature_states {
                return Err(ProjectedPatternDecline::ResourceLimit);
            }
        }

        check_count_memory(
            state_count,
            block_count,
            capacities.len(),
            frontier.patterns.len(),
            limits,
        )?;
        let expected_assignment = usize::try_from(frontier.num_variables)
            .map_err(|_| ProjectedPatternDecline::UnsupportedStructure)?;
        let mut seen_signatures = vec![false; state_count];
        let mut patterns = Vec::with_capacity(frontier.patterns.len());
        for (frontier_index, pattern) in frontier.patterns.iter().enumerate() {
            if frontier_index & 0x3ff == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            if pattern.signature.len() != capacities.len()
                || pattern.assignment.len() != expected_assignment
            {
                return Err(ProjectedPatternDecline::UnsupportedStructure);
            }
            let mut over_capacity = false;
            let coordinates = pattern
                .signature
                .iter()
                .zip(&capacities)
                .map(|(&value, &capacity)| {
                    let coordinate = usize::try_from(value)
                        .map_err(|_| ProjectedPatternDecline::UnsupportedStructure)?;
                    over_capacity |= coordinate > capacity;
                    Ok(coordinate)
                })
                .collect::<Result<Vec<_>, _>>()?;
            if over_capacity {
                continue;
            }
            let signature_index = encode_coordinates(&coordinates, &strides)?;
            let Some(seen) = seen_signatures.get_mut(signature_index) else {
                return Err(ProjectedPatternDecline::UnsupportedStructure);
            };
            if std::mem::replace(seen, true) {
                return Err(ProjectedPatternDecline::UnsupportedStructure);
            }
            patterns.push(CountPattern {
                frontier_index: u32::try_from(frontier_index)
                    .map_err(|_| ProjectedPatternDecline::ResourceLimit)?,
                signature_index,
                coordinates,
                cost: pattern.cost,
            });
        }
        Ok(Self {
            block_count,
            capacities,
            strides,
            state_count,
            patterns,
        })
    }

    fn solve(
        &self,
        frontier: &ProjectedPatternFrontier,
        limits: ProjectedPatternCountLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Option<ProjectedPatternCountSolution>, ProjectedPatternDecline> {
        self.solve_with_traversal(frontier, limits, CountTraversal::Automatic, should_stop)
    }

    fn solve_with_traversal(
        &self,
        frontier: &ProjectedPatternFrontier,
        limits: ProjectedPatternCountLimits,
        traversal: CountTraversal,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Option<ProjectedPatternCountSolution>, ProjectedPatternDecline> {
        let mut current = vec![None::<i128>; self.state_count];
        current[0] = Some(0);
        let mut current_reachable = Vec::with_capacity(self.state_count);
        current_reachable.push(0usize);
        let mut predecessor_states = Vec::with_capacity(self.block_count);
        let mut predecessor_patterns = Vec::with_capacity(self.block_count);
        let mut transition_pairs = 0u64;
        let dense_pairs_per_layer = if self.block_count == 0 {
            0
        } else {
            self.dense_pairs_per_layer(should_stop)?
        };

        for layer in 0..self.block_count {
            if should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            transition_pairs = transition_pairs
                .checked_add(dense_pairs_per_layer)
                .ok_or(ProjectedPatternDecline::ResourceLimit)?;
            if transition_pairs > limits.max_transitions {
                return Err(ProjectedPatternDecline::ResourceLimit);
            }
            let mut next = vec![None::<i128>; self.state_count];
            let mut previous = vec![u32::MAX; self.state_count];
            let mut selected = vec![u32::MAX; self.state_count];
            let mut next_reachable = Vec::with_capacity(self.state_count);
            if use_sparse_count_traversal(
                traversal,
                current_reachable.len(),
                self.patterns.len(),
                dense_pairs_per_layer,
            )? {
                self.relax_sparse_layer(
                    &current,
                    &current_reachable,
                    &mut next,
                    &mut previous,
                    &mut selected,
                    &mut next_reachable,
                    should_stop,
                )?;
            } else {
                self.relax_dense_layer(
                    &current,
                    &mut next,
                    &mut previous,
                    &mut selected,
                    &mut next_reachable,
                    should_stop,
                )?;
            }
            if next_reachable.is_empty() {
                return Ok(None);
            }
            next_reachable.sort_unstable();
            predecessor_states.push(previous);
            predecessor_patterns.push(selected);
            current = next;
            current_reachable = next_reachable;
            if layer & 1 == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
        }

        if should_stop() {
            return Err(ProjectedPatternDecline::Interrupted);
        }
        let mut best = None::<(usize, i128)>;
        for (position, &state) in current_reachable.iter().enumerate() {
            if position & 0xfff == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            let cost = current
                .get(state)
                .copied()
                .flatten()
                .ok_or(ProjectedPatternDecline::VerificationFailed)?;
            if best.is_none_or(|incumbent| (cost, state) < (incumbent.1, incumbent.0)) {
                best = Some((state, cost));
            }
        }
        let Some((best_state, cost)) = best else {
            return Ok(None);
        };
        let mut state = best_state;
        let mut pattern_indices = Vec::with_capacity(self.block_count);
        for layer in (0..self.block_count).rev() {
            let pattern = predecessor_patterns[layer][state];
            let previous = predecessor_states[layer][state];
            if pattern == u32::MAX || previous == u32::MAX {
                return Err(ProjectedPatternDecline::VerificationFailed);
            }
            pattern_indices.push(pattern);
            state = usize::try_from(previous)
                .map_err(|_| ProjectedPatternDecline::VerificationFailed)?;
        }
        pattern_indices.reverse();
        if state != 0 {
            return Err(ProjectedPatternDecline::VerificationFailed);
        }
        let used_resources = decode_coordinates(best_state, &self.capacities, &self.strides)?
            .into_iter()
            .map(|value| i128::try_from(value).map_err(|_| ProjectedPatternDecline::ResourceLimit))
            .collect::<Result<Vec<_>, _>>()?;
        check_selected_patterns(
            frontier,
            &pattern_indices,
            &used_resources,
            cost,
            self.block_count,
        )?;
        Ok(Some(ProjectedPatternCountSolution {
            cost,
            pattern_indices,
            used_resources,
            transition_pairs,
        }))
    }

    fn dense_pairs_per_layer(
        &self,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<u64, ProjectedPatternDecline> {
        let mut dense_pairs = 0u64;
        for (pattern_position, pattern) in self.patterns.iter().enumerate() {
            if pattern_position & 0xff == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            if pattern.coordinates.len() != self.capacities.len() {
                return Err(ProjectedPatternDecline::VerificationFailed);
            }
            let compatible_pairs = compatible_count_pairs(&self.capacities, &pattern.coordinates)?;
            dense_pairs = dense_pairs
                .checked_add(compatible_pairs)
                .ok_or(ProjectedPatternDecline::ResourceLimit)?;
        }
        Ok(dense_pairs)
    }

    fn relax_dense_layer(
        &self,
        current: &[Option<i128>],
        next: &mut [Option<i128>],
        previous: &mut [u32],
        selected: &mut [u32],
        next_reachable: &mut Vec<usize>,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(), ProjectedPatternDecline> {
        for (pattern_position, pattern) in self.patterns.iter().enumerate() {
            if pattern_position & 0xff == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            let maxima = self
                .capacities
                .iter()
                .zip(&pattern.coordinates)
                .map(|(&capacity, &used)| {
                    capacity
                        .checked_sub(used)
                        .ok_or(ProjectedPatternDecline::VerificationFailed)
                })
                .collect::<Result<Vec<_>, _>>()?;
            for_each_mixed_radix_index(
                &maxima,
                &self.strides,
                pattern.signature_index,
                should_stop,
                |source, destination| {
                    relax_count_transition(
                        current,
                        next,
                        previous,
                        selected,
                        next_reachable,
                        source,
                        destination,
                        pattern,
                    )
                },
            )?;
        }
        Ok(())
    }

    fn relax_sparse_layer(
        &self,
        current: &[Option<i128>],
        current_reachable: &[usize],
        next: &mut [Option<i128>],
        previous: &mut [u32],
        selected: &mut [u32],
        next_reachable: &mut Vec<usize>,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(), ProjectedPatternDecline> {
        let mut candidate_pairs = 0u64;
        let mut source_coordinates = vec![0usize; self.capacities.len()];
        for (source_position, &source) in current_reachable.iter().enumerate() {
            if source_position & 0xfff == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            if current.get(source).copied().flatten().is_none() {
                return Err(ProjectedPatternDecline::VerificationFailed);
            }
            decode_coordinates_into(
                source,
                &self.capacities,
                &self.strides,
                &mut source_coordinates,
            )?;
            for pattern in &self.patterns {
                if candidate_pairs & 0xfff == 0 && should_stop() {
                    return Err(ProjectedPatternDecline::Interrupted);
                }
                candidate_pairs = candidate_pairs
                    .checked_add(1)
                    .ok_or(ProjectedPatternDecline::ResourceLimit)?;
                if pattern.coordinates.len() != source_coordinates.len() {
                    return Err(ProjectedPatternDecline::VerificationFailed);
                }
                let fits = source_coordinates
                    .iter()
                    .zip(&self.capacities)
                    .zip(&pattern.coordinates)
                    .all(|((&used, &capacity), &additional)| {
                        additional <= capacity && used <= capacity - additional
                    });
                if !fits {
                    continue;
                }
                let destination = source
                    .checked_add(pattern.signature_index)
                    .filter(|&value| value < self.state_count)
                    .ok_or(ProjectedPatternDecline::VerificationFailed)?;
                relax_count_transition(
                    current,
                    next,
                    previous,
                    selected,
                    next_reachable,
                    source,
                    destination,
                    pattern,
                )?;
            }
        }
        Ok(())
    }
}

fn use_sparse_count_traversal(
    traversal: CountTraversal,
    reachable_states: usize,
    patterns: usize,
    dense_pairs: u64,
) -> Result<bool, ProjectedPatternDecline> {
    let sparse_pairs = u64::try_from(reachable_states).ok().and_then(|states| {
        u64::try_from(patterns)
            .ok()
            .and_then(|patterns| states.checked_mul(patterns))
    });
    match traversal {
        CountTraversal::Automatic => Ok(sparse_pairs.is_some_and(|pairs| pairs <= dense_pairs)),
        #[cfg(test)]
        CountTraversal::Dense => Ok(false),
        #[cfg(test)]
        CountTraversal::Sparse => sparse_pairs
            .filter(|&pairs| pairs <= dense_pairs)
            .map(|_| true)
            .ok_or(ProjectedPatternDecline::ResourceLimit),
    }
}

#[allow(clippy::too_many_arguments)]
fn relax_count_transition(
    current: &[Option<i128>],
    next: &mut [Option<i128>],
    previous: &mut [u32],
    selected: &mut [u32],
    next_reachable: &mut Vec<usize>,
    source: usize,
    destination: usize,
    pattern: &CountPattern,
) -> Result<(), ProjectedPatternDecline> {
    let Some(source_cost) = current.get(source).copied().flatten() else {
        return Ok(());
    };
    if destination >= next.len() || destination >= previous.len() || destination >= selected.len() {
        return Err(ProjectedPatternDecline::VerificationFailed);
    }
    let candidate = source_cost
        .checked_add(pattern.cost)
        .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
    let source_u32 = u32::try_from(source).map_err(|_| ProjectedPatternDecline::ResourceLimit)?;
    let improve = match next[destination] {
        None => true,
        Some(incumbent) if candidate < incumbent => true,
        Some(incumbent) if candidate == incumbent => {
            (pattern.frontier_index, source_u32) < (selected[destination], previous[destination])
        }
        Some(_) => false,
    };
    if improve {
        if next[destination].is_none() {
            next_reachable.push(destination);
        }
        next[destination] = Some(candidate);
        previous[destination] = source_u32;
        selected[destination] = pattern.frontier_index;
    }
    Ok(())
}

impl CanonicalProblem {
    fn detect(
        instance: &PbInstance,
        resources: &[ProjectedPatternResource],
        limits: ProjectedPatternLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Self, ProjectedPatternDecline> {
        let num_variables = usize::try_from(instance.num_vars)
            .map_err(|_| ProjectedPatternDecline::ResourceLimit)?;
        let row_count = instance.constraints.len();
        if num_variables > limits.max_variables
            || num_variables > u128::BITS as usize
            || row_count > limits.max_rows
            || resources.len() > limits.max_resources
        {
            return Err(ProjectedPatternDecline::ResourceLimit);
        }
        if instance.num_constraints != 0
            && usize::try_from(instance.num_constraints).unwrap_or(usize::MAX) != row_count
        {
            return Err(ProjectedPatternDecline::UnsupportedStructure);
        }
        for resource in resources {
            if resource.minimum > resource.maximum {
                return Err(ProjectedPatternDecline::UnsupportedStructure);
            }
        }
        let raw_terms = count_raw_terms(instance, resources, limits.max_terms)?;
        let canonical_bytes =
            canonical_allocation_estimate(num_variables, row_count, resources.len(), raw_terms)?;
        if canonical_bytes > limits.memory_budget_bytes {
            return Err(ProjectedPatternDecline::MemoryLimit);
        }

        let mut row_lower = Vec::with_capacity(row_count);
        let mut row_upper = Vec::with_capacity(row_count);
        let mut local_columns = vec![Vec::<(usize, i128)>::new(); num_variables];
        for (row_index, row) in instance.constraints.iter().enumerate() {
            if row_index & 0x3f == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            let (constant, coefficients) =
                canonicalize_expression(&row.terms, num_variables, should_stop)?;
            let rhs = row
                .rhs
                .checked_sub(constant)
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
            row_lower.push(rhs);
            row_upper.push(match row.rel {
                PbRel::Ge => None,
                PbRel::Eq => Some(rhs),
            });
            for (variable, coefficient) in coefficients {
                local_columns[variable].push((row_index, coefficient));
            }
        }

        let mut resource_columns = vec![Vec::<(usize, i128)>::new(); num_variables];
        let mut resource_constant = Vec::with_capacity(resources.len());
        let mut resource_lower = Vec::with_capacity(resources.len());
        let mut resource_upper = Vec::with_capacity(resources.len());
        for (resource_index, resource) in resources.iter().enumerate() {
            if resource_index & 0x3f == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            let (constant, coefficients) =
                canonicalize_expression(&resource.expression.terms, num_variables, should_stop)?;
            resource_constant.push(constant);
            resource_lower.push(resource.minimum);
            resource_upper.push(resource.maximum);
            for (variable, coefficient) in coefficients {
                resource_columns[variable].push((resource_index, coefficient));
            }
        }

        let (objective_constant, objective_map) = match &instance.objective {
            Some(objective) => {
                canonicalize_expression(&objective.terms, num_variables, should_stop)?
            }
            None => (0, BTreeMap::new()),
        };
        let mut objective = vec![0i128; num_variables];
        for (variable, coefficient) in objective_map {
            objective[variable] = coefficient;
        }

        Ok(Self {
            num_variables,
            row_lower,
            row_upper,
            local_columns,
            resource_columns,
            resource_constant,
            resource_lower,
            resource_upper,
            objective,
            objective_constant,
            canonical_bytes,
        })
    }

    fn variable_order(&self) -> Vec<usize> {
        let mut variables = (0..self.num_variables).collect::<Vec<_>>();
        variables.sort_unstable_by(|&left, &right| {
            let left_local = &self.local_columns[left];
            let right_local = &self.local_columns[right];
            let left_resource = &self.resource_columns[left];
            let right_resource = &self.resource_columns[right];
            let left_weight = expression_weight(left_local)
                .saturating_add(expression_weight(left_resource))
                .saturating_add(self.objective[left].unsigned_abs());
            let right_weight = expression_weight(right_local)
                .saturating_add(expression_weight(right_resource))
                .saturating_add(self.objective[right].unsigned_abs());
            right_local
                .len()
                .cmp(&left_local.len())
                .then_with(|| right_resource.len().cmp(&left_resource.len()))
                .then_with(|| right_weight.cmp(&left_weight))
                .then_with(|| left.cmp(&right))
        });
        variables
    }

    fn enumerate(
        &self,
        limits: ProjectedPatternLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<ProjectedPatternFrontier, ProjectedPatternDecline> {
        if limits.max_states == 0 {
            return Err(ProjectedPatternDecline::ResourceLimit);
        }
        check_memory(self, 1, 0, limits)?;
        let variable_order = self.variable_order();
        let (root, mut local_min, mut local_max) = self.initial_local_state(should_stop)?;
        let (mut resource_min, mut resource_max) = self.initial_resource_suffix(should_stop)?;
        let mut retained_states = 1usize;
        let mut transition_work = 0u64;
        let Some(root) = root else {
            return Ok(ProjectedPatternFrontier {
                num_variables: self.num_variables as u32,
                patterns: Vec::new(),
                retained_states: 1,
                transition_work: 0,
            });
        };
        if !self.resource_interval_possible(
            &self.resource_constant,
            &resource_min,
            &resource_max,
        )? {
            return Ok(ProjectedPatternFrontier {
                num_variables: self.num_variables as u32,
                patterns: Vec::new(),
                retained_states: 1,
                transition_work: 0,
            });
        }

        let mut current = vec![FrontierEntry {
            state: PatternState {
                residual: root,
                signature: self.resource_constant.clone(),
            },
            cost: self.objective_constant,
            assignment: 0,
        }];
        check_memory(self, current.len(), 0, limits)?;

        for (level, &variable) in variable_order.iter().enumerate() {
            if should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            let next_local =
                subtract_suffix(&local_min, &local_max, &self.local_columns[variable])?;
            let next_resource = subtract_suffix(
                &resource_min,
                &resource_max,
                &self.resource_columns[variable],
            )?;
            let mut next = FxHashMap::<PatternState, (i128, u128)>::default();

            for (entry_index, entry) in current.iter().enumerate() {
                if entry_index & 0x3ff == 0 && should_stop() {
                    return Err(ProjectedPatternDecline::Interrupted);
                }
                for value in [false, true] {
                    charge_transition(
                        &mut transition_work,
                        entry.state.residual.len(),
                        self.local_columns[variable].len(),
                        self.resource_columns[variable].len(),
                        limits,
                    )?;
                    let Some(residual) = transition_local(
                        &entry.state.residual,
                        &self.local_columns[variable],
                        value,
                        &next_local.0,
                        &next_local.1,
                    )?
                    else {
                        continue;
                    };
                    let mut signature = entry.state.signature.clone();
                    if value {
                        for &(resource, coefficient) in &self.resource_columns[variable] {
                            signature[resource] = signature[resource]
                                .checked_add(coefficient)
                                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
                        }
                    }
                    if !self.resource_interval_possible(
                        &signature,
                        &next_resource.0,
                        &next_resource.1,
                    )? {
                        continue;
                    }
                    let cost = if value {
                        entry
                            .cost
                            .checked_add(self.objective[variable])
                            .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?
                    } else {
                        entry.cost
                    };
                    let assignment = if value {
                        entry.assignment | (1u128 << variable)
                    } else {
                        entry.assignment
                    };
                    let state = PatternState {
                        residual,
                        signature,
                    };
                    if let Some(incumbent) = next.get_mut(&state) {
                        if cost < incumbent.0
                            || (cost == incumbent.0
                                && assignment_lex_less(assignment, incumbent.1, self.num_variables))
                        {
                            *incumbent = (cost, assignment);
                        }
                    } else {
                        let prospective = next
                            .len()
                            .checked_add(1)
                            .ok_or(ProjectedPatternDecline::ResourceLimit)?;
                        if prospective > limits.max_states.saturating_sub(retained_states) {
                            return Err(ProjectedPatternDecline::ResourceLimit);
                        }
                        if level + 1 == self.num_variables && prospective > limits.max_patterns {
                            return Err(ProjectedPatternDecline::ResourceLimit);
                        }
                        check_memory(self, current.len(), prospective, limits)?;
                        next.insert(state, (cost, assignment));
                    }
                }
            }

            retained_states = retained_states
                .checked_add(next.len())
                .ok_or(ProjectedPatternDecline::ResourceLimit)?;
            if retained_states > limits.max_states {
                return Err(ProjectedPatternDecline::ResourceLimit);
            }
            if level + 1 == self.num_variables && next.len() > limits.max_patterns {
                return Err(ProjectedPatternDecline::ResourceLimit);
            }
            check_memory(self, current.len(), next.len(), limits)?;
            current = next
                .into_iter()
                .map(|(state, (cost, assignment))| FrontierEntry {
                    state,
                    cost,
                    assignment,
                })
                .collect();
            local_min = next_local.0;
            local_max = next_local.1;
            resource_min = next_resource.0;
            resource_max = next_resource.1;
        }

        if current.len() > limits.max_patterns {
            return Err(ProjectedPatternDecline::ResourceLimit);
        }
        check_output_memory(self, current.len(), limits)?;
        if should_stop() {
            return Err(ProjectedPatternDecline::Interrupted);
        }
        let mut patterns = Vec::with_capacity(current.len());
        for (entry_index, entry) in current.into_iter().enumerate() {
            if entry_index & 0xfff == 0 && should_stop() {
                return Err(ProjectedPatternDecline::Interrupted);
            }
            patterns.push(ProjectedPattern {
                signature: entry.state.signature,
                cost: entry.cost,
                assignment: assignment_bits(entry.assignment, self.num_variables),
            });
        }
        patterns.sort_unstable_by(|left, right| {
            left.signature
                .cmp(&right.signature)
                .then_with(|| left.cost.cmp(&right.cost))
                .then_with(|| left.assignment.cmp(&right.assignment))
        });
        if should_stop() {
            return Err(ProjectedPatternDecline::Interrupted);
        }
        Ok(ProjectedPatternFrontier {
            num_variables: self.num_variables as u32,
            patterns,
            retained_states: retained_states as u64,
            transition_work,
        })
    }

    fn initial_local_state(
        &self,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(Option<Vec<ResidualInterval>>, Vec<i128>, Vec<i128>), ProjectedPatternDecline>
    {
        let (remaining_min, remaining_max) =
            suffix_bounds(self.row_lower.len(), &self.local_columns, should_stop)?;
        let mut state = Vec::with_capacity(self.row_lower.len());
        for row in 0..self.row_lower.len() {
            let lower = self.row_lower[row];
            let upper = self.row_upper[row].unwrap_or(remaining_max[row]);
            if lower > remaining_max[row] || upper < remaining_min[row] || lower > upper {
                return Ok((None, remaining_min, remaining_max));
            }
            state.push(ResidualInterval {
                lower: lower.max(remaining_min[row]),
                upper: upper.min(remaining_max[row]),
            });
        }
        Ok((Some(state), remaining_min, remaining_max))
    }

    fn initial_resource_suffix(
        &self,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(Vec<i128>, Vec<i128>), ProjectedPatternDecline> {
        suffix_bounds(
            self.resource_lower.len(),
            &self.resource_columns,
            should_stop,
        )
    }

    fn resource_interval_possible(
        &self,
        signature: &[i128],
        remaining_min: &[i128],
        remaining_max: &[i128],
    ) -> Result<bool, ProjectedPatternDecline> {
        for resource in 0..self.resource_lower.len() {
            let attainable_min = signature[resource]
                .checked_add(remaining_min[resource])
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
            let attainable_max = signature[resource]
                .checked_add(remaining_max[resource])
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
            if attainable_min > self.resource_upper[resource]
                || attainable_max < self.resource_lower[resource]
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

fn canonicalize_expression(
    terms: &[crate::PbTerm],
    num_variables: usize,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<(i128, BTreeMap<usize, i128>), ProjectedPatternDecline> {
    let mut coefficients = BTreeMap::<usize, i128>::new();
    let mut constant = 0i128;
    for (term_index, term) in terms.iter().enumerate() {
        if term_index & 0x3ff == 0 && should_stop() {
            return Err(ProjectedPatternDecline::Interrupted);
        }
        let [literal] = term.lits.as_slice() else {
            return Err(ProjectedPatternDecline::UnsupportedStructure);
        };
        let variable = literal
            .var
            .checked_sub(1)
            .and_then(|value| usize::try_from(value).ok())
            .filter(|&value| value < num_variables)
            .ok_or(ProjectedPatternDecline::UnsupportedStructure)?;
        let coefficient = if literal.negated {
            constant = constant
                .checked_add(term.coeff)
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
            term.coeff
                .checked_neg()
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?
        } else {
            term.coeff
        };
        let updated = coefficients
            .get(&variable)
            .copied()
            .unwrap_or(0)
            .checked_add(coefficient)
            .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
        if updated == 0 {
            coefficients.remove(&variable);
        } else {
            coefficients.insert(variable, updated);
        }
    }
    Ok((constant, coefficients))
}

fn expression_weight(entries: &[(usize, i128)]) -> u128 {
    entries.iter().fold(0u128, |sum, &(_, coefficient)| {
        sum.saturating_add(coefficient.unsigned_abs())
    })
}

fn suffix_bounds(
    count: usize,
    columns: &[Vec<(usize, i128)>],
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<(Vec<i128>, Vec<i128>), ProjectedPatternDecline> {
    let mut minimum = vec![0i128; count];
    let mut maximum = vec![0i128; count];
    for (variable, column) in columns.iter().enumerate() {
        if variable & 0x3ff == 0 && should_stop() {
            return Err(ProjectedPatternDecline::Interrupted);
        }
        for &(entry, coefficient) in column {
            let slot = if coefficient < 0 {
                &mut minimum[entry]
            } else {
                &mut maximum[entry]
            };
            *slot = slot
                .checked_add(coefficient)
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
        }
    }
    Ok((minimum, maximum))
}

fn subtract_suffix(
    minimum: &[i128],
    maximum: &[i128],
    column: &[(usize, i128)],
) -> Result<(Vec<i128>, Vec<i128>), ProjectedPatternDecline> {
    let mut next_minimum = minimum.to_vec();
    let mut next_maximum = maximum.to_vec();
    for &(entry, coefficient) in column {
        let slot = if coefficient < 0 {
            &mut next_minimum[entry]
        } else {
            &mut next_maximum[entry]
        };
        *slot = slot
            .checked_sub(coefficient)
            .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
    }
    Ok((next_minimum, next_maximum))
}

fn transition_local(
    state: &[ResidualInterval],
    column: &[(usize, i128)],
    value: bool,
    next_minimum: &[i128],
    next_maximum: &[i128],
) -> Result<Option<Vec<ResidualInterval>>, ProjectedPatternDecline> {
    let mut child = state.to_vec();
    for &(row, coefficient) in column {
        let mut lower = child[row].lower;
        let mut upper = child[row].upper;
        if value {
            lower = lower
                .checked_sub(coefficient)
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
            upper = upper
                .checked_sub(coefficient)
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
        }
        if lower > next_maximum[row] || upper < next_minimum[row] || lower > upper {
            return Ok(None);
        }
        child[row] = ResidualInterval {
            lower: lower.max(next_minimum[row]),
            upper: upper.min(next_maximum[row]),
        };
    }
    Ok(Some(child))
}

fn charge_transition(
    work: &mut u64,
    rows: usize,
    local_entries: usize,
    resource_entries: usize,
    limits: ProjectedPatternLimits,
) -> Result<(), ProjectedPatternDecline> {
    let delta = rows
        .checked_add(local_entries)
        .and_then(|value| value.checked_add(resource_entries))
        .and_then(|value| value.checked_add(1))
        .and_then(|value| u64::try_from(value).ok())
        .ok_or(ProjectedPatternDecline::ResourceLimit)?;
    *work = work
        .checked_add(delta)
        .ok_or(ProjectedPatternDecline::ResourceLimit)?;
    if *work > limits.max_transitions {
        return Err(ProjectedPatternDecline::ResourceLimit);
    }
    Ok(())
}

fn assignment_bits(bits: u128, num_variables: usize) -> Vec<bool> {
    (0..num_variables)
        .map(|variable| bits & (1u128 << variable) != 0)
        .collect()
}

fn assignment_lex_less(left: u128, right: u128, num_variables: usize) -> bool {
    for variable in 0..num_variables {
        let left_value = left & (1u128 << variable) != 0;
        let right_value = right & (1u128 << variable) != 0;
        if left_value != right_value {
            return !left_value;
        }
    }
    false
}

fn count_raw_terms(
    instance: &PbInstance,
    resources: &[ProjectedPatternResource],
    maximum: usize,
) -> Result<usize, ProjectedPatternDecline> {
    let mut count = 0usize;
    for row in &instance.constraints {
        count = count
            .checked_add(row.terms.len())
            .ok_or(ProjectedPatternDecline::ResourceLimit)?;
        if count > maximum {
            return Err(ProjectedPatternDecline::ResourceLimit);
        }
    }
    if let Some(objective) = &instance.objective {
        count = count
            .checked_add(objective.terms.len())
            .ok_or(ProjectedPatternDecline::ResourceLimit)?;
    }
    for resource in resources {
        count = count
            .checked_add(resource.expression.terms.len())
            .ok_or(ProjectedPatternDecline::ResourceLimit)?;
    }
    if count > maximum {
        return Err(ProjectedPatternDecline::ResourceLimit);
    }
    Ok(count)
}

fn canonical_allocation_estimate(
    variables: usize,
    rows: usize,
    resources: usize,
    terms: usize,
) -> Result<u64, ProjectedPatternDecline> {
    let slots = variables
        .checked_mul(2)
        // `row_lower: i128` plus `row_upper: Option<i128>` occupy at least
        // 48 bytes per row on the supported targets, before Vec overhead.
        // Charge two 32-byte slots so a zero-term-row corpus cannot allocate
        // past a tiny caller envelope before the root-state memory check.
        .and_then(|value| value.checked_add(rows.checked_mul(2)?))
        .and_then(|value| value.checked_add(resources.checked_mul(3)?))
        .and_then(|value| value.checked_add(terms.checked_mul(2)?))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    u64::try_from(slots)
        .ok()
        .and_then(|value| value.checked_mul(32))
        .ok_or(ProjectedPatternDecline::MemoryLimit)
}

fn check_memory(
    problem: &CanonicalProblem,
    current_states: usize,
    next_states: usize,
    limits: ProjectedPatternLimits,
) -> Result<(), ProjectedPatternDecline> {
    let state_cells = problem
        .row_lower
        .len()
        .checked_add(problem.resource_lower.len())
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let state_bytes = u64::try_from(state_cells)
        .unwrap_or(u64::MAX)
        .checked_mul(32)
        // `next` is a hashbrown table. Charge its bucket and transient
        // old-and-grown tables during rehash, in addition to the separately
        // charged heap-owned state cells.
        .and_then(|value| value.checked_add(512))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let live_states = current_states
        .checked_add(next_states)
        .and_then(|value| value.checked_add(2))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let live = u64::try_from(live_states)
        .unwrap_or(u64::MAX)
        .checked_mul(state_bytes)
        .and_then(|value| value.checked_add(problem.canonical_bytes))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    if live > limits.memory_budget_bytes {
        Err(ProjectedPatternDecline::MemoryLimit)
    } else {
        Ok(())
    }
}

fn check_output_memory(
    problem: &CanonicalProblem,
    patterns: usize,
    limits: ProjectedPatternLimits,
) -> Result<(), ProjectedPatternDecline> {
    let state_cells = problem
        .row_lower
        .len()
        .checked_add(problem.resource_lower.len())
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let state_payload = u64::try_from(state_cells)
        .unwrap_or(u64::MAX)
        .checked_mul(32)
        .and_then(|value| value.checked_add(512))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let source_bytes = u64::try_from(patterns.saturating_add(2))
        .unwrap_or(u64::MAX)
        .checked_mul(state_payload)
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let output_payload = u64::try_from(problem.num_variables)
        .unwrap_or(u64::MAX)
        .checked_add(96)
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let output_bytes = u64::try_from(patterns)
        .unwrap_or(u64::MAX)
        .checked_mul(output_payload)
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let live = problem
        .canonical_bytes
        .checked_add(source_bytes)
        .and_then(|value| value.checked_add(output_bytes))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    if live > limits.memory_budget_bytes {
        Err(ProjectedPatternDecline::MemoryLimit)
    } else {
        Ok(())
    }
}

fn encode_coordinates(
    coordinates: &[usize],
    strides: &[usize],
) -> Result<usize, ProjectedPatternDecline> {
    if coordinates.len() != strides.len() {
        return Err(ProjectedPatternDecline::UnsupportedStructure);
    }
    coordinates
        .iter()
        .zip(strides)
        .try_fold(0usize, |index, (&coordinate, &stride)| {
            index
                .checked_add(
                    coordinate
                        .checked_mul(stride)
                        .ok_or(ProjectedPatternDecline::ResourceLimit)?,
                )
                .ok_or(ProjectedPatternDecline::ResourceLimit)
        })
}

fn decode_coordinates(
    index: usize,
    capacities: &[usize],
    strides: &[usize],
) -> Result<Vec<usize>, ProjectedPatternDecline> {
    let mut coordinates = vec![0usize; capacities.len()];
    decode_coordinates_into(index, capacities, strides, &mut coordinates)?;
    Ok(coordinates)
}

fn decode_coordinates_into(
    index: usize,
    capacities: &[usize],
    strides: &[usize],
    coordinates: &mut [usize],
) -> Result<(), ProjectedPatternDecline> {
    if capacities.len() != strides.len() || coordinates.len() != capacities.len() {
        return Err(ProjectedPatternDecline::VerificationFailed);
    }
    for ((coordinate, &capacity), &stride) in coordinates.iter_mut().zip(capacities).zip(strides) {
        let radix = capacity
            .checked_add(1)
            .ok_or(ProjectedPatternDecline::ResourceLimit)?;
        *coordinate = (index / stride) % radix;
    }
    Ok(())
}

fn for_each_mixed_radix_index<F>(
    maxima: &[usize],
    strides: &[usize],
    destination_offset: usize,
    should_stop: &mut dyn FnMut() -> bool,
    mut visit: F,
) -> Result<(), ProjectedPatternDecline>
where
    F: FnMut(usize, usize) -> Result<(), ProjectedPatternDecline>,
{
    if maxima.len() != strides.len() {
        return Err(ProjectedPatternDecline::UnsupportedStructure);
    }
    let mut coordinates = vec![0usize; maxima.len()];
    let mut source = 0usize;
    let mut destination = destination_offset;
    let mut visits = 0u64;
    loop {
        if visits & 0xfff == 0 && should_stop() {
            return Err(ProjectedPatternDecline::Interrupted);
        }
        visit(source, destination)?;
        visits = visits
            .checked_add(1)
            .ok_or(ProjectedPatternDecline::ResourceLimit)?;
        let mut dimension = 0usize;
        loop {
            if dimension == maxima.len() {
                return Ok(());
            }
            if coordinates[dimension] < maxima[dimension] {
                coordinates[dimension] += 1;
                source = source
                    .checked_add(strides[dimension])
                    .ok_or(ProjectedPatternDecline::ResourceLimit)?;
                destination = destination
                    .checked_add(strides[dimension])
                    .ok_or(ProjectedPatternDecline::ResourceLimit)?;
                break;
            }
            let rewind = coordinates[dimension]
                .checked_mul(strides[dimension])
                .ok_or(ProjectedPatternDecline::ResourceLimit)?;
            source = source
                .checked_sub(rewind)
                .ok_or(ProjectedPatternDecline::VerificationFailed)?;
            destination = destination
                .checked_sub(rewind)
                .ok_or(ProjectedPatternDecline::VerificationFailed)?;
            coordinates[dimension] = 0;
            dimension += 1;
        }
    }
}

fn compatible_count_pairs(
    capacities: &[usize],
    used: &[usize],
) -> Result<u64, ProjectedPatternDecline> {
    if capacities.len() != used.len() {
        return Err(ProjectedPatternDecline::VerificationFailed);
    }
    capacities
        .iter()
        .zip(used)
        .try_fold(1u64, |count, (&capacity, &used)| {
            let maximum = capacity
                .checked_sub(used)
                .ok_or(ProjectedPatternDecline::VerificationFailed)?;
            let choices = maximum
                .checked_add(1)
                .and_then(|value| u64::try_from(value).ok())
                .ok_or(ProjectedPatternDecline::ResourceLimit)?;
            count
                .checked_mul(choices)
                .ok_or(ProjectedPatternDecline::ResourceLimit)
        })
}

fn check_selected_patterns(
    frontier: &ProjectedPatternFrontier,
    pattern_indices: &[u32],
    used_resources: &[i128],
    claimed_cost: i128,
    block_count: usize,
) -> Result<(), ProjectedPatternDecline> {
    if pattern_indices.len() != block_count {
        return Err(ProjectedPatternDecline::VerificationFailed);
    }
    let mut resources = vec![0i128; used_resources.len()];
    let mut cost = 0i128;
    for &pattern_index in pattern_indices {
        let pattern = frontier
            .patterns
            .get(
                usize::try_from(pattern_index)
                    .map_err(|_| ProjectedPatternDecline::VerificationFailed)?,
            )
            .ok_or(ProjectedPatternDecline::VerificationFailed)?;
        if pattern.signature.len() != resources.len() {
            return Err(ProjectedPatternDecline::VerificationFailed);
        }
        cost = cost
            .checked_add(pattern.cost)
            .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
        for (total, &usage) in resources.iter_mut().zip(&pattern.signature) {
            *total = total
                .checked_add(usage)
                .ok_or(ProjectedPatternDecline::ArithmeticOverflow)?;
        }
    }
    if cost != claimed_cost || resources != used_resources {
        return Err(ProjectedPatternDecline::VerificationFailed);
    }
    Ok(())
}

fn check_count_memory(
    states: usize,
    blocks: usize,
    resources: usize,
    patterns: usize,
    limits: ProjectedPatternCountLimits,
) -> Result<(), ProjectedPatternDecline> {
    // The 96-byte per-state table charge includes two cost tables
    // (conservatively 32 bytes per `Option<i128>`), current and next reachable
    // `usize` vectors (16 bytes), and 16 bytes for the signature-seen bitmap,
    // padding, and allocation slack. Predecessor layers (two u32 arrays) and
    // pattern/resource coordinate storage are charged separately below.
    let table_bytes = u64::try_from(states)
        .unwrap_or(u64::MAX)
        .checked_mul(96)
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let predecessor_bytes = u64::try_from(states)
        .unwrap_or(u64::MAX)
        .checked_mul(u64::try_from(blocks).unwrap_or(u64::MAX))
        .and_then(|value| value.checked_mul(8))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let pattern_bytes = u64::try_from(patterns)
        .unwrap_or(u64::MAX)
        .checked_mul(
            u64::try_from(resources)
                .unwrap_or(u64::MAX)
                .checked_mul(8)
                .and_then(|value| value.checked_add(64))
                .ok_or(ProjectedPatternDecline::MemoryLimit)?,
        )
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let scratch_bytes = u64::try_from(resources)
        .unwrap_or(u64::MAX)
        .checked_mul(128)
        .and_then(|value| value.checked_add(512))
        .and_then(|value| {
            value.checked_add(u64::try_from(blocks).unwrap_or(u64::MAX).saturating_mul(8))
        })
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let total = table_bytes
        .checked_add(predecessor_bytes)
        .and_then(|value| value.checked_add(pattern_bytes))
        .and_then(|value| value.checked_add(scratch_bytes))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    if total > limits.memory_budget_bytes {
        Err(ProjectedPatternDecline::MemoryLimit)
    } else {
        Ok(())
    }
}

fn check_count_preflight_memory(
    blocks: usize,
    resources: usize,
    patterns: usize,
    limits: ProjectedPatternCountLimits,
) -> Result<(), ProjectedPatternDecline> {
    // This check intentionally precedes copying the capacity slice or
    // allocating strides/pattern storage. The later state-count-aware gate is
    // stronger; this one makes the advertised envelope true even when every
    // radix is one and the dense table itself has a single cell.
    let resource_bytes = u64::try_from(resources)
        .unwrap_or(u64::MAX)
        .checked_mul(128)
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let pattern_bytes = u64::try_from(patterns)
        .unwrap_or(u64::MAX)
        .checked_mul(64)
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let block_bytes = u64::try_from(blocks)
        .unwrap_or(u64::MAX)
        .checked_mul(8)
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    let total = resource_bytes
        .checked_add(pattern_bytes)
        .and_then(|value| value.checked_add(block_bytes))
        .and_then(|value| value.checked_add(512))
        .ok_or(ProjectedPatternDecline::MemoryLimit)?;
    if total > limits.memory_budget_bytes {
        Err(ProjectedPatternDecline::MemoryLimit)
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{PbConstraint, PbLit, PbTerm};

    fn term(coefficient: i128, variable: u32) -> PbTerm {
        PbTerm {
            coeff: coefficient,
            lits: vec![PbLit {
                var: variable,
                negated: false,
            }],
        }
    }

    fn negated_term(coefficient: i128, variable: u32) -> PbTerm {
        PbTerm {
            coeff: coefficient,
            lits: vec![PbLit {
                var: variable,
                negated: true,
            }],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    fn instance(
        variables: u32,
        constraints: Vec<PbConstraint>,
        objective: Vec<PbTerm>,
    ) -> PbInstance {
        PbInstance {
            num_vars: variables,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(PbObjective { terms: objective }),
        }
    }

    fn resource(terms: Vec<PbTerm>, minimum: i128, maximum: i128) -> ProjectedPatternResource {
        ProjectedPatternResource {
            expression: PbObjective { terms },
            minimum,
            maximum,
        }
    }

    #[test]
    fn keeps_the_cheapest_assignment_for_each_signature() {
        let problem = instance(
            2,
            vec![ge(vec![term(1, 1), term(1, 2)], 1)],
            vec![term(3, 1), term(1, 2)],
        );
        let resources = vec![resource(vec![term(1, 1), term(1, 2)], 0, 2)];
        let frontier =
            enumerate_projected_patterns_interruptible(&problem, &resources, || false).unwrap();
        assert_eq!(
            frontier.patterns,
            vec![
                ProjectedPattern {
                    signature: vec![1],
                    cost: 1,
                    assignment: vec![false, true],
                },
                ProjectedPattern {
                    signature: vec![2],
                    cost: 4,
                    assignment: vec![true, true],
                },
            ]
        );
    }

    #[test]
    fn equality_negated_literals_and_resource_bounds_are_exact() {
        let problem = instance(
            3,
            vec![eq(vec![negated_term(2, 1), term(1, 2), term(1, 3)], 2)],
            vec![negated_term(5, 1), term(-2, 2), term(1, 3)],
        );
        let resources = vec![resource(
            vec![negated_term(3, 1), term(2, 2), term(1, 3)],
            1,
            4,
        )];
        let frontier =
            enumerate_projected_patterns_interruptible(&problem, &resources, || false).unwrap();
        let expected = exhaustive_frontier(&problem, &resources);
        assert_eq!(frontier.patterns, expected);
    }

    #[test]
    fn exhaustive_small_systems_match_direct_enumeration() {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        for variables in 0..=8u32 {
            for _ in 0..32 {
                let mut rows = Vec::new();
                for row_index in 0..3 {
                    let mut terms = Vec::new();
                    for variable in 1..=variables {
                        let raw = next_random(&mut seed);
                        let coefficient = (raw % 7) as i128 - 3;
                        if coefficient != 0 {
                            if raw & 8 == 0 {
                                terms.push(negated_term(coefficient, variable));
                            } else {
                                terms.push(term(coefficient, variable));
                            }
                        }
                    }
                    let rhs = (next_random(&mut seed) % 9) as i128 - 4;
                    rows.push(if row_index == 0 && next_random(&mut seed) & 1 == 0 {
                        eq(terms, rhs)
                    } else {
                        ge(terms, rhs)
                    });
                }
                let objective = (1..=variables)
                    .filter_map(|variable| {
                        let coefficient = (next_random(&mut seed) % 9) as i128 - 4;
                        (coefficient != 0).then(|| term(coefficient, variable))
                    })
                    .collect();
                let problem = instance(variables, rows, objective);
                let resources = vec![
                    resource(
                        (1..=variables)
                            .filter_map(|variable| {
                                let coefficient = (next_random(&mut seed) % 4) as i128;
                                (coefficient != 0).then(|| term(coefficient, variable))
                            })
                            .collect(),
                        0,
                        10,
                    ),
                    resource(
                        (1..=variables)
                            .filter_map(|variable| {
                                let coefficient = (next_random(&mut seed) % 3) as i128 - 1;
                                (coefficient != 0).then(|| term(coefficient, variable))
                            })
                            .collect(),
                        -3,
                        3,
                    ),
                ];
                let frontier =
                    enumerate_projected_patterns_interruptible(&problem, &resources, || false)
                        .unwrap();
                assert_eq!(frontier.patterns, exhaustive_frontier(&problem, &resources));
            }
        }
    }

    #[test]
    fn replay_rejects_value_signature_assignment_and_accounting_tampering() {
        let problem = instance(
            2,
            vec![ge(vec![term(1, 1), term(1, 2)], 1)],
            vec![term(2, 1), term(1, 2)],
        );
        let resources = vec![resource(vec![term(1, 1), term(2, 2)], 0, 3)];
        let frontier =
            enumerate_projected_patterns_interruptible(&problem, &resources, || false).unwrap();
        verify_projected_pattern_frontier_interruptible(&problem, &resources, &frontier, || false)
            .unwrap();

        let mut cost = frontier.clone();
        cost.patterns[0].cost += 1;
        assert_eq!(
            verify_projected_pattern_frontier_interruptible(&problem, &resources, &cost, || false),
            Err(ProjectedPatternDecline::VerificationFailed)
        );
        let mut signature = frontier.clone();
        signature.patterns[0].signature[0] += 1;
        assert!(verify_projected_pattern_frontier_interruptible(
            &problem,
            &resources,
            &signature,
            || false
        )
        .is_err());
        let mut assignment = frontier.clone();
        assignment.patterns[0].assignment[0] = !assignment.patterns[0].assignment[0];
        assert!(verify_projected_pattern_frontier_interruptible(
            &problem,
            &resources,
            &assignment,
            || false
        )
        .is_err());
        let mut accounting = frontier.clone();
        accounting.transition_work += 1;
        assert!(verify_projected_pattern_frontier_interruptible(
            &problem,
            &resources,
            &accounting,
            || false
        )
        .is_err());
    }

    #[test]
    fn interruption_and_every_resource_cap_decline_without_a_partial_frontier() {
        let problem = instance(
            6,
            vec![ge((1..=6).map(|variable| term(1, variable)).collect(), 1)],
            vec![term(1, 1)],
        );
        let resources = vec![resource(
            (1..=6).map(|variable| term(1, variable)).collect(),
            0,
            6,
        )];
        assert_eq!(
            enumerate_projected_patterns_interruptible(&problem, &resources, || true),
            Err(ProjectedPatternDecline::Interrupted)
        );

        let baseline = ProjectedPatternLimits::default();
        for limits in [
            ProjectedPatternLimits {
                max_variables: 5,
                ..baseline
            },
            ProjectedPatternLimits {
                max_rows: 0,
                ..baseline
            },
            ProjectedPatternLimits {
                max_resources: 0,
                ..baseline
            },
            ProjectedPatternLimits {
                max_terms: 1,
                ..baseline
            },
            ProjectedPatternLimits {
                max_states: 1,
                ..baseline
            },
            ProjectedPatternLimits {
                max_transitions: 1,
                ..baseline
            },
            ProjectedPatternLimits {
                max_patterns: 1,
                ..baseline
            },
        ] {
            assert!(matches!(
                enumerate_projected_patterns_with_limits(&problem, &resources, limits, || false),
                Err(ProjectedPatternDecline::ResourceLimit)
                    | Err(ProjectedPatternDecline::UnsupportedStructure)
            ));
        }
        let memory = ProjectedPatternLimits {
            memory_budget_bytes: 1,
            ..baseline
        };
        assert_eq!(
            enumerate_projected_patterns_with_limits(&problem, &resources, memory, || false),
            Err(ProjectedPatternDecline::MemoryLimit)
        );

        let empty_rows = instance(0, (0..128).map(|_| ge(Vec::new(), 0)).collect(), Vec::new());
        let row_memory = ProjectedPatternLimits {
            memory_budget_bytes: 128 * 48,
            ..baseline
        };
        assert_eq!(
            enumerate_projected_patterns_with_limits(&empty_rows, &[], row_memory, || false),
            Err(ProjectedPatternDecline::MemoryLimit)
        );
    }

    #[test]
    fn malformed_terms_and_arithmetic_overflow_decline() {
        let nonlinear = PbTerm {
            coeff: 1,
            lits: vec![
                PbLit {
                    var: 1,
                    negated: false,
                },
                PbLit {
                    var: 2,
                    negated: false,
                },
            ],
        };
        let problem = instance(2, vec![ge(vec![nonlinear], 0)], vec![]);
        assert_eq!(
            enumerate_projected_patterns_interruptible(&problem, &[], || false),
            Err(ProjectedPatternDecline::UnsupportedStructure)
        );

        let overflow = instance(
            1,
            vec![],
            vec![negated_term(i128::MAX, 1), negated_term(1, 1)],
        );
        assert_eq!(
            enumerate_projected_patterns_interruptible(&overflow, &[], || false),
            Err(ProjectedPatternDecline::ArithmeticOverflow)
        );
    }

    #[test]
    fn count_master_enforces_exact_block_count_and_packing_capacities() {
        let frontier = manual_frontier(vec![
            (vec![0, 0], 10),
            (vec![0, 1], 2),
            (vec![0, 2], 5),
            (vec![1, 0], 1),
        ]);
        let solution = solve_projected_pattern_count_interruptible(&frontier, 2, &[1, 2], || false)
            .unwrap()
            .unwrap();
        assert_eq!(solution.cost, 3);
        assert_eq!(solution.pattern_indices, vec![3, 1]);
        assert_eq!(solution.used_resources, vec![1, 1]);
        verify_projected_pattern_count_solution_interruptible(
            &frontier,
            2,
            &[1, 2],
            &solution,
            || false,
        )
        .unwrap();

        let empty = solve_projected_pattern_count_interruptible(&frontier, 0, &[1, 2], || false)
            .unwrap()
            .unwrap();
        assert_eq!(empty.cost, 0);
        assert!(empty.pattern_indices.is_empty());
        assert_eq!(empty.used_resources, vec![0, 0]);

        // A complete local frontier may legitimately contain a pattern that
        // cannot fit this particular count master. It is filtered, not treated
        // as corruption of all otherwise usable patterns.
        let with_oversized = manual_frontier(vec![(vec![0], 4), (vec![1], 2), (vec![3], -100)]);
        let filtered =
            solve_projected_pattern_count_interruptible(&with_oversized, 1, &[1], || false)
                .unwrap()
                .unwrap();
        assert_eq!(filtered.cost, 2);
        assert_eq!(filtered.pattern_indices, vec![1]);
    }

    #[test]
    fn count_master_matches_exhaustive_pattern_products() {
        let mut seed = 0xd1b5_4a32_d192_ed03u64;
        for _ in 0..128 {
            let mut by_signature = BTreeMap::new();
            for left in 0..=2i128 {
                for right in 0..=2i128 {
                    if next_random(&mut seed) & 3 != 0 {
                        by_signature
                            .insert(vec![left, right], (next_random(&mut seed) % 17) as i128 - 8);
                    }
                }
            }
            let frontier = manual_frontier(by_signature.into_iter().collect());
            for blocks in 0..=4 {
                let actual =
                    solve_projected_pattern_count_interruptible(&frontier, blocks, &[2, 2], || {
                        false
                    })
                    .unwrap();
                let expected = exhaustive_count_cost(&frontier, blocks, &[2, 2]);
                assert_eq!(actual.as_ref().map(|solution| solution.cost), expected);
                if let Some(solution) = actual {
                    verify_projected_pattern_count_solution_interruptible(
                        &frontier,
                        blocks,
                        &[2, 2],
                        &solution,
                        || false,
                    )
                    .unwrap();
                }
            }
        }
    }

    #[test]
    fn sparse_and_dense_count_traversals_preserve_total_tie_order() {
        let frontier = manual_frontier(vec![(vec![1, 0], 0), (vec![0, 1], 0)]);
        let expected = ProjectedPatternCountSolution {
            cost: 0,
            pattern_indices: vec![1, 0],
            used_resources: vec![1, 1],
            transition_pairs: 8,
        };
        for traversal in [
            CountTraversal::Automatic,
            CountTraversal::Dense,
            CountTraversal::Sparse,
        ] {
            for _ in 0..4 {
                assert_eq!(
                    solve_count_with_traversal_for_test(
                        &frontier,
                        2,
                        &[1, 1],
                        ProjectedPatternCountLimits::default(),
                        traversal,
                    ),
                    Ok(Some(expected.clone()))
                );
            }
        }

        // The final tie remains ordered by `(cost, state)`, independently of
        // traversal order and of the frontier's pattern order.
        let final_tie = manual_frontier(vec![(vec![1], 0), (vec![0], 0)]);
        for traversal in [
            CountTraversal::Automatic,
            CountTraversal::Dense,
            CountTraversal::Sparse,
        ] {
            let solution = solve_count_with_traversal_for_test(
                &final_tie,
                1,
                &[1],
                ProjectedPatternCountLimits::default(),
                traversal,
            )
            .unwrap()
            .unwrap();
            assert_eq!(solution.pattern_indices, vec![1]);
            assert_eq!(solution.used_resources, vec![0]);
        }
    }

    #[test]
    fn sparse_count_traversal_rejects_mixed_radix_carry() {
        let frontier = manual_frontier(vec![(vec![1, 0], 0)]);
        for traversal in [
            CountTraversal::Automatic,
            CountTraversal::Dense,
            CountTraversal::Sparse,
        ] {
            assert_eq!(
                solve_count_with_traversal_for_test(
                    &frontier,
                    2,
                    &[1, 1],
                    ProjectedPatternCountLimits::default(),
                    traversal,
                ),
                Ok(None)
            );
        }
    }

    #[test]
    fn sparse_count_traversal_preserves_dense_transition_cap_accounting() {
        let frontier = manual_frontier(vec![(vec![1, 0], 0), (vec![0, 1], 0)]);
        let exact = ProjectedPatternCountLimits {
            max_transitions: 8,
            ..ProjectedPatternCountLimits::default()
        };
        let solution =
            solve_projected_pattern_count_with_limits(&frontier, 2, &[1, 1], exact, || false)
                .unwrap()
                .unwrap();
        assert_eq!(solution.transition_pairs, 8);

        let short = ProjectedPatternCountLimits {
            max_transitions: 7,
            ..exact
        };
        assert_eq!(
            solve_projected_pattern_count_with_limits(&frontier, 2, &[1, 1], short, || false,),
            Err(ProjectedPatternDecline::ResourceLimit)
        );
    }

    #[test]
    fn sparse_count_traversal_polls_long_candidate_scans() {
        let state_count = 5_000usize;
        let master = CountMaster {
            block_count: 1,
            capacities: vec![state_count - 1],
            strides: vec![1],
            state_count,
            patterns: vec![CountPattern {
                frontier_index: 0,
                signature_index: 0,
                coordinates: vec![0],
                cost: 0,
            }],
        };
        let current = vec![Some(0); state_count];
        let current_reachable = (0..state_count).collect::<Vec<_>>();
        let mut next = vec![None; state_count];
        let mut previous = vec![u32::MAX; state_count];
        let mut selected = vec![u32::MAX; state_count];
        let mut next_reachable = Vec::with_capacity(state_count);
        let polls = std::cell::Cell::new(0usize);
        assert_eq!(
            master.relax_sparse_layer(
                &current,
                &current_reachable,
                &mut next,
                &mut previous,
                &mut selected,
                &mut next_reachable,
                &mut || {
                    let next = polls.get() + 1;
                    polls.set(next);
                    next >= 4
                },
            ),
            Err(ProjectedPatternDecline::Interrupted)
        );
        assert_eq!(polls.get(), 4);
    }

    #[test]
    fn count_replay_rejects_tampering_and_limits_fail_closed() {
        let frontier = manual_frontier(vec![(vec![0, 0], 3), (vec![1, 0], 1)]);
        let solution = solve_projected_pattern_count_interruptible(&frontier, 2, &[2, 1], || false)
            .unwrap()
            .unwrap();
        for tamper in 0..4 {
            let mut edited = solution.clone();
            match tamper {
                0 => edited.cost += 1,
                1 => edited.pattern_indices[0] ^= 1,
                2 => edited.used_resources[0] += 1,
                3 => edited.transition_pairs += 1,
                _ => unreachable!(),
            }
            assert_eq!(
                verify_projected_pattern_count_solution_interruptible(
                    &frontier,
                    2,
                    &[2, 1],
                    &edited,
                    || false,
                ),
                Err(ProjectedPatternDecline::VerificationFailed)
            );
        }
        assert_eq!(
            solve_projected_pattern_count_interruptible(&frontier, 2, &[2, 1], || true),
            Err(ProjectedPatternDecline::Interrupted)
        );

        let long_scan = manual_frontier(vec![(vec![0], 0)]);
        let polls = std::cell::Cell::new(0usize);
        assert_eq!(
            solve_projected_pattern_count_interruptible(&long_scan, 1, &[10_000], || {
                let next = polls.get() + 1;
                polls.set(next);
                next >= 8
            }),
            Err(ProjectedPatternDecline::Interrupted)
        );
        assert!(polls.get() >= 8);

        let baseline = ProjectedPatternCountLimits::default();
        for limits in [
            ProjectedPatternCountLimits {
                max_blocks: 1,
                ..baseline
            },
            ProjectedPatternCountLimits {
                max_resources: 1,
                ..baseline
            },
            ProjectedPatternCountLimits {
                max_patterns: 1,
                ..baseline
            },
            ProjectedPatternCountLimits {
                max_signature_states: 5,
                ..baseline
            },
            ProjectedPatternCountLimits {
                max_transitions: 0,
                ..baseline
            },
        ] {
            assert_eq!(
                solve_projected_pattern_count_with_limits(&frontier, 2, &[2, 1], limits, || false,),
                Err(ProjectedPatternDecline::ResourceLimit)
            );
        }
        let memory = ProjectedPatternCountLimits {
            memory_budget_bytes: 1,
            ..baseline
        };
        assert_eq!(
            solve_projected_pattern_count_with_limits(&frontier, 2, &[2, 1], memory, || false,),
            Err(ProjectedPatternDecline::MemoryLimit)
        );

        let many_zero_radices = vec![0; 4_096];
        let dimension_memory = ProjectedPatternCountLimits {
            max_resources: many_zero_radices.len(),
            memory_budget_bytes: 100_000,
            ..baseline
        };
        assert_eq!(
            solve_projected_pattern_count_with_limits(
                &manual_frontier(vec![(vec![0; many_zero_radices.len()], 0)]),
                1,
                &many_zero_radices,
                dimension_memory,
                || false,
            ),
            Err(ProjectedPatternDecline::MemoryLimit)
        );
    }

    #[test]
    fn count_master_rejects_malformed_signatures_and_cost_overflow() {
        let duplicate = manual_frontier(vec![(vec![0], 1), (vec![0], 0)]);
        assert_eq!(
            solve_projected_pattern_count_interruptible(&duplicate, 1, &[1], || false),
            Err(ProjectedPatternDecline::UnsupportedStructure)
        );
        let ordinary = manual_frontier(vec![(vec![0], 1)]);
        assert_eq!(
            solve_projected_pattern_count_interruptible(&ordinary, 1, &[-1], || false),
            Err(ProjectedPatternDecline::UnsupportedStructure)
        );
        let overflow = manual_frontier(vec![(vec![0], i128::MAX)]);
        assert_eq!(
            solve_projected_pattern_count_interruptible(&overflow, 2, &[0], || false),
            Err(ProjectedPatternDecline::ArithmeticOverflow)
        );
    }

    fn manual_frontier(patterns: Vec<(Vec<i128>, i128)>) -> ProjectedPatternFrontier {
        ProjectedPatternFrontier {
            num_variables: 0,
            patterns: patterns
                .into_iter()
                .map(|(signature, cost)| ProjectedPattern {
                    signature,
                    cost,
                    assignment: Vec::new(),
                })
                .collect(),
            retained_states: 0,
            transition_work: 0,
        }
    }

    fn solve_count_with_traversal_for_test(
        frontier: &ProjectedPatternFrontier,
        block_count: usize,
        capacities: &[i128],
        limits: ProjectedPatternCountLimits,
        traversal: CountTraversal,
    ) -> Result<Option<ProjectedPatternCountSolution>, ProjectedPatternDecline> {
        let mut never_stop = || false;
        let master =
            CountMaster::detect(frontier, block_count, capacities, limits, &mut never_stop)?;
        master.solve_with_traversal(frontier, limits, traversal, &mut never_stop)
    }

    fn exhaustive_count_cost(
        frontier: &ProjectedPatternFrontier,
        blocks: usize,
        capacities: &[i128],
    ) -> Option<i128> {
        fn visit(
            frontier: &ProjectedPatternFrontier,
            blocks: usize,
            capacities: &[i128],
            depth: usize,
            used: &mut [i128],
            cost: i128,
            best: &mut Option<i128>,
        ) {
            if depth == blocks {
                if best.is_none_or(|incumbent| cost < incumbent) {
                    *best = Some(cost);
                }
                return;
            }
            for pattern in &frontier.patterns {
                if used
                    .iter()
                    .zip(&pattern.signature)
                    .zip(capacities)
                    .any(|((&current, &delta), &capacity)| current + delta > capacity)
                {
                    continue;
                }
                for (current, &delta) in used.iter_mut().zip(&pattern.signature) {
                    *current += delta;
                }
                visit(
                    frontier,
                    blocks,
                    capacities,
                    depth + 1,
                    used,
                    cost + pattern.cost,
                    best,
                );
                for (current, &delta) in used.iter_mut().zip(&pattern.signature) {
                    *current -= delta;
                }
            }
        }

        let mut best = None;
        let mut used = vec![0; capacities.len()];
        visit(frontier, blocks, capacities, 0, &mut used, 0, &mut best);
        best
    }

    fn exhaustive_frontier(
        instance: &PbInstance,
        resources: &[ProjectedPatternResource],
    ) -> Vec<ProjectedPattern> {
        let variables = instance.num_vars as usize;
        assert!(variables < usize::BITS as usize);
        let mut best = BTreeMap::<Vec<i128>, (i128, Vec<bool>)>::new();
        for mask in 0usize..(1usize << variables) {
            let assignment = (0..variables)
                .map(|variable| mask & (1usize << variable) != 0)
                .collect::<Vec<_>>();
            if !instance
                .constraints
                .iter()
                .all(|row| eval_constraint(row, &assignment))
            {
                continue;
            }
            let signature = resources
                .iter()
                .map(|resource| eval_expression(&resource.expression, &assignment))
                .collect::<Vec<_>>();
            if resources
                .iter()
                .zip(&signature)
                .any(|(resource, &value)| value < resource.minimum || value > resource.maximum)
            {
                continue;
            }
            let cost = instance
                .objective
                .as_ref()
                .map_or(0, |objective| eval_expression(objective, &assignment));
            match best.entry(signature) {
                std::collections::btree_map::Entry::Vacant(slot) => {
                    slot.insert((cost, assignment));
                }
                std::collections::btree_map::Entry::Occupied(mut slot) => {
                    let incumbent = slot.get_mut();
                    if cost < incumbent.0 || (cost == incumbent.0 && assignment < incumbent.1) {
                        *incumbent = (cost, assignment);
                    }
                }
            }
        }
        best.into_iter()
            .map(|(signature, (cost, assignment))| ProjectedPattern {
                signature,
                cost,
                assignment,
            })
            .collect()
    }

    fn eval_constraint(row: &PbConstraint, assignment: &[bool]) -> bool {
        let value = eval_terms(&row.terms, assignment);
        match row.rel {
            PbRel::Ge => value >= row.rhs,
            PbRel::Eq => value == row.rhs,
        }
    }

    fn eval_expression(expression: &PbObjective, assignment: &[bool]) -> i128 {
        eval_terms(&expression.terms, assignment)
    }

    fn eval_terms(terms: &[PbTerm], assignment: &[bool]) -> i128 {
        terms
            .iter()
            .map(|term| {
                let literal = term.lits[0];
                let value = assignment[literal.var as usize - 1] ^ literal.negated;
                if value {
                    term.coeff
                } else {
                    0
                }
            })
            .sum()
    }

    fn next_random(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }
}
