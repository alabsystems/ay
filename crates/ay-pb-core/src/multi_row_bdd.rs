// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Independently replayable decision-DAG refutations for linear PB systems.
//!
//! The generator constructs an ordered binary decision diagram over exact
//! residual row intervals.  States at the same variable layer are merged only
//! when every residual interval agrees.  An infeasibility artifact stores only
//! the variable order and the two child edges of each reachable state; it does
//! not store or assert the states themselves.
//!
//! The verifier independently canonicalizes the original [`PbInstance`],
//! reconstructs every state from the root, checks every merge, and accepts only
//! when every leaf transition is arithmetically impossible.  Thus the DAG is a
//! proof object rather than a trusted transcript of the generator.  Resource,
//! memory, interruption, malformed-input, and arithmetic failures all decline
//! without granting an UNSAT verdict.

use std::collections::BTreeMap;
use std::io::{self, Write};

use rustc_hash::FxHashMap;

use crate::{PbInstance, PbRel};

/// Stable JSON artifact format for general linear-PB decision-DAG refutations.
pub const MULTI_ROW_BDD_INFEASIBILITY_CERTIFICATE_FORMAT: &str = "ay.multi-row-bdd-infeasible.v1";

const DEFAULT_MAX_VARIABLES: usize = 4_096;
const DEFAULT_MAX_ROWS: usize = 8_192;
const DEFAULT_MAX_TERMS: usize = 250_000;
const DEFAULT_MAX_NODES: usize = 2_000_000;
const DEFAULT_MAX_STATE_TRANSITIONS: u64 = 250_000_000;
const DEFAULT_MEMORY_BUDGET_BYTES: u64 = 512 << 20;
const CERTIFICATE_JSON_MEMORY_FACTOR: u64 = 16;

/// Explicit resource envelope for decision-DAG generation and replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MultiRowBddLimits {
    /// Maximum number of declared Boolean variables.
    pub max_variables: usize,
    /// Maximum number of linear constraints.
    pub max_rows: usize,
    /// Maximum number of raw constraint terms.
    pub max_terms: usize,
    /// Maximum number of reachable DAG nodes over all layers.
    pub max_nodes: usize,
    /// Maximum number of exact row-state cells copied or transitioned.
    pub max_state_transitions: u64,
    /// Maximum conservatively estimated live allocation.
    pub memory_budget_bytes: u64,
}

impl Default for MultiRowBddLimits {
    fn default() -> Self {
        Self {
            max_variables: DEFAULT_MAX_VARIABLES,
            max_rows: DEFAULT_MAX_ROWS,
            max_terms: DEFAULT_MAX_TERMS,
            max_nodes: DEFAULT_MAX_NODES,
            max_state_transitions: DEFAULT_MAX_STATE_TRANSITIONS,
            memory_budget_bytes: DEFAULT_MEMORY_BUDGET_BYTES,
        }
    }
}

/// Typed, fail-closed reason no decision-DAG proof was produced or accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MultiRowBddDecline {
    /// The instance is not a supported linear Boolean PB system.
    UnsupportedStructure,
    /// A term is nonlinear or references an invalid variable.
    InvalidLinearTerm,
    /// Checked exact integer arithmetic overflowed.
    ArithmeticOverflow,
    /// A variable, row, term, node, or transition cap was exceeded.
    ResourceLimit,
    /// The conservative live-allocation estimate exceeded its budget.
    MemoryLimit,
    /// The caller requested interruption or its deadline expired.
    Interrupted,
    /// The supplied artifact failed independent replay.
    VerificationFailed,
}

/// Independently replayable proof that a linear Boolean PB system is infeasible.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MultiRowBddInfeasibilityCertificate {
    /// Artifact format identifier.  Unknown versions fail closed.
    pub format: String,
    /// Complete zero-based variable permutation used by the ordered DAG.
    pub variable_order: Vec<u32>,
    /// Arithmetic contradiction or layered decision-DAG body.
    pub proof: MultiRowBddInfeasibilityProof,
}

/// Body of a general linear-PB infeasibility artifact.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MultiRowBddInfeasibilityProof {
    /// At least one row misses its attainable interval before any decision.
    RootContradiction,
    /// All reachable exact residual states form a rejecting decision DAG.
    DecisionDag {
        /// Nonempty consecutive layers beginning at the root variable.
        layers: Vec<MultiRowBddLayer>,
    },
}

/// One variable layer of the ordered decision DAG.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MultiRowBddLayer {
    /// All and only the reachable residual states at this layer.
    pub nodes: Vec<MultiRowBddNode>,
}

/// Child edges for one implicit exact residual state.
///
/// Child indices address the next layer.  `None` is a rejecting edge and is
/// accepted only when the independent verifier proves that transition cannot
/// satisfy at least one row with the variables that remain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MultiRowBddNode {
    /// Edge for assigning the layer variable to false.
    pub zero_child: Option<u32>,
    /// Edge for assigning the layer variable to true.
    pub one_child: Option<u32>,
}

/// Typed failure to encode or decode a bounded JSON proof artifact.
#[derive(Debug, thiserror::Error)]
pub enum MultiRowBddCertificateCodecError {
    /// The encoded artifact exceeds the configured safe encoded-size share.
    #[error("multi-row BDD certificate exceeds the {limit}-byte encoded limit")]
    Oversized {
        /// Maximum accepted encoded bytes.
        limit: u64,
    },
    /// The artifact is malformed, truncated, or otherwise invalid JSON.
    #[error("malformed multi-row BDD certificate: {0}")]
    Malformed(#[source] serde_json::Error),
}

/// Generate a replayable infeasibility certificate under the default limits.
///
/// `Ok(None)` means that the BDD found a feasible Boolean assignment.  A cap,
/// deadline, unsupported term, or arithmetic failure is returned as a decline,
/// never as infeasibility.
pub fn generate_multi_row_bdd_infeasibility_certificate_interruptible<F>(
    instance: &PbInstance,
    should_stop: F,
) -> Result<Option<MultiRowBddInfeasibilityCertificate>, MultiRowBddDecline>
where
    F: FnMut() -> bool,
{
    generate_multi_row_bdd_infeasibility_certificate_with_limits(
        instance,
        MultiRowBddLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized form of
/// [`generate_multi_row_bdd_infeasibility_certificate_interruptible`].
pub fn generate_multi_row_bdd_infeasibility_certificate_with_limits<F>(
    instance: &PbInstance,
    limits: MultiRowBddLimits,
    mut should_stop: F,
) -> Result<Option<MultiRowBddInfeasibilityCertificate>, MultiRowBddDecline>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(MultiRowBddDecline::Interrupted);
    }
    let problem = GeneratorProblem::detect(instance, limits, &mut should_stop)?;
    let variable_order = problem.variable_order()?;
    let (root, remaining_min, remaining_max) = problem.initial_state(&mut should_stop)?;

    let proof = match root {
        None => MultiRowBddInfeasibilityProof::RootContradiction,
        Some(root) => {
            if problem.num_variables == 0 {
                return Ok(None);
            }
            let Some(layers) = problem.build_rejecting_dag(
                root,
                remaining_min,
                remaining_max,
                &variable_order,
                limits,
                &mut should_stop,
            )?
            else {
                return Ok(None);
            };
            MultiRowBddInfeasibilityProof::DecisionDag { layers }
        }
    };

    let certificate = MultiRowBddInfeasibilityCertificate {
        format: MULTI_ROW_BDD_INFEASIBILITY_CERTIFICATE_FORMAT.to_owned(),
        variable_order: variable_order
            .iter()
            .map(|&variable| u32::try_from(variable).map_err(|_| MultiRowBddDecline::ResourceLimit))
            .collect::<Result<Vec<_>, _>>()?,
        proof,
    };
    drop(problem);

    // The emitter does not get to trust its own search representation.  A
    // separately implemented dense canonicalizer and replay engine must accept
    // the artifact before it can escape this API.
    verify_multi_row_bdd_infeasibility_certificate_with_limits(
        instance,
        &certificate,
        limits,
        &mut should_stop,
    )?;
    Ok(Some(certificate))
}

/// Independently replay a decision-DAG certificate under the default limits.
pub fn verify_multi_row_bdd_infeasibility_certificate_interruptible<F>(
    instance: &PbInstance,
    certificate: &MultiRowBddInfeasibilityCertificate,
    should_stop: F,
) -> Result<(), MultiRowBddDecline>
where
    F: FnMut() -> bool,
{
    verify_multi_row_bdd_infeasibility_certificate_with_limits(
        instance,
        certificate,
        MultiRowBddLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized independent verifier.
pub fn verify_multi_row_bdd_infeasibility_certificate_with_limits<F>(
    instance: &PbInstance,
    certificate: &MultiRowBddInfeasibilityCertificate,
    limits: MultiRowBddLimits,
    mut should_stop: F,
) -> Result<(), MultiRowBddDecline>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(MultiRowBddDecline::Interrupted);
    }
    if certificate.format != MULTI_ROW_BDD_INFEASIBILITY_CERTIFICATE_FORMAT {
        return Err(MultiRowBddDecline::VerificationFailed);
    }
    let artifact_bytes =
        validate_untrusted_certificate_shape(instance, certificate, limits, &mut should_stop)?;
    let replay_limits = MultiRowBddLimits {
        memory_budget_bytes: limits
            .memory_budget_bytes
            .checked_sub(artifact_bytes)
            .ok_or(MultiRowBddDecline::MemoryLimit)?,
        ..limits
    };
    let problem = ReplayProblem::detect(instance, replay_limits, &mut should_stop)?;
    problem.replay(certificate, replay_limits, &mut should_stop)
}

/// Serialize a certificate to bounded JSON under the default resource limits.
pub fn encode_multi_row_bdd_infeasibility_certificate_json(
    certificate: &MultiRowBddInfeasibilityCertificate,
) -> Result<Vec<u8>, MultiRowBddCertificateCodecError> {
    encode_multi_row_bdd_infeasibility_certificate_json_with_limits(
        certificate,
        MultiRowBddLimits::default(),
    )
}

/// Serialize a certificate without exceeding the configured encoded-size cap.
pub fn encode_multi_row_bdd_infeasibility_certificate_json_with_limits(
    certificate: &MultiRowBddInfeasibilityCertificate,
    limits: MultiRowBddLimits,
) -> Result<Vec<u8>, MultiRowBddCertificateCodecError> {
    let encoded_limit = certificate_json_encoded_limit(limits);
    let mut writer = BoundedCertificateWriter::new(encoded_limit);
    let result = serde_json::to_writer(&mut writer, certificate);
    if writer.exceeded {
        return Err(MultiRowBddCertificateCodecError::Oversized {
            limit: encoded_limit,
        });
    }
    result.map_err(MultiRowBddCertificateCodecError::Malformed)?;
    Ok(writer.bytes)
}

/// Decode a bounded JSON certificate under the default resource limits.
pub fn decode_multi_row_bdd_infeasibility_certificate_json(
    encoded: &[u8],
) -> Result<MultiRowBddInfeasibilityCertificate, MultiRowBddCertificateCodecError> {
    decode_multi_row_bdd_infeasibility_certificate_json_with_limits(
        encoded,
        MultiRowBddLimits::default(),
    )
}

/// Decode JSON only after enforcing a byte cap before vector allocation.
pub fn decode_multi_row_bdd_infeasibility_certificate_json_with_limits(
    encoded: &[u8],
    limits: MultiRowBddLimits,
) -> Result<MultiRowBddInfeasibilityCertificate, MultiRowBddCertificateCodecError> {
    let encoded_limit = certificate_json_encoded_limit(limits);
    if u64::try_from(encoded.len()).unwrap_or(u64::MAX) > encoded_limit {
        return Err(MultiRowBddCertificateCodecError::Oversized {
            limit: encoded_limit,
        });
    }
    serde_json::from_slice(encoded).map_err(MultiRowBddCertificateCodecError::Malformed)
}

const fn certificate_json_encoded_limit(limits: MultiRowBddLimits) -> u64 {
    limits.memory_budget_bytes / CERTIFICATE_JSON_MEMORY_FACTOR
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ResidualInterval {
    lower: i128,
    upper: i128,
}

type ResidualState = Vec<ResidualInterval>;

#[derive(Debug)]
struct GeneratorProblem {
    num_variables: usize,
    row_lower: Vec<i128>,
    row_upper: Vec<Option<i128>>,
    columns: Vec<Vec<(usize, i128)>>,
    canonical_bytes: u64,
}

impl GeneratorProblem {
    /// Generator-side sparse-map canonicalization.  The replay side below is
    /// intentionally implemented separately with a dense temporary row.
    fn detect(
        instance: &PbInstance,
        limits: MultiRowBddLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Self, MultiRowBddDecline> {
        let num_variables =
            usize::try_from(instance.num_vars).map_err(|_| MultiRowBddDecline::ResourceLimit)?;
        let row_count = instance.constraints.len();
        if num_variables > limits.max_variables
            || row_count > limits.max_rows
            || (instance.num_constraints != 0
                && usize::try_from(instance.num_constraints).unwrap_or(usize::MAX) != row_count)
        {
            return Err(MultiRowBddDecline::UnsupportedStructure);
        }
        let raw_terms = count_raw_terms(instance, limits)?;
        let canonical_bytes = canonical_allocation_estimate(num_variables, row_count, raw_terms)?;
        if canonical_bytes > limits.memory_budget_bytes {
            return Err(MultiRowBddDecline::MemoryLimit);
        }

        let mut row_lower = Vec::with_capacity(row_count);
        let mut row_upper = Vec::with_capacity(row_count);
        let mut columns = vec![Vec::<(usize, i128)>::new(); num_variables];
        for (row_index, row) in instance.constraints.iter().enumerate() {
            if row_index & 0x3f == 0 && should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
            let mut coefficients = BTreeMap::<usize, i128>::new();
            let mut constant = 0i128;
            for (term_index, term) in row.terms.iter().enumerate() {
                if term_index & 0x3ff == 0 && should_stop() {
                    return Err(MultiRowBddDecline::Interrupted);
                }
                let [literal] = term.lits.as_slice() else {
                    return Err(MultiRowBddDecline::InvalidLinearTerm);
                };
                let variable = checked_variable(literal.var, num_variables)?;
                let contribution = if literal.negated {
                    constant = constant
                        .checked_add(term.coeff)
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                    term.coeff
                        .checked_neg()
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?
                } else {
                    term.coeff
                };
                let old = coefficients.get(&variable).copied().unwrap_or(0);
                let updated = old
                    .checked_add(contribution)
                    .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                if updated == 0 {
                    coefficients.remove(&variable);
                } else {
                    coefficients.insert(variable, updated);
                }
            }
            let rhs = row
                .rhs
                .checked_sub(constant)
                .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
            row_lower.push(rhs);
            row_upper.push(match row.rel {
                PbRel::Ge => None,
                PbRel::Eq => Some(rhs),
            });
            for (variable, coefficient) in coefficients {
                columns[variable].push((row_index, coefficient));
            }
        }

        Ok(Self {
            num_variables,
            row_lower,
            row_upper,
            columns,
            canonical_bytes,
        })
    }

    fn variable_order(&self) -> Result<Vec<usize>, MultiRowBddDecline> {
        let mut variables = (0..self.num_variables).collect::<Vec<_>>();
        variables.sort_unstable_by(|&left, &right| {
            let left_column = &self.columns[left];
            let right_column = &self.columns[right];
            let left_weight = left_column.iter().fold(0u128, |sum, &(_, coefficient)| {
                sum.saturating_add(coefficient.unsigned_abs())
            });
            let right_weight = right_column.iter().fold(0u128, |sum, &(_, coefficient)| {
                sum.saturating_add(coefficient.unsigned_abs())
            });
            right_column
                .len()
                .cmp(&left_column.len())
                .then_with(|| right_weight.cmp(&left_weight))
                .then_with(|| left.cmp(&right))
        });
        if variables.len() != self.num_variables {
            return Err(MultiRowBddDecline::ResourceLimit);
        }
        Ok(variables)
    }

    fn initial_state(
        &self,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(Option<ResidualState>, Vec<i128>, Vec<i128>), MultiRowBddDecline> {
        let rows = self.row_lower.len();
        let mut remaining_min = vec![0i128; rows];
        let mut remaining_max = vec![0i128; rows];
        for (variable, column) in self.columns.iter().enumerate() {
            if variable & 0x3ff == 0 && should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
            for &(row, coefficient) in column {
                if coefficient < 0 {
                    remaining_min[row] = remaining_min[row]
                        .checked_add(coefficient)
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                } else {
                    remaining_max[row] = remaining_max[row]
                        .checked_add(coefficient)
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                }
            }
        }

        let mut state = Vec::with_capacity(rows);
        for row in 0..rows {
            if row & 0x3ff == 0 && should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
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

    #[allow(clippy::too_many_arguments)]
    fn build_rejecting_dag(
        &self,
        root: ResidualState,
        mut remaining_min: Vec<i128>,
        mut remaining_max: Vec<i128>,
        variable_order: &[usize],
        limits: MultiRowBddLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Option<Vec<MultiRowBddLayer>>, MultiRowBddDecline> {
        let mut layers = Vec::new();
        let mut current_states = vec![root];
        let mut total_nodes = 0usize;
        let mut state_transitions = 0u64;

        for (level, &variable) in variable_order.iter().enumerate() {
            if should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
            total_nodes = total_nodes
                .checked_add(current_states.len())
                .ok_or(MultiRowBddDecline::ResourceLimit)?;
            if total_nodes > limits.max_nodes {
                return Err(MultiRowBddDecline::ResourceLimit);
            }
            check_generation_memory(
                self,
                current_states.len(),
                0,
                total_nodes,
                layers.len().saturating_add(1),
                limits,
            )?;

            let column = &self.columns[variable];
            let (next_min, next_max) =
                generator_next_suffix_bounds(&remaining_min, &remaining_max, column)?;
            let mut next_map = FxHashMap::<ResidualState, u32>::default();
            let mut nodes = Vec::with_capacity(current_states.len());

            for (node_index, state) in current_states.iter().enumerate() {
                if node_index & 0x3ff == 0 && should_stop() {
                    return Err(MultiRowBddDecline::Interrupted);
                }
                let zero = generator_transition(
                    state,
                    column,
                    false,
                    &next_min,
                    &next_max,
                    &mut state_transitions,
                    limits,
                    should_stop,
                )?;
                let one = generator_transition(
                    state,
                    column,
                    true,
                    &next_min,
                    &next_max,
                    &mut state_transitions,
                    limits,
                    should_stop,
                )?;

                if level + 1 == self.num_variables && (zero.is_some() || one.is_some()) {
                    return Ok(None);
                }
                let zero_child = intern_generator_state(
                    zero,
                    &mut next_map,
                    self,
                    current_states.len(),
                    total_nodes,
                    layers.len().saturating_add(1),
                    limits,
                )?;
                let one_child = intern_generator_state(
                    one,
                    &mut next_map,
                    self,
                    current_states.len(),
                    total_nodes,
                    layers.len().saturating_add(1),
                    limits,
                )?;
                nodes.push(MultiRowBddNode {
                    zero_child,
                    one_child,
                });
            }
            layers.push(MultiRowBddLayer { nodes });

            if next_map.is_empty() {
                return Ok(Some(layers));
            }
            let next_len = next_map.len();
            if next_len > limits.max_nodes.saturating_sub(total_nodes) {
                return Err(MultiRowBddDecline::ResourceLimit);
            }
            let mut indexed = (0..next_len).map(|_| None).collect::<Vec<_>>();
            for (state, index) in next_map {
                let index =
                    usize::try_from(index).map_err(|_| MultiRowBddDecline::ResourceLimit)?;
                let Some(slot) = indexed.get_mut(index) else {
                    return Err(MultiRowBddDecline::VerificationFailed);
                };
                if slot.is_some() {
                    return Err(MultiRowBddDecline::VerificationFailed);
                }
                *slot = Some(state);
            }
            current_states = indexed
                .into_iter()
                .collect::<Option<Vec<_>>>()
                .ok_or(MultiRowBddDecline::VerificationFailed)?;
            remaining_min = next_min;
            remaining_max = next_max;
        }

        // A non-contradictory zero-variable problem was handled before entry,
        // and every feasible full assignment returns `None` above.
        Err(MultiRowBddDecline::VerificationFailed)
    }
}

fn intern_generator_state(
    state: Option<ResidualState>,
    next_map: &mut FxHashMap<ResidualState, u32>,
    problem: &GeneratorProblem,
    current_count: usize,
    total_nodes: usize,
    layer_count: usize,
    limits: MultiRowBddLimits,
) -> Result<Option<u32>, MultiRowBddDecline> {
    let Some(state) = state else {
        return Ok(None);
    };
    if let Some(&index) = next_map.get(&state) {
        return Ok(Some(index));
    }
    let index = u32::try_from(next_map.len()).map_err(|_| MultiRowBddDecline::ResourceLimit)?;
    let prospective = next_map
        .len()
        .checked_add(1)
        .ok_or(MultiRowBddDecline::ResourceLimit)?;
    if prospective > limits.max_nodes.saturating_sub(total_nodes) {
        return Err(MultiRowBddDecline::ResourceLimit);
    }
    check_generation_memory(
        problem,
        current_count,
        prospective,
        total_nodes,
        layer_count,
        limits,
    )?;
    next_map.insert(state, index);
    Ok(Some(index))
}

fn generator_next_suffix_bounds(
    remaining_min: &[i128],
    remaining_max: &[i128],
    column: &[(usize, i128)],
) -> Result<(Vec<i128>, Vec<i128>), MultiRowBddDecline> {
    let mut next_min = remaining_min.to_vec();
    let mut next_max = remaining_max.to_vec();
    for &(row, coefficient) in column {
        if coefficient < 0 {
            next_min[row] = next_min[row]
                .checked_sub(coefficient)
                .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
        } else {
            next_max[row] = next_max[row]
                .checked_sub(coefficient)
                .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
        }
    }
    Ok((next_min, next_max))
}

#[allow(clippy::too_many_arguments)]
fn generator_transition(
    state: &[ResidualInterval],
    column: &[(usize, i128)],
    value: bool,
    next_min: &[i128],
    next_max: &[i128],
    state_transitions: &mut u64,
    limits: MultiRowBddLimits,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<Option<ResidualState>, MultiRowBddDecline> {
    let work = u64::try_from(state.len())
        .unwrap_or(u64::MAX)
        .checked_add(u64::try_from(column.len()).unwrap_or(u64::MAX))
        .ok_or(MultiRowBddDecline::ResourceLimit)?;
    *state_transitions = state_transitions
        .checked_add(work)
        .ok_or(MultiRowBddDecline::ResourceLimit)?;
    if *state_transitions > limits.max_state_transitions {
        return Err(MultiRowBddDecline::ResourceLimit);
    }
    let mut child = state.to_vec();
    for (entry_index, &(row, coefficient)) in column.iter().enumerate() {
        if entry_index & 0x3ff == 0 && should_stop() {
            return Err(MultiRowBddDecline::Interrupted);
        }
        let mut lower = child[row].lower;
        let mut upper = child[row].upper;
        if value {
            lower = lower
                .checked_sub(coefficient)
                .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
            upper = upper
                .checked_sub(coefficient)
                .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
        }
        if lower > next_max[row] || upper < next_min[row] || lower > upper {
            return Ok(None);
        }
        child[row] = ResidualInterval {
            lower: lower.max(next_min[row]),
            upper: upper.min(next_max[row]),
        };
    }
    Ok(Some(child))
}

fn check_generation_memory(
    problem: &GeneratorProblem,
    current_states: usize,
    next_states: usize,
    certificate_nodes: usize,
    certificate_layers: usize,
    limits: MultiRowBddLimits,
) -> Result<(), MultiRowBddDecline> {
    let state_payload = u64::try_from(problem.row_lower.len())
        .unwrap_or(u64::MAX)
        .checked_mul(32)
        .and_then(|bytes| bytes.checked_add(96))
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let live_states = current_states
        .checked_add(next_states)
        // Both branch states can coexist transiently before interning.
        .and_then(|states| states.checked_add(2))
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let state_bytes = u64::try_from(live_states)
        .unwrap_or(u64::MAX)
        .checked_mul(state_payload)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let certificate_bytes = u64::try_from(certificate_nodes)
        .unwrap_or(u64::MAX)
        .checked_mul(16)
        .and_then(|bytes| {
            bytes.checked_add(
                u64::try_from(certificate_layers)
                    .unwrap_or(u64::MAX)
                    .saturating_mul(24),
            )
        })
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let live = problem
        .canonical_bytes
        .checked_add(state_bytes)
        .and_then(|bytes| bytes.checked_add(certificate_bytes))
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    if live > limits.memory_budget_bytes {
        return Err(MultiRowBddDecline::MemoryLimit);
    }
    Ok(())
}

// The replay representation deliberately does not share canonical rows,
// ordering logic, suffix-bound code, or transition code with the generator.
#[derive(Debug)]
struct ReplayProblem {
    num_variables: usize,
    lower_bounds: Vec<i128>,
    upper_bounds: Vec<Option<i128>>,
    coefficients_by_variable: Vec<Vec<(usize, i128)>>,
    canonical_bytes: u64,
}

impl ReplayProblem {
    fn detect(
        instance: &PbInstance,
        limits: MultiRowBddLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Self, MultiRowBddDecline> {
        let num_variables =
            usize::try_from(instance.num_vars).map_err(|_| MultiRowBddDecline::ResourceLimit)?;
        let row_count = instance.constraints.len();
        if num_variables > limits.max_variables
            || row_count > limits.max_rows
            || (instance.num_constraints != 0 && instance.num_constraints as usize != row_count)
        {
            return Err(MultiRowBddDecline::UnsupportedStructure);
        }
        let raw_terms = count_raw_terms(instance, limits)?;
        let canonical_bytes = canonical_allocation_estimate(num_variables, row_count, raw_terms)?;
        let dense_scratch = u64::try_from(num_variables)
            .unwrap_or(u64::MAX)
            .checked_mul(16)
            .ok_or(MultiRowBddDecline::MemoryLimit)?;
        if canonical_bytes.saturating_add(dense_scratch) > limits.memory_budget_bytes {
            return Err(MultiRowBddDecline::MemoryLimit);
        }

        let mut lower_bounds = Vec::with_capacity(row_count);
        let mut upper_bounds = Vec::with_capacity(row_count);
        let mut coefficients_by_variable = vec![Vec::<(usize, i128)>::new(); num_variables];
        let mut dense = vec![0i128; num_variables];
        for (row_index, row) in instance.constraints.iter().enumerate() {
            if row_index & 0x3f == 0 && should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
            dense.fill(0);
            let mut adjusted_rhs = row.rhs;
            for (term_index, term) in row.terms.iter().enumerate() {
                if term_index & 0x3ff == 0 && should_stop() {
                    return Err(MultiRowBddDecline::Interrupted);
                }
                if term.lits.len() != 1 {
                    return Err(MultiRowBddDecline::InvalidLinearTerm);
                }
                let literal = term.lits[0];
                let variable = checked_variable(literal.var, num_variables)?;
                let coefficient = if literal.negated {
                    adjusted_rhs = adjusted_rhs
                        .checked_sub(term.coeff)
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                    term.coeff
                        .checked_neg()
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?
                } else {
                    term.coeff
                };
                dense[variable] = dense[variable]
                    .checked_add(coefficient)
                    .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
            }
            lower_bounds.push(adjusted_rhs);
            upper_bounds.push(match row.rel {
                PbRel::Ge => None,
                PbRel::Eq => Some(adjusted_rhs),
            });
            for (variable, &coefficient) in dense.iter().enumerate() {
                if variable & 0x3ff == 0 && should_stop() {
                    return Err(MultiRowBddDecline::Interrupted);
                }
                if coefficient != 0 {
                    coefficients_by_variable[variable].push((row_index, coefficient));
                }
            }
        }
        Ok(Self {
            num_variables,
            lower_bounds,
            upper_bounds,
            coefficients_by_variable,
            canonical_bytes,
        })
    }

    fn replay(
        &self,
        certificate: &MultiRowBddInfeasibilityCertificate,
        limits: MultiRowBddLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(), MultiRowBddDecline> {
        let order = certificate
            .variable_order
            .iter()
            .map(|&variable| {
                usize::try_from(variable).map_err(|_| MultiRowBddDecline::VerificationFailed)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (root, mut suffix_min, mut suffix_max) = self.replay_initial_state(should_stop)?;
        match (&certificate.proof, root) {
            (MultiRowBddInfeasibilityProof::RootContradiction, None) => return Ok(()),
            (MultiRowBddInfeasibilityProof::RootContradiction, Some(_))
            | (MultiRowBddInfeasibilityProof::DecisionDag { .. }, None) => {
                return Err(MultiRowBddDecline::VerificationFailed);
            }
            (MultiRowBddInfeasibilityProof::DecisionDag { layers }, Some(root)) => {
                let mut states = vec![root];
                let mut state_transitions = 0u64;
                for (level, layer) in layers.iter().enumerate() {
                    if should_stop() {
                        return Err(MultiRowBddDecline::Interrupted);
                    }
                    if states.len() != layer.nodes.len() {
                        return Err(MultiRowBddDecline::VerificationFailed);
                    }
                    let variable = order[level];
                    let column = &self.coefficients_by_variable[variable];

                    // Replay derives the next suffix bounds locally, without
                    // calling the generator's suffix transition routine.
                    let mut following_min = suffix_min.clone();
                    let mut following_max = suffix_max.clone();
                    for &(row, coefficient) in column {
                        if coefficient.is_negative() {
                            following_min[row] = following_min[row]
                                .checked_add(
                                    coefficient
                                        .checked_neg()
                                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?,
                                )
                                .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                        } else {
                            following_max[row] = following_max[row]
                                .checked_add(
                                    coefficient
                                        .checked_neg()
                                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?,
                                )
                                .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                        }
                    }

                    let is_last_artifact_layer = level + 1 == layers.len();
                    let next_count = if is_last_artifact_layer {
                        0
                    } else {
                        layers[level + 1].nodes.len()
                    };
                    check_replay_memory(self, states.len(), next_count, limits)?;
                    let mut next_states = (0..next_count)
                        .map(|_| None)
                        .collect::<Vec<Option<ResidualState>>>();

                    for (node_index, (state, node)) in states.iter().zip(&layer.nodes).enumerate() {
                        if node_index & 0x3ff == 0 && should_stop() {
                            return Err(MultiRowBddDecline::Interrupted);
                        }
                        let zero = replay_branch(
                            state,
                            column,
                            false,
                            &following_min,
                            &following_max,
                            &mut state_transitions,
                            limits,
                            should_stop,
                        )?;
                        let one = replay_branch(
                            state,
                            column,
                            true,
                            &following_min,
                            &following_max,
                            &mut state_transitions,
                            limits,
                            should_stop,
                        )?;
                        replay_edge(zero, node.zero_child, &mut next_states)?;
                        replay_edge(one, node.one_child, &mut next_states)?;
                    }

                    if is_last_artifact_layer {
                        // `replay_edge` accepts no live transition when there
                        // is no following layer.
                        return Ok(());
                    }
                    states = next_states
                        .into_iter()
                        .collect::<Option<Vec<_>>>()
                        .ok_or(MultiRowBddDecline::VerificationFailed)?;
                    suffix_min = following_min;
                    suffix_max = following_max;
                }
            }
        }
        Err(MultiRowBddDecline::VerificationFailed)
    }

    fn replay_initial_state(
        &self,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(Option<ResidualState>, Vec<i128>, Vec<i128>), MultiRowBddDecline> {
        let row_count = self.lower_bounds.len();
        let mut suffix_min = vec![0i128; row_count];
        let mut suffix_max = vec![0i128; row_count];
        for (variable, entries) in self.coefficients_by_variable.iter().enumerate() {
            if variable & 0x3ff == 0 && should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
            for &(row, coefficient) in entries {
                if coefficient.is_negative() {
                    suffix_min[row] = suffix_min[row]
                        .checked_add(coefficient)
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                } else {
                    suffix_max[row] = suffix_max[row]
                        .checked_add(coefficient)
                        .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
                }
            }
        }
        let mut state = Vec::with_capacity(row_count);
        for row in 0..row_count {
            if row & 0x3ff == 0 && should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
            let wanted_lower = self.lower_bounds[row];
            let wanted_upper = self.upper_bounds[row].unwrap_or(suffix_max[row]);
            let clipped_lower = wanted_lower.max(suffix_min[row]);
            let clipped_upper = wanted_upper.min(suffix_max[row]);
            if clipped_lower > clipped_upper {
                return Ok((None, suffix_min, suffix_max));
            }
            state.push(ResidualInterval {
                lower: clipped_lower,
                upper: clipped_upper,
            });
        }
        Ok((Some(state), suffix_min, suffix_max))
    }
}

#[allow(clippy::too_many_arguments)]
fn replay_branch(
    parent: &[ResidualInterval],
    column: &[(usize, i128)],
    assigned_one: bool,
    suffix_min: &[i128],
    suffix_max: &[i128],
    work_done: &mut u64,
    limits: MultiRowBddLimits,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<Option<ResidualState>, MultiRowBddDecline> {
    let copied_cells = u64::try_from(parent.len()).unwrap_or(u64::MAX);
    let changed_cells = u64::try_from(column.len()).unwrap_or(u64::MAX);
    *work_done = work_done
        .checked_add(copied_cells)
        .and_then(|work| work.checked_add(changed_cells))
        .ok_or(MultiRowBddDecline::ResourceLimit)?;
    if *work_done > limits.max_state_transitions {
        return Err(MultiRowBddDecline::ResourceLimit);
    }

    let mut result = parent.to_vec();
    for (position, &(row, coefficient)) in column.iter().enumerate() {
        if position & 0x3ff == 0 && should_stop() {
            return Err(MultiRowBddDecline::Interrupted);
        }
        let delta = if assigned_one { coefficient } else { 0 };
        let required_lower = result[row]
            .lower
            .checked_sub(delta)
            .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
        let required_upper = result[row]
            .upper
            .checked_sub(delta)
            .ok_or(MultiRowBddDecline::ArithmeticOverflow)?;
        let intersected_lower = required_lower.max(suffix_min[row]);
        let intersected_upper = required_upper.min(suffix_max[row]);
        if intersected_lower > intersected_upper {
            return Ok(None);
        }
        result[row] = ResidualInterval {
            lower: intersected_lower,
            upper: intersected_upper,
        };
    }
    Ok(Some(result))
}

fn replay_edge(
    computed: Option<ResidualState>,
    claimed_child: Option<u32>,
    next_states: &mut [Option<ResidualState>],
) -> Result<(), MultiRowBddDecline> {
    match (computed, claimed_child) {
        (None, None) => Ok(()),
        (Some(state), Some(child)) => {
            let child =
                usize::try_from(child).map_err(|_| MultiRowBddDecline::VerificationFailed)?;
            let Some(slot) = next_states.get_mut(child) else {
                return Err(MultiRowBddDecline::VerificationFailed);
            };
            match slot {
                Some(existing) if *existing != state => Err(MultiRowBddDecline::VerificationFailed),
                Some(_) => Ok(()),
                None => {
                    *slot = Some(state);
                    Ok(())
                }
            }
        }
        (None, Some(_)) | (Some(_), None) => Err(MultiRowBddDecline::VerificationFailed),
    }
}

fn check_replay_memory(
    problem: &ReplayProblem,
    current_states: usize,
    next_states: usize,
    limits: MultiRowBddLimits,
) -> Result<(), MultiRowBddDecline> {
    let state_payload = u64::try_from(problem.lower_bounds.len())
        .unwrap_or(u64::MAX)
        .checked_mul(32)
        .and_then(|bytes| bytes.checked_add(48))
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let state_count = current_states
        .checked_add(next_states)
        // The independently computed zero/one states coexist until their
        // claimed edges have both been checked.
        .and_then(|states| states.checked_add(2))
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let state_bytes = u64::try_from(state_count)
        .unwrap_or(u64::MAX)
        .checked_mul(state_payload)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let live = problem
        .canonical_bytes
        .checked_add(state_bytes)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    if live > limits.memory_budget_bytes {
        return Err(MultiRowBddDecline::MemoryLimit);
    }
    Ok(())
}

fn count_raw_terms(
    instance: &PbInstance,
    limits: MultiRowBddLimits,
) -> Result<usize, MultiRowBddDecline> {
    let terms = instance
        .constraints
        .iter()
        .try_fold(0usize, |sum, row| sum.checked_add(row.terms.len()));
    let terms = terms.ok_or(MultiRowBddDecline::ResourceLimit)?;
    if terms > limits.max_terms {
        return Err(MultiRowBddDecline::ResourceLimit);
    }
    Ok(terms)
}

fn canonical_allocation_estimate(
    variables: usize,
    rows: usize,
    terms: usize,
) -> Result<u64, MultiRowBddDecline> {
    let variable_bytes = u64::try_from(variables)
        .unwrap_or(u64::MAX)
        .checked_mul(32)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    // Persistent row bounds plus the live suffix min/max vectors are covered
    // here.  Per-node residual intervals are accounted separately.
    let row_bytes = u64::try_from(rows)
        .unwrap_or(u64::MAX)
        .checked_mul(128)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let term_bytes = u64::try_from(terms)
        .unwrap_or(u64::MAX)
        .checked_mul(96)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    variable_bytes
        .checked_add(row_bytes)
        .and_then(|bytes| bytes.checked_add(term_bytes))
        .ok_or(MultiRowBddDecline::MemoryLimit)
}

fn checked_variable(variable: u32, num_variables: usize) -> Result<usize, MultiRowBddDecline> {
    let zero_based = variable
        .checked_sub(1)
        .ok_or(MultiRowBddDecline::InvalidLinearTerm)?;
    let zero_based =
        usize::try_from(zero_based).map_err(|_| MultiRowBddDecline::InvalidLinearTerm)?;
    if zero_based >= num_variables {
        return Err(MultiRowBddDecline::InvalidLinearTerm);
    }
    Ok(zero_based)
}

fn validate_untrusted_certificate_shape(
    instance: &PbInstance,
    certificate: &MultiRowBddInfeasibilityCertificate,
    limits: MultiRowBddLimits,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<u64, MultiRowBddDecline> {
    let variables =
        usize::try_from(instance.num_vars).map_err(|_| MultiRowBddDecline::ResourceLimit)?;
    if variables > limits.max_variables {
        return Err(MultiRowBddDecline::ResourceLimit);
    }
    if certificate.variable_order.len() != variables {
        return Err(MultiRowBddDecline::VerificationFailed);
    }
    if u64::try_from(variables).unwrap_or(u64::MAX) > limits.memory_budget_bytes {
        return Err(MultiRowBddDecline::MemoryLimit);
    }
    let mut seen = vec![false; variables];
    for (index, &variable) in certificate.variable_order.iter().enumerate() {
        if index & 0x3ff == 0 && should_stop() {
            return Err(MultiRowBddDecline::Interrupted);
        }
        let variable =
            usize::try_from(variable).map_err(|_| MultiRowBddDecline::VerificationFailed)?;
        let Some(was_seen) = seen.get_mut(variable) else {
            return Err(MultiRowBddDecline::VerificationFailed);
        };
        if *was_seen {
            return Err(MultiRowBddDecline::VerificationFailed);
        }
        *was_seen = true;
    }

    if let MultiRowBddInfeasibilityProof::DecisionDag { layers } = &certificate.proof {
        if layers.is_empty() || layers.len() > variables || layers[0].nodes.len() != 1 {
            return Err(MultiRowBddDecline::VerificationFailed);
        }
        let mut nodes = 0usize;
        for (level, layer) in layers.iter().enumerate() {
            if level & 0x3ff == 0 && should_stop() {
                return Err(MultiRowBddDecline::Interrupted);
            }
            if layer.nodes.is_empty() {
                return Err(MultiRowBddDecline::VerificationFailed);
            }
            nodes = nodes
                .checked_add(layer.nodes.len())
                .ok_or(MultiRowBddDecline::ResourceLimit)?;
            if nodes > limits.max_nodes {
                return Err(MultiRowBddDecline::ResourceLimit);
            }
        }
    }
    let bytes = estimate_certificate_bytes(certificate)?;
    if bytes > limits.memory_budget_bytes {
        return Err(MultiRowBddDecline::MemoryLimit);
    }
    Ok(bytes)
}

fn estimate_certificate_bytes(
    certificate: &MultiRowBddInfeasibilityCertificate,
) -> Result<u64, MultiRowBddDecline> {
    let mut nodes = 0usize;
    let mut layers = 0usize;
    if let MultiRowBddInfeasibilityProof::DecisionDag {
        layers: artifact_layers,
    } = &certificate.proof
    {
        layers = artifact_layers.len();
        for layer in artifact_layers {
            nodes = nodes
                .checked_add(layer.nodes.len())
                .ok_or(MultiRowBddDecline::MemoryLimit)?;
        }
    }
    let order_bytes = u64::try_from(certificate.variable_order.len())
        .unwrap_or(u64::MAX)
        .checked_mul(4)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let node_bytes = u64::try_from(nodes)
        .unwrap_or(u64::MAX)
        .checked_mul(16)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    let layer_bytes = u64::try_from(layers)
        .unwrap_or(u64::MAX)
        .checked_mul(24)
        .ok_or(MultiRowBddDecline::MemoryLimit)?;
    order_bytes
        .checked_add(node_bytes)
        .and_then(|bytes| bytes.checked_add(layer_bytes))
        .and_then(|bytes| bytes.checked_add(256))
        .ok_or(MultiRowBddDecline::MemoryLimit)
}

struct BoundedCertificateWriter {
    bytes: Vec<u8>,
    max_bytes: u64,
    exceeded: bool,
}

impl BoundedCertificateWriter {
    fn new(max_bytes: u64) -> Self {
        Self {
            bytes: Vec::new(),
            max_bytes,
            exceeded: false,
        }
    }
}

impl Write for BoundedCertificateWriter {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        let length = u64::try_from(self.bytes.len())
            .unwrap_or(u64::MAX)
            .checked_add(u64::try_from(buffer.len()).unwrap_or(u64::MAX));
        if length.is_none_or(|length| length > self.max_bytes) {
            self.exceeded = true;
            return Err(io::Error::other("multi-row BDD certificate size limit"));
        }
        self.bytes.extend_from_slice(buffer);
        Ok(buffer.len())
    }

    fn flush(&mut self) -> io::Result<()> {
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

    fn row(terms: Vec<PbTerm>, relation: PbRel, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: relation,
            rhs,
        }
    }

    fn instance(variables: u32, constraints: Vec<PbConstraint>) -> PbInstance {
        PbInstance {
            num_vars: variables,
            num_constraints: u32::try_from(constraints.len()).unwrap(),
            constraints,
            objective: None,
        }
    }

    fn exhaustive_feasible(problem: &PbInstance) -> bool {
        assert!(problem.num_vars <= 20);
        (0u64..(1u64 << problem.num_vars)).any(|assignment| {
            problem.constraints.iter().all(|constraint| {
                let value = constraint.terms.iter().fold(0i128, |sum, term| {
                    let literal = term.lits[0];
                    let selected = ((assignment >> (literal.var - 1)) & 1) != 0;
                    let literal_value = selected != literal.negated;
                    if literal_value {
                        sum + term.coeff
                    } else {
                        sum
                    }
                });
                match constraint.rel {
                    PbRel::Ge => value >= constraint.rhs,
                    PbRel::Eq => value == constraint.rhs,
                }
            })
        })
    }

    #[test]
    fn proves_joint_multi_row_contradiction() {
        // x1 and x2 must both be true, while at least one must be false.  No
        // individual row is contradictory.
        let problem = instance(
            2,
            vec![
                row(vec![term(1, 1)], PbRel::Ge, 1),
                row(vec![term(1, 2)], PbRel::Ge, 1),
                row(vec![negated_term(1, 1), negated_term(1, 2)], PbRel::Ge, 1),
            ],
        );
        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();
        assert!(matches!(
            certificate.proof,
            MultiRowBddInfeasibilityProof::DecisionDag { .. }
        ));
        verify_multi_row_bdd_infeasibility_certificate_interruptible(
            &problem,
            &certificate,
            || false,
        )
        .unwrap();
    }

    #[test]
    fn feasible_system_emits_no_refutation() {
        let problem = instance(
            3,
            vec![
                row(vec![term(2, 1), term(-1, 2)], PbRel::Ge, 0),
                row(vec![term(1, 2), term(1, 3)], PbRel::Eq, 1),
            ],
        );
        assert!(exhaustive_feasible(&problem));
        assert_eq!(
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap(),
            None
        );
    }

    #[test]
    fn root_arithmetic_contradiction_is_replayed() {
        let problem = instance(2, vec![row(vec![term(2, 1), term(3, 2)], PbRel::Eq, 9)]);
        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();
        assert_eq!(
            certificate.proof,
            MultiRowBddInfeasibilityProof::RootContradiction
        );
        verify_multi_row_bdd_infeasibility_certificate_interruptible(
            &problem,
            &certificate,
            || false,
        )
        .unwrap();
    }

    #[test]
    fn missing_optional_constraint_header_is_supported() {
        let mut problem = instance(
            1,
            vec![
                row(vec![term(1, 1)], PbRel::Ge, 1),
                row(vec![negated_term(1, 1)], PbRel::Ge, 1),
            ],
        );
        problem.num_constraints = 0;
        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();
        verify_multi_row_bdd_infeasibility_certificate_interruptible(
            &problem,
            &certificate,
            || false,
        )
        .unwrap();
    }

    #[test]
    fn dag_is_materially_smaller_than_enumeration() {
        let variables = 20u32;
        let positive = (1..=variables).map(|v| term(1, v)).collect();
        let negative = (1..=variables).map(|v| negated_term(1, v)).collect();
        // sum(x) >= 11 and sum(x) <= 10.
        let problem = instance(
            variables,
            vec![row(positive, PbRel::Ge, 11), row(negative, PbRel::Ge, 10)],
        );
        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();
        let MultiRowBddInfeasibilityProof::DecisionDag { layers } = &certificate.proof else {
            panic!("expected a decision DAG");
        };
        let nodes = layers.iter().map(|layer| layer.nodes.len()).sum::<usize>();
        assert!(nodes < 1_000, "{nodes} nodes should be far below 2^20");
        verify_multi_row_bdd_infeasibility_certificate_interruptible(
            &problem,
            &certificate,
            || false,
        )
        .unwrap();
    }

    #[test]
    fn differential_small_random_systems() {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        for variables in 1..=6u32 {
            for _case in 0..160 {
                let row_count = 1 + usize::try_from(next_random(&mut seed) % 5).unwrap();
                let mut constraints = Vec::with_capacity(row_count);
                for _ in 0..row_count {
                    let term_count = 1 + usize::try_from(next_random(&mut seed) % 8).unwrap();
                    let mut terms = Vec::with_capacity(term_count);
                    for _ in 0..term_count {
                        let variable =
                            1 + u32::try_from(next_random(&mut seed) % u64::from(variables))
                                .unwrap();
                        let mut coefficient = i128::from((next_random(&mut seed) % 7) as i8) - 3;
                        if coefficient == 0 {
                            coefficient = 1;
                        }
                        let negated = next_random(&mut seed) & 1 != 0;
                        terms.push(if negated {
                            negated_term(coefficient, variable)
                        } else {
                            term(coefficient, variable)
                        });
                    }
                    let relation = if next_random(&mut seed) % 4 == 0 {
                        PbRel::Eq
                    } else {
                        PbRel::Ge
                    };
                    let rhs = i128::from((next_random(&mut seed) % 17) as i8) - 8;
                    constraints.push(row(terms, relation, rhs));
                }
                let problem = instance(variables, constraints);
                let feasible = exhaustive_feasible(&problem);
                let artifact = generate_multi_row_bdd_infeasibility_certificate_interruptible(
                    &problem,
                    || false,
                )
                .unwrap();
                assert_eq!(artifact.is_none(), feasible, "problem: {problem:?}");
                if let Some(certificate) = artifact {
                    verify_multi_row_bdd_infeasibility_certificate_interruptible(
                        &problem,
                        &certificate,
                        || false,
                    )
                    .unwrap();
                }
            }
        }
    }

    #[test]
    fn corrupt_edge_and_merge_are_rejected() {
        let problem = instance(
            4,
            vec![
                row(vec![term(1, 1), term(1, 2)], PbRel::Ge, 1),
                row(vec![term(1, 3), term(1, 4)], PbRel::Ge, 1),
                row((1..=4).map(|v| negated_term(1, v)).collect(), PbRel::Ge, 3),
            ],
        );
        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();

        let mut out_of_range = certificate.clone();
        let MultiRowBddInfeasibilityProof::DecisionDag { layers } = &mut out_of_range.proof else {
            panic!("expected DAG");
        };
        let node = layers
            .iter_mut()
            .flat_map(|layer| &mut layer.nodes)
            .find(|node| node.zero_child.is_some() || node.one_child.is_some())
            .unwrap();
        if node.zero_child.is_some() {
            node.zero_child = Some(u32::MAX);
        } else {
            node.one_child = Some(u32::MAX);
        }
        assert_eq!(
            verify_multi_row_bdd_infeasibility_certificate_interruptible(
                &problem,
                &out_of_range,
                || false
            ),
            Err(MultiRowBddDecline::VerificationFailed)
        );

        let mut wrong_merge = certificate;
        let MultiRowBddInfeasibilityProof::DecisionDag { layers } = &mut wrong_merge.proof else {
            panic!("expected DAG");
        };
        let mut changed = false;
        for level in 0..layers.len().saturating_sub(1) {
            if layers[level + 1].nodes.len() < 2 {
                continue;
            }
            for node in &mut layers[level].nodes {
                if let Some(child) = node.one_child.or(node.zero_child) {
                    let replacement = if child == 0 { 1 } else { 0 };
                    if node.one_child.is_some() {
                        node.one_child = Some(replacement);
                    } else {
                        node.zero_child = Some(replacement);
                    }
                    changed = true;
                    break;
                }
            }
            if changed {
                break;
            }
        }
        assert!(changed);
        assert_eq!(
            verify_multi_row_bdd_infeasibility_certificate_interruptible(
                &problem,
                &wrong_merge,
                || false
            ),
            Err(MultiRowBddDecline::VerificationFailed)
        );
    }

    #[test]
    fn order_truncation_and_wrong_instance_are_rejected() {
        let problem = instance(
            3,
            vec![
                row(vec![term(1, 1)], PbRel::Ge, 1),
                row(vec![term(1, 2)], PbRel::Ge, 1),
                row(vec![negated_term(1, 1), negated_term(1, 2)], PbRel::Ge, 1),
            ],
        );
        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();

        let mut duplicate_order = certificate.clone();
        duplicate_order.variable_order[1] = duplicate_order.variable_order[0];
        assert_eq!(
            verify_multi_row_bdd_infeasibility_certificate_interruptible(
                &problem,
                &duplicate_order,
                || false
            ),
            Err(MultiRowBddDecline::VerificationFailed)
        );

        let mut truncated = certificate.clone();
        let MultiRowBddInfeasibilityProof::DecisionDag { layers } = &mut truncated.proof else {
            panic!("expected DAG");
        };
        if layers.len() > 1 {
            layers.pop();
            assert_eq!(
                verify_multi_row_bdd_infeasibility_certificate_interruptible(
                    &problem,
                    &truncated,
                    || false
                ),
                Err(MultiRowBddDecline::VerificationFailed)
            );
        }

        let feasible = instance(3, vec![row(vec![term(1, 1)], PbRel::Ge, 0)]);
        assert_eq!(
            verify_multi_row_bdd_infeasibility_certificate_interruptible(
                &feasible,
                &certificate,
                || false
            ),
            Err(MultiRowBddDecline::VerificationFailed)
        );
    }

    #[test]
    fn resource_and_interrupt_limits_fail_closed() {
        let problem = instance(
            8,
            vec![
                row((1..=8).map(|v| term(1, v)).collect(), PbRel::Ge, 5),
                row((1..=8).map(|v| negated_term(1, v)).collect(), PbRel::Ge, 4),
            ],
        );
        let tiny = MultiRowBddLimits {
            max_nodes: 1,
            ..MultiRowBddLimits::default()
        };
        assert_eq!(
            generate_multi_row_bdd_infeasibility_certificate_with_limits(&problem, tiny, || false),
            Err(MultiRowBddDecline::ResourceLimit)
        );
        assert_eq!(
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || true),
            Err(MultiRowBddDecline::Interrupted)
        );

        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();
        assert_eq!(
            verify_multi_row_bdd_infeasibility_certificate_with_limits(
                &problem,
                &certificate,
                tiny,
                || false
            ),
            Err(MultiRowBddDecline::ResourceLimit)
        );
        assert_eq!(
            verify_multi_row_bdd_infeasibility_certificate_interruptible(
                &problem,
                &certificate,
                || true
            ),
            Err(MultiRowBddDecline::Interrupted)
        );
    }

    #[test]
    fn malformed_terms_and_overflow_decline() {
        let nonlinear = instance(
            2,
            vec![row(
                vec![PbTerm {
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
                }],
                PbRel::Ge,
                1,
            )],
        );
        assert_eq!(
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&nonlinear, || false),
            Err(MultiRowBddDecline::InvalidLinearTerm)
        );

        let overflow = instance(1, vec![row(vec![negated_term(i128::MIN, 1)], PbRel::Ge, 0)]);
        assert_eq!(
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&overflow, || false),
            Err(MultiRowBddDecline::ArithmeticOverflow)
        );
    }

    #[test]
    fn bounded_json_round_trip_and_corruption() {
        let problem = instance(
            2,
            vec![
                row(vec![term(1, 1)], PbRel::Ge, 1),
                row(vec![term(1, 2)], PbRel::Ge, 1),
                row(vec![negated_term(1, 1), negated_term(1, 2)], PbRel::Ge, 1),
            ],
        );
        let certificate =
            generate_multi_row_bdd_infeasibility_certificate_interruptible(&problem, || false)
                .unwrap()
                .unwrap();
        let encoded = encode_multi_row_bdd_infeasibility_certificate_json(&certificate).unwrap();
        let decoded = decode_multi_row_bdd_infeasibility_certificate_json(&encoded).unwrap();
        assert_eq!(decoded, certificate);

        let mut trailing = encoded.clone();
        trailing.extend_from_slice(b" garbage");
        assert!(matches!(
            decode_multi_row_bdd_infeasibility_certificate_json(&trailing),
            Err(MultiRowBddCertificateCodecError::Malformed(_))
        ));

        let tiny = MultiRowBddLimits {
            memory_budget_bytes: 32,
            ..MultiRowBddLimits::default()
        };
        assert!(matches!(
            decode_multi_row_bdd_infeasibility_certificate_json_with_limits(&encoded, tiny),
            Err(MultiRowBddCertificateCodecError::Oversized { .. })
        ));
        assert!(matches!(
            encode_multi_row_bdd_infeasibility_certificate_json_with_limits(&certificate, tiny),
            Err(MultiRowBddCertificateCodecError::Oversized { .. })
        ));
    }

    fn next_random(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }
}
