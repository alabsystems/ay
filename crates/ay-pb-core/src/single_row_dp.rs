// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact pseudo-polynomial optimization for one-row 0/1 problems.
//!
//! A single bounded linear row over Boolean variables is a subset-sum (for
//! feasibility) or a 0/1 knapsack (for optimization).  Generic CDCL and MILP
//! search are particularly poor on the deliberately near-equal, large-weight
//! instances in this family.  This module recognizes the mathematical shape,
//! normalizes signed coefficients by complementing variables, and runs the
//! standard dynamic program over reachable row sums.
//!
//! The fast path for an objective proportional to the row uses a word-parallel
//! subset-sum bitset.  An arbitrary linear objective uses the usual minimum-
//! cost-per-weight DP.  Both paths are exact and reconstruct a total Boolean
//! assignment.  Every witness and objective is independently evaluated against
//! the original [`PbInstance`] before it is returned.
//!
//! Infeasibility and optimality are accepted only after a second pass in the
//! reverse item order agrees.  This is deliberately redundant: it makes the
//! route fail closed under an indexing or word-boundary defect rather than
//! granting one DP pass sole authority over a negative verdict.

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::mem::size_of;

use num_bigint::BigInt;

use crate::{PbConstraint, PbInstance, PbObjective, PbRel};

/// Maximum number of variables admitted by the default route.  Variables not
/// present in the row are optimized independently, but still consume space in
/// the returned total assignment.
const DEFAULT_MAX_VARIABLES: usize = 1_000_000;

/// Maximum number of nonzero row items.  This matches the established exact
/// equality-knapsack route and bounds both traceback work and choice storage.
const DEFAULT_MAX_ITEMS: usize = 512;

/// Largest number of DP sum states.  The memory and work gates below generally
/// bind first; this independent ceiling prevents surprising huge allocations
/// when a caller supplies unusually permissive limits.
const DEFAULT_MAX_STATES: usize = (1 << 27) + 1;

/// Maximum item/state transitions for scalar minimum-cost DP or independent
/// certificate replay.
const DEFAULT_MAX_TRANSITIONS: u64 = 250_000_000;

/// Hard peak-allocation estimate accepted by the route.
const DEFAULT_MEMORY_BUDGET_BYTES: u64 = 384 << 20;

/// A checkpoint every eight items keeps word-parallel traceback cheap without
/// retaining one full reachability bitset per item.
const CHECKPOINT_INTERVAL: usize = 8;

/// Conservative allowance for JSON tokens, deserialized Vec capacity, and the
/// input buffer coexisting with the decoded binary proof representation.
const CERTIFICATE_JSON_MEMORY_FACTOR: u64 = 16;

/// Stable JSON artifact format emitted for single-row DP infeasibility.
pub const SINGLE_ROW_DP_INFEASIBILITY_CERTIFICATE_FORMAT: &str = "ay.single-row-dp-infeasible.v1";

/// Explicit resource envelope for [`solve_single_row_binary_interruptible`].
///
/// The production adapter uses [`Default`].  Keeping the envelope typed makes
/// refusals testable and lets other in-process callers choose a smaller budget
/// without adding user-facing solver knobs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SingleRowDpLimits {
    /// Maximum declared Boolean variables.
    pub max_variables: usize,
    /// Maximum variables with a nonzero row coefficient.
    pub max_items: usize,
    /// Maximum number of represented row sums (`upper + 1`).
    pub max_states: usize,
    /// Maximum scalar item/state transitions.
    pub max_transitions: u64,
    /// Maximum estimated peak bytes retained by the DP.
    pub memory_budget_bytes: u64,
}

impl Default for SingleRowDpLimits {
    fn default() -> Self {
        Self {
            max_variables: DEFAULT_MAX_VARIABLES,
            max_items: DEFAULT_MAX_ITEMS,
            max_states: DEFAULT_MAX_STATES,
            max_transitions: DEFAULT_MAX_TRANSITIONS,
            memory_budget_bytes: DEFAULT_MEMORY_BUDGET_BYTES,
        }
    }
}

/// A conclusive result from the exact single-row route.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SingleRowDpOutcome {
    /// The row is feasible.  This variant is returned only when the instance
    /// has no objective.
    Feasible(Vec<bool>),
    /// The row interval contains no reachable Boolean sum.
    Infeasible,
    /// The exact minimum of the PB objective and a witnessing assignment.
    Optimal {
        /// Total assignment in zero-based vector order (`x1` at index zero).
        assignment: Vec<bool>,
        /// Exact value of the original PB objective.
        value: i128,
    },
}

/// Typed, fail-closed reason this specialized route returned no verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SingleRowDpDecline {
    /// Header counts or the one-row structural shape do not match.
    UnsupportedStructure,
    /// A term is nonlinear or references an invalid variable.
    InvalidLinearTerm,
    /// A checked exact-arithmetic operation overflowed.
    ArithmeticOverflow,
    /// A configured variable/item/state/work limit was exceeded.
    ResourceLimit,
    /// The estimated peak allocation exceeds the configured memory budget.
    MemoryLimit,
    /// The caller requested interruption or its deadline expired.
    Interrupted,
    /// Independent recomputation or final exact witness checking disagreed.
    VerificationFailed,
}

/// Serializable, independently replayable proof that a canonical one-row
/// Boolean PB problem has no feasible sum.
///
/// The canonical problem is an exact binding to both the row and objective.
/// The verifier reconstructs that canonical form from the supplied instance;
/// it never trusts this copy to define the problem being proved.  For a
/// nonempty target interval, `proof` contains complete reachability bitsets at
/// fixed item checkpoints.  Those bitsets are evidence, rather than a digest:
/// the verifier independently replays every intervening subset-sum transition
/// and compares the resulting state at each checkpoint.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SingleRowDpInfeasibilityCertificate {
    /// Artifact format identifier.  Unknown formats fail closed.
    pub format: String,
    /// Exact canonical row/objective binding reconstructed by the verifier.
    pub canonical_problem: SingleRowDpCanonicalProblem,
    /// Arithmetic or checkpoint-reachability proof body.
    pub proof: SingleRowDpInfeasibilityProof,
}

/// Platform-independent serialized form of the canonical signed one-row
/// problem used by the subset-sum DP.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SingleRowDpCanonicalProblem {
    /// Number of declared Boolean variables.
    pub num_variables: u64,
    /// Positive normalized row items, ordered by original variable number.
    pub items: Vec<SingleRowDpCanonicalItem>,
    /// Inclusive lower bound of the normalized reachable-sum interval.
    pub lower: u64,
    /// Inclusive upper bound of the normalized reachable-sum interval.
    pub upper: u64,
    /// Objective constant accumulated during literal/item complementation.
    pub objective_constant: i128,
    /// Distinguishes decision instances from an explicitly empty objective.
    pub has_objective: bool,
    /// Objective-minimizing values of variables absent from the row.
    pub independent_values: Vec<SingleRowDpIndependentValue>,
}

/// One positive-weight item in the canonical subset-sum problem.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SingleRowDpCanonicalItem {
    /// Zero-based original assignment index.
    pub variable: u64,
    /// Positive GCD-scaled subset-sum weight.
    pub weight: u64,
    /// Objective contribution when this normalized item is selected.
    pub cost: i128,
    /// Whether normalized selection complements the original Boolean value.
    pub flipped: bool,
}

/// Canonical objective choice for a variable absent from the row.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SingleRowDpIndependentValue {
    /// Zero-based original assignment index.
    pub variable: u64,
    /// Exact minimizing value for the independent variable.
    pub value: bool,
}

/// Proof body for a single-row infeasibility artifact.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum SingleRowDpInfeasibilityProof {
    /// Canonicalization itself proves the target interval is empty.
    EmptyInterval,
    /// Complete reachable-sum bitsets at fixed item checkpoints.
    Reachability {
        /// Number of item transitions between full bitset checkpoints.
        checkpoint_interval: u32,
        /// Checkpoints from zero processed items through all items.
        checkpoints: Vec<SingleRowDpReachabilityCheckpoint>,
    },
}

/// A complete canonical reachable-sum bitset after an item prefix.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SingleRowDpReachabilityCheckpoint {
    /// Number of canonical items whose transitions have been applied.
    pub items_processed: u32,
    /// Little-endian words: bit `s` is set exactly when sum `s` is reachable.
    pub reachable_words: Vec<u64>,
}

/// Typed failure to encode or decode a bounded JSON proof artifact.
#[derive(Debug, thiserror::Error)]
pub enum SingleRowDpCertificateCodecError {
    /// The encoded artifact exceeds the caller's memory/resource envelope.
    #[error("single-row DP certificate exceeds the {limit}-byte encoded limit")]
    Oversized {
        /// Maximum accepted encoded bytes.
        limit: u64,
    },
    /// The artifact is malformed, truncated, or otherwise invalid JSON.
    #[error("malformed single-row DP certificate: {0}")]
    Malformed(#[source] serde_json::Error),
}

/// Solve a one-row Boolean PB instance under the default resource envelope.
///
/// The interrupt callback is polled between items and within long word/state
/// loops.  [`SingleRowDpDecline::Interrupted`] grants no verdict; callers can
/// fall back only if their outer deadline still permits it.
pub fn solve_single_row_binary_interruptible<F>(
    instance: &PbInstance,
    should_stop: F,
) -> Result<SingleRowDpOutcome, SingleRowDpDecline>
where
    F: FnMut() -> bool,
{
    solve_single_row_binary_with_limits(instance, SingleRowDpLimits::default(), should_stop)
}

/// Resource-parameterized form of [`solve_single_row_binary_interruptible`].
pub fn solve_single_row_binary_with_limits<F>(
    instance: &PbInstance,
    limits: SingleRowDpLimits,
    mut should_stop: F,
) -> Result<SingleRowDpOutcome, SingleRowDpDecline>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(SingleRowDpDecline::Interrupted);
    }
    let problem = Problem::detect(instance, limits, &mut should_stop)?;
    problem.solve(instance, limits, &mut should_stop)
}

/// Generate an independently replayable infeasibility certificate under the
/// default resource envelope.
///
/// `Ok(None)` means the supported one-row problem is feasible.  No negative
/// verdict is returned unless the generated artifact has also passed the
/// independent scalar verifier.
pub fn generate_single_row_dp_infeasibility_certificate_interruptible<F>(
    instance: &PbInstance,
    should_stop: F,
) -> Result<Option<SingleRowDpInfeasibilityCertificate>, SingleRowDpDecline>
where
    F: FnMut() -> bool,
{
    generate_single_row_dp_infeasibility_certificate_with_limits(
        instance,
        SingleRowDpLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized form of
/// [`generate_single_row_dp_infeasibility_certificate_interruptible`].
pub fn generate_single_row_dp_infeasibility_certificate_with_limits<F>(
    instance: &PbInstance,
    limits: SingleRowDpLimits,
    mut should_stop: F,
) -> Result<Option<SingleRowDpInfeasibilityCertificate>, SingleRowDpDecline>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(SingleRowDpDecline::Interrupted);
    }
    let problem = Problem::detect(instance, limits, &mut should_stop)?;
    let canonical_problem = SingleRowDpCanonicalProblem::from_problem(&problem, &mut should_stop)?;
    let proof = if problem.lower > problem.upper {
        SingleRowDpInfeasibilityProof::EmptyInterval
    } else {
        certificate_resource_requirements(&problem, limits)?;
        let (reach, checkpoints) =
            reachability_pass(&problem.items, problem.upper, true, &mut should_stop)?;
        if select_reachable(
            &reach,
            problem.lower,
            problem.upper,
            Ordering::Equal,
            &mut should_stop,
        )?
        .is_some()
        {
            return Ok(None);
        }

        let mut artifact_checkpoints = Vec::with_capacity(
            problem
                .items
                .len()
                .div_ceil(CHECKPOINT_INTERVAL)
                .checked_add(1)
                .ok_or(SingleRowDpDecline::MemoryLimit)?,
        );
        for (index, checkpoint) in checkpoints.into_iter().enumerate() {
            artifact_checkpoints.push(SingleRowDpReachabilityCheckpoint {
                items_processed: u32::try_from(
                    index
                        .checked_mul(CHECKPOINT_INTERVAL)
                        .ok_or(SingleRowDpDecline::ResourceLimit)?,
                )
                .map_err(|_| SingleRowDpDecline::ResourceLimit)?,
                reachable_words: checkpoint.words,
            });
        }
        artifact_checkpoints.push(SingleRowDpReachabilityCheckpoint {
            items_processed: u32::try_from(problem.items.len())
                .map_err(|_| SingleRowDpDecline::ResourceLimit)?,
            reachable_words: reach.words,
        });
        SingleRowDpInfeasibilityProof::Reachability {
            checkpoint_interval: u32::try_from(CHECKPOINT_INTERVAL)
                .map_err(|_| SingleRowDpDecline::ResourceLimit)?,
            checkpoints: artifact_checkpoints,
        }
    };
    let certificate = SingleRowDpInfeasibilityCertificate {
        format: SINGLE_ROW_DP_INFEASIBILITY_CERTIFICATE_FORMAT.to_owned(),
        canonical_problem,
        proof,
    };
    drop(problem);

    // Certificate production is not on the existing solve fast path.  Paying
    // for an independent scalar replay here makes it impossible for callers
    // to accidentally persist an artifact the public verifier rejects.
    verify_single_row_dp_infeasibility_certificate_with_limits(
        instance,
        &certificate,
        limits,
        &mut should_stop,
    )?;
    Ok(Some(certificate))
}

/// Verify a single-row DP infeasibility artifact under the default resource
/// envelope.
///
/// The callback is polled while canonicalizing the original instance, while
/// replaying every item transition, and while checking the target interval.
pub fn verify_single_row_dp_infeasibility_certificate_interruptible<F>(
    instance: &PbInstance,
    certificate: &SingleRowDpInfeasibilityCertificate,
    should_stop: F,
) -> Result<(), SingleRowDpDecline>
where
    F: FnMut() -> bool,
{
    verify_single_row_dp_infeasibility_certificate_with_limits(
        instance,
        certificate,
        SingleRowDpLimits::default(),
        should_stop,
    )
}

/// Resource-parameterized form of
/// [`verify_single_row_dp_infeasibility_certificate_interruptible`].
pub fn verify_single_row_dp_infeasibility_certificate_with_limits<F>(
    instance: &PbInstance,
    certificate: &SingleRowDpInfeasibilityCertificate,
    limits: SingleRowDpLimits,
    mut should_stop: F,
) -> Result<(), SingleRowDpDecline>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(SingleRowDpDecline::Interrupted);
    }
    let artifact_bytes = validate_untrusted_certificate_shape(certificate, limits)?;
    if certificate.format != SINGLE_ROW_DP_INFEASIBILITY_CERTIFICATE_FORMAT {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    // The untrusted artifact remains resident while the original instance is
    // canonicalized.  Give detection only the remaining envelope so those two
    // allocations cannot each independently claim the full memory budget.
    let detection_limits = SingleRowDpLimits {
        memory_budget_bytes: limits
            .memory_budget_bytes
            .checked_sub(artifact_bytes)
            .ok_or(SingleRowDpDecline::MemoryLimit)?,
        ..limits
    };
    let problem = Problem::detect(instance, detection_limits, &mut should_stop)?;
    if !certificate
        .canonical_problem
        .matches_problem(&problem, &mut should_stop)?
    {
        return Err(SingleRowDpDecline::VerificationFailed);
    }

    match (&certificate.proof, problem.lower > problem.upper) {
        (SingleRowDpInfeasibilityProof::EmptyInterval, true) => Ok(()),
        (SingleRowDpInfeasibilityProof::EmptyInterval, false)
        | (SingleRowDpInfeasibilityProof::Reachability { .. }, true) => {
            Err(SingleRowDpDecline::VerificationFailed)
        }
        (
            SingleRowDpInfeasibilityProof::Reachability {
                checkpoint_interval,
                checkpoints,
            },
            false,
        ) => verify_reachability_certificate(
            &problem,
            *checkpoint_interval,
            checkpoints,
            limits,
            &mut should_stop,
        ),
    }
}

/// Serialize a certificate to bounded JSON using the default resource
/// envelope.
pub fn encode_single_row_dp_infeasibility_certificate_json(
    certificate: &SingleRowDpInfeasibilityCertificate,
) -> Result<Vec<u8>, SingleRowDpCertificateCodecError> {
    encode_single_row_dp_infeasibility_certificate_json_with_limits(
        certificate,
        SingleRowDpLimits::default(),
    )
}

/// Serialize a certificate to JSON without allowing the encoded output length
/// to exceed its conservative share of `limits.memory_budget_bytes`.
pub fn encode_single_row_dp_infeasibility_certificate_json_with_limits(
    certificate: &SingleRowDpInfeasibilityCertificate,
    limits: SingleRowDpLimits,
) -> Result<Vec<u8>, SingleRowDpCertificateCodecError> {
    let encoded_limit = certificate_json_encoded_limit(limits);
    let mut writer = BoundedCertificateWriter::new(encoded_limit);
    let result = serde_json::to_writer(&mut writer, certificate);
    if writer.exceeded {
        return Err(SingleRowDpCertificateCodecError::Oversized {
            limit: encoded_limit,
        });
    }
    result.map_err(SingleRowDpCertificateCodecError::Malformed)?;
    Ok(writer.bytes)
}

/// Decode a bounded JSON certificate using the default resource envelope.
pub fn decode_single_row_dp_infeasibility_certificate_json(
    encoded: &[u8],
) -> Result<SingleRowDpInfeasibilityCertificate, SingleRowDpCertificateCodecError> {
    decode_single_row_dp_infeasibility_certificate_json_with_limits(
        encoded,
        SingleRowDpLimits::default(),
    )
}

/// Decode a JSON certificate after enforcing an encoded-size limit before any
/// artifact-owned vectors are allocated.
pub fn decode_single_row_dp_infeasibility_certificate_json_with_limits(
    encoded: &[u8],
    limits: SingleRowDpLimits,
) -> Result<SingleRowDpInfeasibilityCertificate, SingleRowDpCertificateCodecError> {
    let encoded_limit = certificate_json_encoded_limit(limits);
    let encoded_len = u64::try_from(encoded.len()).unwrap_or(u64::MAX);
    if encoded_len > encoded_limit {
        return Err(SingleRowDpCertificateCodecError::Oversized {
            limit: encoded_limit,
        });
    }
    serde_json::from_slice(encoded).map_err(SingleRowDpCertificateCodecError::Malformed)
}

const fn certificate_json_encoded_limit(limits: SingleRowDpLimits) -> u64 {
    limits.memory_budget_bytes / CERTIFICATE_JSON_MEMORY_FACTOR
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Item {
    /// Zero-based assignment index.
    variable: usize,
    /// Positive, scaled DP weight.
    weight: usize,
    /// Objective contribution when the normalized item is selected.
    cost: i128,
    /// Original variable value is `selected != flipped`.
    flipped: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Problem {
    num_vars: usize,
    items: Vec<Item>,
    lower: usize,
    upper: usize,
    objective_constant: i128,
    has_objective: bool,
    independent_values: Vec<(usize, bool)>,
}

impl SingleRowDpCanonicalProblem {
    fn from_problem(
        problem: &Problem,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Self, SingleRowDpDecline> {
        let mut items = Vec::with_capacity(problem.items.len());
        for (index, item) in problem.items.iter().enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            items.push(SingleRowDpCanonicalItem {
                variable: u64::try_from(item.variable)
                    .map_err(|_| SingleRowDpDecline::ResourceLimit)?,
                weight: u64::try_from(item.weight)
                    .map_err(|_| SingleRowDpDecline::ResourceLimit)?,
                cost: item.cost,
                flipped: item.flipped,
            });
        }
        let mut independent_values = Vec::with_capacity(problem.independent_values.len());
        for (index, &(variable, value)) in problem.independent_values.iter().enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            independent_values.push(SingleRowDpIndependentValue {
                variable: u64::try_from(variable).map_err(|_| SingleRowDpDecline::ResourceLimit)?,
                value,
            });
        }
        Ok(Self {
            num_variables: u64::try_from(problem.num_vars)
                .map_err(|_| SingleRowDpDecline::ResourceLimit)?,
            items,
            lower: u64::try_from(problem.lower).map_err(|_| SingleRowDpDecline::ResourceLimit)?,
            upper: u64::try_from(problem.upper).map_err(|_| SingleRowDpDecline::ResourceLimit)?,
            objective_constant: problem.objective_constant,
            has_objective: problem.has_objective,
            independent_values,
        })
    }

    fn matches_problem(
        &self,
        problem: &Problem,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<bool, SingleRowDpDecline> {
        if self.num_variables != u64::try_from(problem.num_vars).unwrap_or(u64::MAX)
            || self.lower != u64::try_from(problem.lower).unwrap_or(u64::MAX)
            || self.upper != u64::try_from(problem.upper).unwrap_or(u64::MAX)
            || self.objective_constant != problem.objective_constant
            || self.has_objective != problem.has_objective
            || self.items.len() != problem.items.len()
            || self.independent_values.len() != problem.independent_values.len()
        {
            return Ok(false);
        }
        for (index, (artifact, item)) in self.items.iter().zip(&problem.items).enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            if artifact.variable != u64::try_from(item.variable).unwrap_or(u64::MAX)
                || artifact.weight != u64::try_from(item.weight).unwrap_or(u64::MAX)
                || artifact.cost != item.cost
                || artifact.flipped != item.flipped
            {
                return Ok(false);
            }
        }
        for (index, (artifact, &(variable, value))) in self
            .independent_values
            .iter()
            .zip(&problem.independent_values)
            .enumerate()
        {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            if artifact.variable != u64::try_from(variable).unwrap_or(u64::MAX)
                || artifact.value != value
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
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
        let new_len = u64::try_from(self.bytes.len())
            .unwrap_or(u64::MAX)
            .checked_add(u64::try_from(buffer.len()).unwrap_or(u64::MAX));
        if new_len.is_none_or(|length| length > self.max_bytes) {
            self.exceeded = true;
            return Err(io::Error::other("single-row DP certificate size limit"));
        }
        self.bytes.extend_from_slice(buffer);
        Ok(buffer.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Problem {
    fn detect(
        instance: &PbInstance,
        limits: SingleRowDpLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<Self, SingleRowDpDecline> {
        let num_vars =
            usize::try_from(instance.num_vars).map_err(|_| SingleRowDpDecline::ResourceLimit)?;
        if num_vars > limits.max_variables
            || instance.num_constraints as usize != instance.constraints.len()
        {
            return Err(SingleRowDpDecline::UnsupportedStructure);
        }

        // Canonicalization retains ordered maps of the row/objective support.
        // Bound their worst-case live footprint before allocating.  Counting
        // raw terms is conservative when duplicates cancel, which is fine for
        // a specialization: a decline leaves the generic solver authoritative.
        let row_terms = instance
            .constraints
            .iter()
            .try_fold(0usize, |count, row| count.checked_add(row.terms.len()))
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        let objective_terms = instance
            .objective
            .as_ref()
            .map_or(0, |objective| objective.terms.len());
        let retained_entries = row_terms
            .min(num_vars.saturating_mul(instance.constraints.len()))
            .checked_add(objective_terms.min(num_vars))
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        // A BTreeMap node has allocator/link overhead in addition to its key
        // and i128 value.  Ninety-six bytes per possible entry deliberately
        // overestimates current standard-library layouts.
        let canonical_bytes = (retained_entries as u64)
            .checked_mul(96)
            .and_then(|bytes| bytes.checked_add(num_vars as u64))
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        if canonical_bytes > limits.memory_budget_bytes {
            return Err(SingleRowDpDecline::MemoryLimit);
        }

        let (row_coeffs, mut lower, upper) =
            detect_row(&instance.constraints, num_vars, should_stop)?;
        if row_coeffs.len() > limits.max_items {
            return Err(SingleRowDpDecline::ResourceLimit);
        }
        let (objective_coeffs, mut objective_constant) = match &instance.objective {
            Some(objective) => {
                let (coefficients, rhs_adjustment) =
                    canonicalize_terms(&objective.terms, 0, num_vars, should_stop)?;
                let constant = rhs_adjustment
                    .checked_neg()
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
                (coefficients, constant)
            }
            None => (BTreeMap::new(), 0),
        };

        let mut items = Vec::with_capacity(row_coeffs.len());
        let mut row_offset = 0i128;
        let mut total = 0i128;
        for (index, (&var, &coefficient)) in row_coeffs.iter().enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            if coefficient == 0 {
                continue;
            }
            let objective_coefficient = objective_coeffs.get(&var).copied().unwrap_or(0);
            let (weight, cost, flipped) = if coefficient > 0 {
                (coefficient, objective_coefficient, false)
            } else {
                let weight = coefficient
                    .checked_neg()
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
                row_offset = row_offset
                    .checked_add(coefficient)
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
                objective_constant = objective_constant
                    .checked_add(objective_coefficient)
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
                let cost = objective_coefficient
                    .checked_neg()
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
                (weight, cost, true)
            };
            total = total
                .checked_add(weight)
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
            items.push(Item {
                variable: usize::try_from(var - 1)
                    .map_err(|_| SingleRowDpDecline::InvalidLinearTerm)?,
                weight: usize::try_from(weight).map_err(|_| SingleRowDpDecline::ResourceLimit)?,
                cost,
                flipped,
            });
        }

        lower = lower
            .checked_sub(row_offset)
            .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
        let upper = upper
            .unwrap_or(total)
            .checked_sub(row_offset)
            .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;

        // Variables absent from the row are independent.  Set each to its
        // exact minimum-cost value now and retain that choice in the witness.
        let mut independent_values = Vec::new();
        for (index, (&var, &coefficient)) in objective_coeffs.iter().enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            if row_coeffs.contains_key(&var) {
                continue;
            }
            let value = coefficient < 0;
            if value {
                objective_constant = objective_constant
                    .checked_add(coefficient)
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
            }
            independent_values.push((
                usize::try_from(var - 1).map_err(|_| SingleRowDpDecline::InvalidLinearTerm)?,
                value,
            ));
        }

        // The positive-weight form can attain only [0,total].  An empty
        // intersection is a conclusive arithmetic infeasibility proof.
        let clipped_lower = lower.max(0);
        let clipped_upper = upper.min(total);
        if clipped_lower > clipped_upper {
            return Ok(Self {
                num_vars,
                items,
                lower: 1,
                upper: 0,
                objective_constant,
                has_objective: instance.objective.is_some(),
                independent_values,
            });
        }

        // Every reachable sum is divisible by the row-weight GCD.  Scaling by
        // it is exact: [L,U] becomes [ceil(L/g), floor(U/g)].
        let gcd = items
            .iter()
            .map(|item| item.weight)
            .fold(0usize, gcd_usize)
            .max(1);
        let mut lower = div_ceil_nonnegative(
            usize::try_from(clipped_lower).map_err(|_| SingleRowDpDecline::ResourceLimit)?,
            gcd,
        );
        let mut upper =
            usize::try_from(clipped_upper).map_err(|_| SingleRowDpDecline::ResourceLimit)? / gcd;
        let total = usize::try_from(total).map_err(|_| SingleRowDpDecline::ResourceLimit)? / gcd;
        for item in &mut items {
            item.weight /= gcd;
        }
        if lower > upper {
            return Ok(Self {
                num_vars,
                items,
                lower: 1,
                upper: 0,
                objective_constant,
                has_objective: instance.objective.is_some(),
                independent_values,
            });
        }

        // Complement every normalized item when that reduces the represented
        // maximum sum.  This is a bijection and can turn a near-total lower
        // bound into a tiny DP.
        if total
            .checked_sub(lower)
            .ok_or(SingleRowDpDecline::ArithmeticOverflow)?
            < upper
        {
            let new_lower = total
                .checked_sub(upper)
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
            let new_upper = total
                .checked_sub(lower)
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
            lower = new_lower;
            upper = new_upper;
            for item in &mut items {
                objective_constant = objective_constant
                    .checked_add(item.cost)
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
                item.cost = item
                    .cost
                    .checked_neg()
                    .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
                item.flipped = !item.flipped;
            }
        }

        let states = upper
            .checked_add(1)
            .ok_or(SingleRowDpDecline::ResourceLimit)?;
        if states > limits.max_states {
            return Err(SingleRowDpDecline::ResourceLimit);
        }

        Ok(Self {
            num_vars,
            items,
            lower,
            upper,
            objective_constant,
            has_objective: instance.objective.is_some(),
            independent_values,
        })
    }

    fn solve(
        &self,
        instance: &PbInstance,
        limits: SingleRowDpLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<SingleRowDpOutcome, SingleRowDpDecline> {
        if self.lower > self.upper {
            return Ok(SingleRowDpOutcome::Infeasible);
        }

        let proportional = !self.has_objective || proportional_direction(&self.items).is_some();
        if proportional {
            self.solve_reachability(instance, limits, should_stop)
        } else {
            self.solve_min_cost(instance, limits, should_stop)
        }
    }

    fn solve_reachability(
        &self,
        instance: &PbInstance,
        limits: SingleRowDpLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<SingleRowDpOutcome, SingleRowDpDecline> {
        let words = bit_words(self.upper + 1)?;
        let checkpoint_count = self.items.len().div_ceil(CHECKPOINT_INTERVAL);
        let live_bitsets = checkpoint_count
            .checked_add(CHECKPOINT_INTERVAL + 5)
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        let bitset_bytes = words
            .checked_mul(size_of::<u64>())
            .and_then(|bytes| bytes.checked_mul(live_bitsets))
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        let assignment_bytes = self.num_vars;
        if (bitset_bytes as u64).saturating_add(assignment_bytes as u64)
            > limits.memory_budget_bytes
        {
            return Err(SingleRowDpDecline::MemoryLimit);
        }

        let (reach, checkpoints) = reachability_pass(&self.items, self.upper, true, should_stop)?;
        let direction = if self.has_objective {
            proportional_direction(&self.items).ok_or(SingleRowDpDecline::VerificationFailed)?
        } else {
            Ordering::Equal
        };
        let target = select_reachable(&reach, self.lower, self.upper, direction, should_stop)?;

        // Independent pass in the opposite item order.  It must expose the
        // same extremal reachable sum (or the same absence of one).
        let mut reversed = self.items.clone();
        reversed.reverse();
        let (confirm, _) = reachability_pass(&reversed, self.upper, false, should_stop)?;
        let confirmed = select_reachable(&confirm, self.lower, self.upper, direction, should_stop)?;
        if target != confirmed {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        let Some(target) = target else {
            return Ok(SingleRowDpOutcome::Infeasible);
        };

        let selected =
            traceback_reachability(&self.items, target, &checkpoints, self.upper, should_stop)?;
        self.checked_outcome(instance, &selected, should_stop)
    }

    fn solve_min_cost(
        &self,
        instance: &PbInstance,
        limits: SingleRowDpLimits,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<SingleRowDpOutcome, SingleRowDpDecline> {
        let states = self.upper + 1;
        let transitions = (states as u64).saturating_mul(self.items.len() as u64);
        if transitions > limits.max_transitions {
            return Err(SingleRowDpDecline::ResourceLimit);
        }
        let choice_bits = states
            .checked_mul(self.items.len())
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        let choice_words = bit_words(choice_bits)?;
        let reachable_bytes = bit_words(states)?
            .checked_mul(size_of::<u64>())
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        let choice_bytes = choice_words
            .checked_mul(size_of::<u64>())
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        let live_bytes = states
            .checked_mul(size_of::<i128>())
            .and_then(|bytes| bytes.checked_add(reachable_bytes))
            .and_then(|bytes| bytes.checked_add(choice_bytes))
            .and_then(|bytes| bytes.checked_add(self.num_vars))
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        if live_bytes as u64 > limits.memory_budget_bytes {
            return Err(SingleRowDpDecline::MemoryLimit);
        }

        let first = min_cost_pass(&self.items, self.lower, self.upper, true, should_stop)?;
        let mut reversed = self.items.clone();
        reversed.reverse();
        let confirm = min_cost_pass(&reversed, self.lower, self.upper, false, should_stop)?;
        if first.best_cost != confirm.best_cost {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        let Some(target) = first.best_sum else {
            return Ok(SingleRowDpOutcome::Infeasible);
        };
        let selected = traceback_choices(
            &self.items,
            target,
            states,
            first
                .choices
                .as_ref()
                .ok_or(SingleRowDpDecline::VerificationFailed)?,
        )?;
        let selected_cost = self
            .items
            .iter()
            .zip(&selected)
            .filter(|&(_, &used)| used)
            // `min_cost_pass` stores only the selected-item contribution;
            // the normalization constant is added when the original
            // objective is checked in `checked_outcome` below.
            .try_fold(0i128, |sum, (item, _)| sum.checked_add(item.cost))
            .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
        if Some(selected_cost) != first.best_cost {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        self.checked_outcome(instance, &selected, should_stop)
    }

    fn checked_outcome(
        &self,
        instance: &PbInstance,
        selected: &[bool],
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<SingleRowDpOutcome, SingleRowDpDecline> {
        if selected.len() != self.items.len() {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        let mut assignment = vec![false; self.num_vars];
        for (index, &(variable, value)) in self.independent_values.iter().enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            assignment[variable] = value;
        }
        for (index, (item, &used)) in self.items.iter().zip(selected).enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            assignment[item.variable] = used != item.flipped;
        }
        if !verify_constraints_interruptible(&instance.constraints, &assignment, should_stop)? {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        let Some(objective) = &instance.objective else {
            return Ok(SingleRowDpOutcome::Feasible(assignment));
        };
        let value = eval_objective_interruptible(objective, &assignment, should_stop)?;
        let normalized_value = self
            .items
            .iter()
            .zip(selected)
            .filter(|&(_, &used)| used)
            .try_fold(self.objective_constant, |sum, (item, _)| {
                sum.checked_add(item.cost)
            })
            .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
        if normalized_value != value {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        Ok(SingleRowDpOutcome::Optimal { assignment, value })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ordering {
    Less,
    Equal,
    Greater,
}

/// Return the sign of the common objective/weight ratio, or `None` when the
/// objective is not proportional to the row.  Cross products are checked;
/// overflow simply selects the general DP.
fn proportional_direction(items: &[Item]) -> Option<Ordering> {
    let Some(first) = items.iter().find(|item| item.cost != 0) else {
        return Some(Ordering::Equal);
    };
    let first_weight = i128::try_from(first.weight).ok()?;
    for item in items {
        let weight = i128::try_from(item.weight).ok()?;
        if item.cost.checked_mul(first_weight)? != first.cost.checked_mul(weight)? {
            return None;
        }
    }
    Some(if first.cost < 0 {
        Ordering::Less
    } else {
        Ordering::Greater
    })
}

fn detect_row(
    constraints: &[PbConstraint],
    num_vars: usize,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<(BTreeMap<u32, i128>, i128, Option<i128>), SingleRowDpDecline> {
    match constraints {
        [row] if row.rel == PbRel::Eq => {
            let (coeffs, rhs) = canonicalize_terms(&row.terms, row.rhs, num_vars, should_stop)?;
            Ok((coeffs, rhs, Some(rhs)))
        }
        [row] if row.rel == PbRel::Ge => {
            let (coeffs, rhs) = canonicalize_terms(&row.terms, row.rhs, num_vars, should_stop)?;
            Ok((coeffs, rhs, None))
        }
        [a, b] if a.rel == PbRel::Ge && b.rel == PbRel::Ge => {
            let (ca, ra) = canonicalize_terms(&a.terms, a.rhs, num_vars, should_stop)?;
            let (cb, rb) = canonicalize_terms(&b.terms, b.rhs, num_vars, should_stop)?;
            if ca.len() != cb.len()
                || ca.iter().any(|(var, coefficient)| {
                    cb.get(var).and_then(|other| other.checked_neg()) != Some(*coefficient)
                })
            {
                return Err(SingleRowDpDecline::UnsupportedStructure);
            }
            let upper = rb
                .checked_neg()
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
            Ok((ca, ra, Some(upper)))
        }
        _ => Err(SingleRowDpDecline::UnsupportedStructure),
    }
}

/// Canonicalize linear terms to positive-literal coefficients.  A negated
/// literal `c*~x` becomes `-c*x` and subtracts `c` from the row RHS/objective
/// constant supplied by the caller.
fn canonicalize_terms(
    terms: &[crate::PbTerm],
    mut constant: i128,
    num_vars: usize,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<(BTreeMap<u32, i128>, i128), SingleRowDpDecline> {
    let mut coeffs = BTreeMap::<u32, i128>::new();
    for (index, term) in terms.iter().enumerate() {
        if index & 0x3ff == 0 && should_stop() {
            return Err(SingleRowDpDecline::Interrupted);
        }
        let [literal] = term.lits.as_slice() else {
            return Err(SingleRowDpDecline::InvalidLinearTerm);
        };
        let index = literal
            .var
            .checked_sub(1)
            .and_then(|index| usize::try_from(index).ok())
            .filter(|&index| index < num_vars)
            .ok_or(SingleRowDpDecline::InvalidLinearTerm)?;
        let _ = index;
        let coefficient = if literal.negated {
            constant = constant
                .checked_sub(term.coeff)
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
            term.coeff
                .checked_neg()
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?
        } else {
            term.coeff
        };
        let entry = coeffs.entry(literal.var).or_insert(0);
        *entry = entry
            .checked_add(coefficient)
            .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
    }
    coeffs.retain(|_, coefficient| *coefficient != 0);
    Ok((coeffs, constant))
}

/// Re-evaluate the original rows with independent exact arithmetic while
/// retaining deadline/cancellation responsiveness.  Detection already proved
/// every term linear; this boundary checks that invariant again instead of
/// relying on it for indexing safety.
fn verify_constraints_interruptible(
    constraints: &[PbConstraint],
    assignment: &[bool],
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<bool, SingleRowDpDecline> {
    for constraint in constraints {
        let mut lhs = BigInt::from(0);
        for (index, term) in constraint.terms.iter().enumerate() {
            if index & 0x3ff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            let [literal] = term.lits.as_slice() else {
                return Err(SingleRowDpDecline::VerificationFailed);
            };
            let variable = literal
                .var
                .checked_sub(1)
                .and_then(|value| usize::try_from(value).ok())
                .and_then(|value| assignment.get(value).copied())
                .ok_or(SingleRowDpDecline::VerificationFailed)?;
            if variable != literal.negated {
                lhs += BigInt::from(term.coeff);
            }
        }
        let rhs = BigInt::from(constraint.rhs);
        let satisfied = match constraint.rel {
            PbRel::Ge => lhs >= rhs,
            PbRel::Eq => lhs == rhs,
        };
        if !satisfied {
            return Ok(false);
        }
    }
    Ok(true)
}

fn eval_objective_interruptible(
    objective: &PbObjective,
    assignment: &[bool],
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<i128, SingleRowDpDecline> {
    let mut value = 0i128;
    for (index, term) in objective.terms.iter().enumerate() {
        if index & 0x3ff == 0 && should_stop() {
            return Err(SingleRowDpDecline::Interrupted);
        }
        let [literal] = term.lits.as_slice() else {
            return Err(SingleRowDpDecline::VerificationFailed);
        };
        let variable = literal
            .var
            .checked_sub(1)
            .and_then(|raw| usize::try_from(raw).ok())
            .and_then(|column| assignment.get(column).copied())
            .ok_or(SingleRowDpDecline::VerificationFailed)?;
        if variable != literal.negated {
            value = value
                .checked_add(term.coeff)
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
        }
    }
    Ok(value)
}

fn validate_untrusted_certificate_shape(
    certificate: &SingleRowDpInfeasibilityCertificate,
    limits: SingleRowDpLimits,
) -> Result<u64, SingleRowDpDecline> {
    let canonical = &certificate.canonical_problem;
    if canonical.num_variables > u64::try_from(limits.max_variables).unwrap_or(u64::MAX)
        || canonical.items.len() > limits.max_items
        || canonical.independent_values.len() > limits.max_variables
    {
        return Err(SingleRowDpDecline::ResourceLimit);
    }
    let canonical_entries = canonical
        .items
        .len()
        .checked_add(canonical.independent_values.len())
        .ok_or(SingleRowDpDecline::MemoryLimit)?;
    // This deliberately overestimates the current Vec element layouts and
    // accounts for the already-deserialized canonical binding.
    let mut retained_bytes = u64::try_from(canonical_entries)
        .unwrap_or(u64::MAX)
        .checked_mul(128)
        .ok_or(SingleRowDpDecline::MemoryLimit)?;
    if let SingleRowDpInfeasibilityProof::Reachability { checkpoints, .. } = &certificate.proof {
        let maximum_checkpoints = limits
            .max_items
            .checked_add(1)
            .ok_or(SingleRowDpDecline::ResourceLimit)?;
        if checkpoints.len() > maximum_checkpoints {
            return Err(SingleRowDpDecline::ResourceLimit);
        }
        let total_words = checkpoints.iter().try_fold(0usize, |total, checkpoint| {
            total.checked_add(checkpoint.reachable_words.len())
        });
        let total_words = total_words.ok_or(SingleRowDpDecline::MemoryLimit)?;
        let checkpoint_bytes = u64::try_from(total_words)
            .unwrap_or(u64::MAX)
            .checked_mul(size_of::<u64>() as u64)
            .and_then(|bytes| {
                bytes.checked_add(
                    u64::try_from(checkpoints.len())
                        .unwrap_or(u64::MAX)
                        .saturating_mul(64),
                )
            })
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
        retained_bytes = retained_bytes
            .checked_add(checkpoint_bytes)
            .ok_or(SingleRowDpDecline::MemoryLimit)?;
    }
    if retained_bytes > limits.memory_budget_bytes {
        return Err(SingleRowDpDecline::MemoryLimit);
    }
    Ok(retained_bytes)
}

fn certificate_resource_requirements(
    problem: &Problem,
    limits: SingleRowDpLimits,
) -> Result<(usize, usize, usize), SingleRowDpDecline> {
    let states = problem
        .upper
        .checked_add(1)
        .ok_or(SingleRowDpDecline::ResourceLimit)?;
    if states > limits.max_states {
        return Err(SingleRowDpDecline::ResourceLimit);
    }
    // The artifact verifier deliberately uses an implementation-independent
    // scalar recurrence.  Account for every one of those state transitions,
    // plus the final target-interval scan, before generating an artifact.
    let scalar_transitions = u64::try_from(states)
        .unwrap_or(u64::MAX)
        .checked_mul(u64::try_from(problem.items.len()).unwrap_or(u64::MAX))
        .and_then(|work| work.checked_add(u64::try_from(states).unwrap_or(u64::MAX)))
        .ok_or(SingleRowDpDecline::ResourceLimit)?;
    if scalar_transitions > limits.max_transitions {
        return Err(SingleRowDpDecline::ResourceLimit);
    }

    let words = bit_words(states)?;
    let checkpoint_count = problem
        .items
        .len()
        .div_ceil(CHECKPOINT_INTERVAL)
        .checked_add(1)
        .ok_or(SingleRowDpDecline::MemoryLimit)?;
    let bitset_count = checkpoint_count
        .checked_add(1)
        .ok_or(SingleRowDpDecline::MemoryLimit)?;
    let bitset_bytes = words
        .checked_mul(size_of::<u64>())
        .and_then(|bytes| bytes.checked_mul(bitset_count))
        .ok_or(SingleRowDpDecline::MemoryLimit)?;
    let canonical_entries = problem
        .items
        .len()
        .checked_add(problem.independent_values.len())
        .ok_or(SingleRowDpDecline::MemoryLimit)?;
    let retained_bytes = u64::try_from(bitset_bytes)
        .map_err(|_| SingleRowDpDecline::MemoryLimit)?
        .checked_add(
            u64::try_from(canonical_entries)
                .unwrap_or(u64::MAX)
                .saturating_mul(128),
        )
        .and_then(|bytes| {
            bytes.checked_add(
                u64::try_from(checkpoint_count)
                    .unwrap_or(u64::MAX)
                    .saturating_mul(64),
            )
        })
        .ok_or(SingleRowDpDecline::MemoryLimit)?;
    if retained_bytes > limits.memory_budget_bytes {
        return Err(SingleRowDpDecline::MemoryLimit);
    }
    Ok((states, words, checkpoint_count))
}

fn verify_reachability_certificate(
    problem: &Problem,
    checkpoint_interval: u32,
    checkpoints: &[SingleRowDpReachabilityCheckpoint],
    limits: SingleRowDpLimits,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<(), SingleRowDpDecline> {
    if usize::try_from(checkpoint_interval).ok() != Some(CHECKPOINT_INTERVAL) {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    let (_states, words, expected_checkpoints) =
        certificate_resource_requirements(problem, limits)?;
    if checkpoints.len() != expected_checkpoints {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    if checkpoints
        .iter()
        .any(|checkpoint| checkpoint.reachable_words.len() != words)
    {
        return Err(SingleRowDpDecline::VerificationFailed);
    }

    // This is intentionally not `BitSet::or_shifted_self`, which generated
    // the artifact word-parallel.  A descending scalar recurrence provides an
    // implementation-independent replay of every item transition.
    let mut reconstructed = BitSet::new(problem.upper)?;
    let mut processed = 0usize;
    for (index, checkpoint) in checkpoints.iter().enumerate() {
        if should_stop() {
            return Err(SingleRowDpDecline::Interrupted);
        }
        let expected_processed = if index + 1 == checkpoints.len() {
            problem.items.len()
        } else {
            index
                .checked_mul(CHECKPOINT_INTERVAL)
                .ok_or(SingleRowDpDecline::VerificationFailed)?
        };
        if usize::try_from(checkpoint.items_processed).ok() != Some(expected_processed)
            || expected_processed < processed
            || expected_processed > problem.items.len()
        {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        for item in &problem.items[processed..expected_processed] {
            or_shifted_self_scalar(&mut reconstructed, item.weight, should_stop)?;
        }
        if reconstructed.words != checkpoint.reachable_words {
            return Err(SingleRowDpDecline::VerificationFailed);
        }
        processed = expected_processed;
    }
    if processed != problem.items.len() {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    if select_reachable(
        &reconstructed,
        problem.lower,
        problem.upper,
        Ordering::Equal,
        should_stop,
    )?
    .is_some()
    {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    Ok(())
}

fn or_shifted_self_scalar(
    reachable: &mut BitSet,
    shift: usize,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<(), SingleRowDpDecline> {
    if shift == 0 || shift > reachable.max_bit {
        return Ok(());
    }
    for (polled, sum) in (shift..=reachable.max_bit).rev().enumerate() {
        if polled & 0xfff == 0 && should_stop() {
            return Err(SingleRowDpDecline::Interrupted);
        }
        if reachable.get(sum - shift) {
            reachable.set(sum);
        }
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BitSet {
    words: Vec<u64>,
    max_bit: usize,
}

impl BitSet {
    fn new(max_bit: usize) -> Result<Self, SingleRowDpDecline> {
        let mut words = vec![0; bit_words(max_bit + 1)?];
        words[0] = 1;
        Ok(Self { words, max_bit })
    }

    fn get(&self, bit: usize) -> bool {
        bit <= self.max_bit && (self.words[bit / 64] >> (bit % 64)) & 1 == 1
    }

    fn set(&mut self, bit: usize) {
        self.words[bit / 64] |= 1u64 << (bit % 64);
    }

    fn or_shifted_self(
        &mut self,
        shift: usize,
        should_stop: &mut dyn FnMut() -> bool,
    ) -> Result<(), SingleRowDpDecline> {
        if shift == 0 || shift > self.max_bit {
            return Ok(());
        }
        let word_shift = shift / 64;
        let bit_shift = shift % 64;
        let len = self.words.len();
        for (polled, i) in (word_shift..len).rev().enumerate() {
            if polled & 0xfff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            let mut shifted = self.words[i - word_shift] << bit_shift;
            if bit_shift != 0 && i > word_shift {
                shifted |= self.words[i - word_shift - 1] >> (64 - bit_shift);
            }
            self.words[i] |= shifted;
        }
        let used = self.max_bit % 64 + 1;
        if used < 64 {
            let last = self.words.len() - 1;
            self.words[last] &= (1u64 << used) - 1;
        }
        Ok(())
    }
}

fn reachability_pass(
    items: &[Item],
    upper: usize,
    retain_checkpoints: bool,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<(BitSet, Vec<BitSet>), SingleRowDpDecline> {
    let mut reach = BitSet::new(upper)?;
    let mut checkpoints = if retain_checkpoints {
        Vec::with_capacity(items.len().div_ceil(CHECKPOINT_INTERVAL))
    } else {
        Vec::new()
    };
    for (index, item) in items.iter().enumerate() {
        if should_stop() {
            return Err(SingleRowDpDecline::Interrupted);
        }
        if retain_checkpoints && index % CHECKPOINT_INTERVAL == 0 {
            checkpoints.push(reach.clone());
        }
        reach.or_shifted_self(item.weight, should_stop)?;
    }
    Ok((reach, checkpoints))
}

fn select_reachable(
    reach: &BitSet,
    lower: usize,
    upper: usize,
    direction: Ordering,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<Option<usize>, SingleRowDpDecline> {
    match direction {
        Ordering::Less => {
            for (polled, sum) in (lower..=upper).rev().enumerate() {
                if polled & 0xfff == 0 && should_stop() {
                    return Err(SingleRowDpDecline::Interrupted);
                }
                if reach.get(sum) {
                    return Ok(Some(sum));
                }
            }
        }
        Ordering::Equal | Ordering::Greater => {
            for (polled, sum) in (lower..=upper).enumerate() {
                if polled & 0xfff == 0 && should_stop() {
                    return Err(SingleRowDpDecline::Interrupted);
                }
                if reach.get(sum) {
                    return Ok(Some(sum));
                }
            }
        }
    }
    Ok(None)
}

fn traceback_reachability(
    items: &[Item],
    target: usize,
    checkpoints: &[BitSet],
    upper: usize,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<Vec<bool>, SingleRowDpDecline> {
    if items.is_empty() {
        return if target == 0 {
            Ok(Vec::new())
        } else {
            Err(SingleRowDpDecline::VerificationFailed)
        };
    }
    let expected = items.len().div_ceil(CHECKPOINT_INTERVAL);
    if checkpoints.len() != expected {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    let mut selected = vec![false; items.len()];
    let mut remaining = target;
    for checkpoint_index in (0..checkpoints.len()).rev() {
        let start = checkpoint_index * CHECKPOINT_INTERVAL;
        let end = (start + CHECKPOINT_INTERVAL).min(items.len());
        let mut prefixes = Vec::with_capacity(end - start + 1);
        prefixes.push(checkpoints[checkpoint_index].clone());
        for item in &items[start..end] {
            let mut next = prefixes
                .last()
                .cloned()
                .ok_or(SingleRowDpDecline::VerificationFailed)?;
            next.or_shifted_self(item.weight, should_stop)?;
            prefixes.push(next);
        }
        for index in (start..end).rev() {
            if should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            let without = &prefixes[index - start];
            if without.get(remaining) {
                continue;
            }
            let weight = items[index].weight;
            if remaining < weight || !without.get(remaining - weight) {
                return Err(SingleRowDpDecline::VerificationFailed);
            }
            selected[index] = true;
            remaining -= weight;
        }
    }
    if remaining != 0 || target > upper {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    Ok(selected)
}

#[derive(Debug)]
struct MinCostPass {
    best_sum: Option<usize>,
    best_cost: Option<i128>,
    choices: Option<BitSet>,
}

fn min_cost_pass(
    items: &[Item],
    lower: usize,
    upper: usize,
    retain_choices: bool,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<MinCostPass, SingleRowDpDecline> {
    let states = upper + 1;
    let mut costs = vec![0i128; states];
    let mut reachable = BitSet::new(upper)?;
    let mut choices = if retain_choices {
        Some(BitSet {
            words: vec![
                0;
                bit_words(
                    states
                        .checked_mul(items.len())
                        .ok_or(SingleRowDpDecline::MemoryLimit,)?
                )?
            ],
            max_bit: states
                .checked_mul(items.len())
                .and_then(|bits| bits.checked_sub(1))
                .unwrap_or(0),
        })
    } else {
        None
    };

    for (item_index, item) in items.iter().enumerate() {
        if should_stop() {
            return Err(SingleRowDpDecline::Interrupted);
        }
        if item.weight > upper {
            continue;
        }
        for (polled, sum) in (item.weight..=upper).rev().enumerate() {
            if polled & 0xfff == 0 && should_stop() {
                return Err(SingleRowDpDecline::Interrupted);
            }
            let predecessor = sum - item.weight;
            if !reachable.get(predecessor) {
                continue;
            }
            let candidate = costs[predecessor]
                .checked_add(item.cost)
                .ok_or(SingleRowDpDecline::ArithmeticOverflow)?;
            if !reachable.get(sum) || candidate < costs[sum] {
                costs[sum] = candidate;
                reachable.set(sum);
                if let Some(choice_bits) = &mut choices {
                    choice_bits.set(
                        item_index
                            .checked_mul(states)
                            .and_then(|base| base.checked_add(sum))
                            .ok_or(SingleRowDpDecline::MemoryLimit)?,
                    );
                }
            }
        }
    }

    let mut best_sum = None;
    let mut best_cost = None;
    for (polled, sum) in (lower..=upper).enumerate() {
        if polled & 0xfff == 0 && should_stop() {
            return Err(SingleRowDpDecline::Interrupted);
        }
        if !reachable.get(sum) {
            continue;
        }
        if best_cost.is_none_or(|best| costs[sum] < best) {
            best_sum = Some(sum);
            best_cost = Some(costs[sum]);
        }
    }
    Ok(MinCostPass {
        best_sum,
        best_cost,
        choices,
    })
}

fn traceback_choices(
    items: &[Item],
    mut sum: usize,
    states: usize,
    choices: &BitSet,
) -> Result<Vec<bool>, SingleRowDpDecline> {
    let mut selected = vec![false; items.len()];
    for index in (0..items.len()).rev() {
        let choice_index = index
            .checked_mul(states)
            .and_then(|base| base.checked_add(sum))
            .ok_or(SingleRowDpDecline::VerificationFailed)?;
        if choices.get(choice_index) {
            let weight = items[index].weight;
            if sum < weight {
                return Err(SingleRowDpDecline::VerificationFailed);
            }
            selected[index] = true;
            sum -= weight;
        }
    }
    if sum != 0 {
        return Err(SingleRowDpDecline::VerificationFailed);
    }
    Ok(selected)
}

fn bit_words(bits: usize) -> Result<usize, SingleRowDpDecline> {
    bits.checked_add(63)
        .map(|rounded| rounded / 64)
        .filter(|&words| words > 0)
        .ok_or(SingleRowDpDecline::MemoryLimit)
}

fn gcd_usize(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let remainder = a % b;
        a = b;
        b = remainder;
    }
    a
}

fn div_ceil_nonnegative(value: usize, divisor: usize) -> usize {
    value / divisor + usize::from(!value.is_multiple_of(divisor))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{eval_objective_exact, verify_all_constraints, PbLit, PbTerm};

    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        }
    }

    fn negated_term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit { var, negated: true }],
        }
    }

    fn ge(terms: &[(i128, u32)], rhs: i128) -> PbConstraint {
        PbConstraint {
            terms: terms.iter().map(|&(c, v)| term(c, v)).collect(),
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn ranged_instance(
        weights: &[i128],
        lower: i128,
        upper: i128,
        objective: Option<&[i128]>,
    ) -> PbInstance {
        let positive: Vec<_> = weights
            .iter()
            .enumerate()
            .map(|(i, &weight)| (weight, (i + 1) as u32))
            .collect();
        let negative: Vec<_> = weights
            .iter()
            .enumerate()
            .map(|(i, &weight)| (-weight, (i + 1) as u32))
            .collect();
        let objective = objective.map(|coefficients| PbObjective {
            terms: coefficients
                .iter()
                .enumerate()
                .filter(|&(_, coefficient)| *coefficient != 0)
                .map(|(i, &coefficient)| term(coefficient, (i + 1) as u32))
                .collect(),
        });
        PbInstance {
            num_vars: weights.len() as u32,
            num_constraints: 2,
            constraints: vec![ge(&positive, lower), ge(&negative, -upper)],
            objective,
        }
    }

    fn brute_force(instance: &PbInstance) -> Option<(i128, Vec<bool>)> {
        assert!(instance.num_vars <= 20);
        let mut best: Option<(i128, Vec<bool>)> = None;
        for mask in 0u64..(1u64 << instance.num_vars) {
            let assignment: Vec<bool> = (0..instance.num_vars)
                .map(|bit| mask & (1u64 << bit) != 0)
                .collect();
            if !verify_all_constraints(&instance.constraints, &assignment) {
                continue;
            }
            let value = instance
                .objective
                .as_ref()
                .map(|objective| eval_objective_exact(objective, &assignment).unwrap())
                .unwrap_or(0);
            if best.as_ref().is_none_or(|(old, _)| value < *old) {
                best = Some((value, assignment));
            }
        }
        best
    }

    #[test]
    fn bounded_interval_feasibility_and_aligned_objective() {
        let feasibility = ranged_instance(&[3, 5, 8, 11], 13, 14, None);
        let SingleRowDpOutcome::Feasible(point) =
            solve_single_row_binary_interruptible(&feasibility, || false).unwrap()
        else {
            panic!("expected feasible")
        };
        assert!(verify_all_constraints(&feasibility.constraints, &point));

        let optimization = ranged_instance(&[3, 5, 8, 11], 8, 16, Some(&[3, 5, 8, 11]));
        let SingleRowDpOutcome::Optimal { assignment, value } =
            solve_single_row_binary_interruptible(&optimization, || false).unwrap()
        else {
            panic!("expected optimum")
        };
        assert_eq!(value, 8);
        assert!(verify_all_constraints(
            &optimization.constraints,
            &assignment
        ));
    }

    #[test]
    fn arbitrary_objective_uses_exact_min_cost_dp() {
        let instance = ranged_instance(&[2, 3, 5, 7], 7, 10, Some(&[8, -4, 3, 6]));
        let brute = brute_force(&instance).unwrap();
        let SingleRowDpOutcome::Optimal { assignment, value } =
            solve_single_row_binary_interruptible(&instance, || false).unwrap()
        else {
            panic!("expected optimum")
        };
        assert_eq!(value, brute.0);
        assert!(verify_all_constraints(&instance.constraints, &assignment));
        assert_eq!(
            eval_objective_exact(instance.objective.as_ref().unwrap(), &assignment).unwrap(),
            value
        );
    }

    #[test]
    fn signed_complemented_row_and_nonzero_objective_constant_match_enumeration() {
        // -2*x1 + 3*x2 + 5*x3 in [4,5].  Signed-row normalization flips x1,
        // and the near-total interval then triggers the whole-item complement.
        // The objective is deliberately non-proportional, contains negated
        // literals (hence a nonzero normalization constant), and mentions x4,
        // which is independent of the row.
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 2,
            constraints: vec![
                ge(&[(-2, 1), (3, 2), (5, 3)], 4),
                ge(&[(2, 1), (-3, 2), (-5, 3)], -5),
            ],
            objective: Some(PbObjective {
                terms: vec![
                    negated_term(7, 1),
                    term(-4, 2),
                    term(2, 3),
                    negated_term(-9, 4),
                ],
            }),
        };
        let expected = brute_force(&instance).expect("fixture is feasible");
        let actual = solve_single_row_binary_interruptible(&instance, || false)
            .expect("exact single-row route");
        let SingleRowDpOutcome::Optimal { assignment, value } = actual else {
            panic!("expected optimum")
        };
        assert_eq!(value, expected.0);
        assert!(verify_all_constraints(&instance.constraints, &assignment));
        assert_eq!(
            eval_objective_exact(instance.objective.as_ref().unwrap(), &assignment).unwrap(),
            value
        );
    }

    #[test]
    fn p2m2p1m1p0n100_shape_is_proved_infeasible() {
        // Exact coefficient/interval shape of the one-row MIPLIB instance.
        // The implementation sees only a generic ranged Boolean row.
        let weights = [
            6567, 6563, 14353, 11135, 6562, 9785, 8174, 6563, 12741, 8176, 12740, 11136, 12744,
            8176, 9783, 12742, 11135, 12745, 14352, 9782, 6565, 11136, 6563, 12743, 14350, 11134,
            8176, 12740, 6563, 9782, 12743, 14352, 12741, 6566, 12743, 6564, 9785, 9782, 12741,
            9782, 14350, 11133, 6562, 11135, 8176, 9781, 6562, 11135, 8175, 12745, 11133, 6566,
            11135, 11132, 12743, 12743, 14349, 9784, 12740, 9783, 8174, 9785, 6567, 8176, 8175,
            8174, 8174, 6564, 11135, 6564, 9781, 6565, 12740, 14353, 8176, 11132, 14350, 8172,
            14353, 8175, 8171, 14353, 9783, 8175, 6567, 8173, 9783, 6564, 9781, 12742, 14353,
            11133, 9783, 11132, 12743, 12743, 12740, 9782, 9782, 14354,
        ];
        let instance = ranged_instance(&weights, 80424, 80425, Some(&weights));
        assert_eq!(
            solve_single_row_binary_interruptible(&instance, || false).unwrap(),
            SingleRowDpOutcome::Infeasible
        );
        assert!(
            generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || false)
                .expect("bounded checkpoint proof")
                .is_some()
        );
    }

    #[test]
    fn exhaustive_differential_against_enumeration() {
        // Deterministic small corpus covering signed weights, negative and
        // unrelated objectives, empty intervals, and both DP implementations.
        let mut state = 0x4d59_5df4_d0f3_3173u64;
        for n in 1..=8usize {
            for _case in 0..96 {
                let mut next = || {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    state
                };
                let weights: Vec<i128> = (0..n).map(|_| (next() % 15) as i128 - 7).collect();
                if weights.iter().all(|&weight| weight == 0) {
                    continue;
                }
                let objective: Vec<i128> = (0..n).map(|_| (next() % 17) as i128 - 8).collect();
                let low = (next() % 31) as i128 - 15;
                let high = low + (next() % 13) as i128;
                let instance = ranged_instance(&weights, low, high, Some(&objective));
                let expected = brute_force(&instance);
                let actual = solve_single_row_binary_interruptible(&instance, || false).unwrap();
                match (expected, actual) {
                    (None, SingleRowDpOutcome::Infeasible) => {}
                    (Some((best, _)), SingleRowDpOutcome::Optimal { assignment, value }) => {
                        assert_eq!(value, best, "n={n} weights={weights:?}");
                        assert!(verify_all_constraints(&instance.constraints, &assignment));
                    }
                    (expected, actual) => panic!(
                        "differential mismatch: n={n} weights={weights:?} \
                         objective={objective:?} interval=[{low},{high}] \
                         expected={expected:?} actual={actual:?}"
                    ),
                }
            }
        }
    }

    #[test]
    fn infeasibility_certificate_round_trips_and_replays_checkpoints() {
        // Ten items force an interior checkpoint at item eight.  All weights
        // exceed the nonempty target interval [1,1], so only sum zero remains.
        let weights = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let objective = [7, -3, 2, 0, 1, 9, -4, 6, 5, -2];
        let instance = ranged_instance(&weights, 1, 1, Some(&objective));
        let certificate =
            generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || false)
                .expect("certificate generation")
                .expect("instance is infeasible");
        let SingleRowDpInfeasibilityProof::Reachability {
            checkpoint_interval,
            checkpoints,
        } = &certificate.proof
        else {
            panic!("expected reachability proof")
        };
        assert_eq!(*checkpoint_interval as usize, CHECKPOINT_INTERVAL);
        assert_eq!(
            checkpoints
                .iter()
                .map(|checkpoint| checkpoint.items_processed)
                .collect::<Vec<_>>(),
            vec![0, 8, 10]
        );
        verify_single_row_dp_infeasibility_certificate_interruptible(
            &instance,
            &certificate,
            || false,
        )
        .expect("generated certificate must verify");

        let encoded = encode_single_row_dp_infeasibility_certificate_json(&certificate)
            .expect("bounded serialization");
        let decoded = decode_single_row_dp_infeasibility_certificate_json(&encoded)
            .expect("bounded deserialization");
        assert_eq!(decoded, certificate);
        verify_single_row_dp_infeasibility_certificate_interruptible(&instance, &decoded, || false)
            .expect("round-tripped certificate must verify");
    }

    #[test]
    fn certificate_corruption_and_instance_mismatch_fail_closed() {
        let instance = ranged_instance(
            &[2, 3, 4, 5, 6, 7, 8, 9, 10],
            1,
            1,
            Some(&[5, -2, 7, 1, 0, 3, -4, 9, 6]),
        );
        let certificate =
            generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || false)
                .unwrap()
                .unwrap();

        let mut corrupted_word = certificate.clone();
        let SingleRowDpInfeasibilityProof::Reachability { checkpoints, .. } =
            &mut corrupted_word.proof
        else {
            panic!("expected reachability proof")
        };
        checkpoints[1].reachable_words[0] ^= 1 << 1;
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_interruptible(
                &instance,
                &corrupted_word,
                || false
            ),
            Err(SingleRowDpDecline::VerificationFailed)
        );

        let mut wrong_checkpoint = certificate.clone();
        let SingleRowDpInfeasibilityProof::Reachability { checkpoints, .. } =
            &mut wrong_checkpoint.proof
        else {
            panic!("expected reachability proof")
        };
        checkpoints[1].items_processed -= 1;
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_interruptible(
                &instance,
                &wrong_checkpoint,
                || false
            ),
            Err(SingleRowDpDecline::VerificationFailed)
        );

        let mut wrong_row = instance.clone();
        wrong_row.constraints[0].terms[0].coeff += 1;
        wrong_row.constraints[1].terms[0].coeff -= 1;
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_interruptible(
                &wrong_row,
                &certificate,
                || false
            ),
            Err(SingleRowDpDecline::VerificationFailed)
        );

        let mut wrong_objective = instance.clone();
        wrong_objective.objective.as_mut().unwrap().terms[0].coeff += 1;
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_interruptible(
                &wrong_objective,
                &certificate,
                || false
            ),
            Err(SingleRowDpDecline::VerificationFailed)
        );

        let mut wrong_binding = certificate.clone();
        wrong_binding.canonical_problem.lower += 1;
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_interruptible(
                &instance,
                &wrong_binding,
                || false
            ),
            Err(SingleRowDpDecline::VerificationFailed)
        );

        let mut oversized = certificate.clone();
        let SingleRowDpInfeasibilityProof::Reachability { checkpoints, .. } = &mut oversized.proof
        else {
            panic!("expected reachability proof")
        };
        checkpoints[0].reachable_words.resize(1_000, 0);
        let small_memory = SingleRowDpLimits {
            memory_budget_bytes: 4_096,
            ..SingleRowDpLimits::default()
        };
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_with_limits(
                &instance,
                &oversized,
                small_memory,
                || false
            ),
            Err(SingleRowDpDecline::MemoryLimit)
        );
    }

    #[test]
    fn certificate_codec_rejects_truncation_and_oversized_artifacts() {
        let instance = ranged_instance(&[2, 3, 5], 1, 1, None);
        let certificate =
            generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || false)
                .unwrap()
                .unwrap();
        let encoded = encode_single_row_dp_infeasibility_certificate_json(&certificate).unwrap();
        assert!(matches!(
            decode_single_row_dp_infeasibility_certificate_json(
                &encoded[..encoded.len().saturating_sub(1)]
            ),
            Err(SingleRowDpCertificateCodecError::Malformed(_))
        ));

        let mut unknown_field: serde_json::Value =
            serde_json::from_slice(&encoded).expect("fixture JSON");
        unknown_field
            .as_object_mut()
            .expect("certificate object")
            .insert("untrusted_extra".into(), serde_json::Value::Bool(true));
        assert!(matches!(
            decode_single_row_dp_infeasibility_certificate_json(
                &serde_json::to_vec(&unknown_field).unwrap()
            ),
            Err(SingleRowDpCertificateCodecError::Malformed(_))
        ));

        let tiny = SingleRowDpLimits {
            memory_budget_bytes: u64::try_from(encoded.len()).unwrap() - 1,
            ..SingleRowDpLimits::default()
        };
        assert!(matches!(
            decode_single_row_dp_infeasibility_certificate_json_with_limits(&encoded, tiny),
            Err(SingleRowDpCertificateCodecError::Oversized { .. })
        ));
        assert!(matches!(
            encode_single_row_dp_infeasibility_certificate_json_with_limits(&certificate, tiny),
            Err(SingleRowDpCertificateCodecError::Oversized { .. })
        ));
    }

    #[test]
    fn empty_interval_certificate_and_cancellation_fail_closed() {
        let instance = ranged_instance(&[2, 4], 20, 21, Some(&[3, -1]));
        assert_eq!(
            generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || true),
            Err(SingleRowDpDecline::Interrupted)
        );
        let certificate =
            generate_single_row_dp_infeasibility_certificate_interruptible(&instance, || false)
                .unwrap()
                .unwrap();
        assert_eq!(
            certificate.proof,
            SingleRowDpInfeasibilityProof::EmptyInterval
        );
        verify_single_row_dp_infeasibility_certificate_interruptible(
            &instance,
            &certificate,
            || false,
        )
        .unwrap();
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_interruptible(
                &instance,
                &certificate,
                || true
            ),
            Err(SingleRowDpDecline::Interrupted)
        );

        let mut malformed = certificate.clone();
        malformed.proof = SingleRowDpInfeasibilityProof::Reachability {
            checkpoint_interval: CHECKPOINT_INTERVAL as u32,
            checkpoints: Vec::new(),
        };
        assert_eq!(
            verify_single_row_dp_infeasibility_certificate_interruptible(
                &instance,
                &malformed,
                || false
            ),
            Err(SingleRowDpDecline::VerificationFailed)
        );
    }

    #[test]
    fn infeasibility_certificate_differential_against_enumeration() {
        let mut state = 0xa076_1d64_78bd_642fu64;
        for n in 1..=8usize {
            for _case in 0..48 {
                let mut next = || {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    state
                };
                let weights: Vec<i128> = (0..n).map(|_| (next() % 13) as i128 - 6).collect();
                if weights.iter().all(|&weight| weight == 0) {
                    continue;
                }
                let objective: Vec<i128> = (0..n).map(|_| (next() % 15) as i128 - 7).collect();
                let lower = (next() % 27) as i128 - 13;
                let upper = lower + (next() % 9) as i128;
                let instance = ranged_instance(&weights, lower, upper, Some(&objective));
                let expected_infeasible = brute_force(&instance).is_none();
                let certificate = generate_single_row_dp_infeasibility_certificate_interruptible(
                    &instance,
                    || false,
                )
                .unwrap();
                assert_eq!(
                    certificate.is_some(),
                    expected_infeasible,
                    "weights={weights:?} interval=[{lower},{upper}]"
                );
                if let Some(certificate) = certificate {
                    verify_single_row_dp_infeasibility_certificate_interruptible(
                        &instance,
                        &certificate,
                        || false,
                    )
                    .unwrap();
                }
            }
        }
    }

    #[test]
    fn interruption_and_resource_limits_decline() {
        let instance = ranged_instance(&[3, 5, 7], 4, 11, Some(&[2, -1, 4]));
        assert_eq!(
            solve_single_row_binary_interruptible(&instance, || true),
            Err(SingleRowDpDecline::Interrupted)
        );

        let tiny = SingleRowDpLimits {
            max_states: 2,
            ..SingleRowDpLimits::default()
        };
        assert_eq!(
            solve_single_row_binary_with_limits(&instance, tiny, || false),
            Err(SingleRowDpDecline::ResourceLimit)
        );
    }

    #[test]
    fn malformed_or_multilinear_inputs_decline() {
        let mut instance = ranged_instance(&[2, 3], 2, 4, None);
        instance.constraints[0].terms[0].lits.push(PbLit {
            var: 2,
            negated: false,
        });
        assert_eq!(
            solve_single_row_binary_interruptible(&instance, || false),
            Err(SingleRowDpDecline::InvalidLinearTerm)
        );

        let mut two_rows = ranged_instance(&[2, 3], 2, 4, None);
        two_rows.constraints[1].terms[0].coeff += 1;
        assert_eq!(
            solve_single_row_binary_interruptible(&two_rows, || false),
            Err(SingleRowDpDecline::UnsupportedStructure)
        );
    }
}
