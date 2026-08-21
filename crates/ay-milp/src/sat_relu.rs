// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, fail-closed recognition of the `sat_relu` SAT-in-a-network gadget.
//!
//! This is deliberately a structural fast path, not a heuristic classifier. A
//! model is accepted only when every column, affine equation, ReLU big-M row,
//! output equation, and output bound has the canonical shape. When an
//! exact-rational side store exists, recognition reads it as authoritative;
//! the rounded `f64` matrix is never allowed to establish the match.
//!
//! The input boxes produced by neural-network bound propagation are padded
//! slightly outside `[0, 1]`. Soundness therefore cannot pretend that the MILP
//! inputs are Boolean. Let
//!
//! * `L = sum max(0, -lb_i)`, and
//! * `U = sum max(0, ub_i - 1)`.
//!
//! The second output says that the sum of each input's distance to `{0, 1}` is
//! at most the total upper overshoot. Rounding at `1/2` consequently changes
//! all clause affine forms by less than `L + 2U`. We require that quantity to
//! be strictly below one. A violated rounded clause has integer affine value
//! at least one, whereas the corresponding MILP ReLU/output rows force its
//! unrounded value to be non-positive, a contradiction. This also transports
//! the constraints implied by fixed ReLU phases (with the tie at zero handled
//! explicitly below).

use std::mem::size_of;
use std::time::Instant;

use ay_lra::rational::Rational;
use ay_sat::{
    solve_resolution_dag_with_limits, Literal, ResolutionDag, ResolutionProofLimits,
    ResolutionSolveOutcome, ResolutionValidationError, ResolutionValidationLimits, RupStep,
    Variable,
};
use num_rational::BigRational;
use num_traits::{One, Zero};
use sha2::{Digest as _, Sha256};

use crate::model::{exact_small, ColSpec, RowSpec};
use crate::sat_route::{
    deadline_reached, lift_and_check_assignment, solve_and_lift, CheckedSatPoint, SatDecision,
};
use crate::{ColKind, Model};

const MAX_FIXED_ACTIVE_PAIR_CLAUSES: usize = 1_000_000;
const MAX_PROOF_MEMORY_BYTES: usize = 256 * 1024 * 1024;
const MIN_PROOF_MEMORY_BYTES: usize = 16 * 1024 * 1024;
const MAX_PROOF_VARS: usize = 1_000_000;
const MAX_PROOF_CLAUSES: usize = 2_000_000;
const MAX_PROOF_LITERALS: usize = 8_000_000;
const MAX_PROOF_ITEMS_PER_CLAUSE: usize = 60_000;
const MAX_PROOF_STEPS: usize = 2_000_000;
const MAX_PROOF_HINTS: usize = 8_000_000;
const MAX_PROOF_REPLAY_WORK: u64 = 128_000_000;
const MAX_PLAN_AFFINES: usize = 2_000_000;
const MAX_PLAN_MODEL_COLS: usize = MAX_PROOF_VARS + 3 * MAX_PLAN_AFFINES + 2;
const MAX_PLAN_MODEL_ROWS: usize = 4 * MAX_PLAN_AFFINES + 4;
const MAX_PLAN_BYTES: usize = 128 * 1024 * 1024;
const MAX_CANONICAL_MODEL_BYTES: usize = 64 * 1024 * 1024;
const MAX_EXACT_SOURCE_BITS: u64 = 4 * 1024;
const MAX_EXACT_DERIVED_BITS: u64 = 8 * 1024;
const MAX_EXACT_SCRATCH_BYTES: usize = 4 * 1024 * 1024;
const EXACT_SCRATCH_LIVE_VALUES: usize = 64;
const F64_EXACT_PAYLOAD_CEILING: usize = 512;

#[cfg(test)]
std::thread_local! {
    static TEST_CDCL_INVOCATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TEST_BOUNDED_CDCL_INVOCATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static TEST_POST_SOLVE_DELAY: std::cell::Cell<std::time::Duration> =
        const { std::cell::Cell::new(std::time::Duration::ZERO) };
}

/// Compatibility name for the route's existing session/tests.
pub(crate) type SatReluDecision = SatDecision;

/// Conclusive result from the single proof-enabled SAT/ReLU CDCL pass.
pub(crate) enum SatReluProofDecision {
    /// Exact source-model point checked after lifting the SAT assignment.
    Sat(CheckedSatPoint),
    /// Bounded, independently replayed refutation bound to the source model.
    Unsat(SatReluInfeasibilityCertificate),
}

#[derive(Clone)]
struct Affine {
    /// Input-column coefficients; only small exact integers occur.
    terms: Vec<(usize, Rational)>,
    /// `z = terms * x - rhs`.
    rhs: Rational,
}

struct Gadget {
    n: usize,
    c: usize,
    k: usize,
    clauses: Vec<Vec<Literal>>,
    affine: Vec<Affine>,
    fixed_phases: Vec<Option<bool>>,
}

/// One exact recognition of a SAT/ReLU source model.
///
/// The complete CNF and lift data are retained so every evidence posture uses
/// one bounded proof-enabled SAT-or-refutation pass. If that bounded API
/// declines, only a caller without an explicit memory envelope may use the
/// identical plan for one ordinary-CDCL fallback.
pub(crate) struct SatReluPlan {
    gadget: Gadget,
    /// Conservative logical bytes retained by the completed plan, using the
    /// actual capacities returned by every fallible reservation.
    retained_bytes: usize,
    /// Peak route-owned logical bytes during recognition/completion, excluding
    /// allocator metadata/transients covered by the process RSS envelope.
    peak_bytes: usize,
    /// Bounded license for exact side-store clones, normalized arithmetic, and
    /// canonical formatting. It is not retained allocation, but it can coexist
    /// with the plan and proof/SAT-completion payload in later phases.
    exact_scratch_bytes: usize,
    /// Assignment plus exact reconstruction buffers live after ay-sat returns
    /// SAT and its solver/proof arena has been dropped.
    sat_completion_bytes: usize,
}

const SAT_RELU_CERTIFICATE_FORMAT: u32 = 1;

/// A DAG returned by ay-sat's bounded producer after its independent replay.
///
/// Keeping this wrapper private makes the model-bound certificate constructor
/// unavailable to arbitrary, merely well-shaped `ResolutionDag` values.
struct ValidatedSatReluDag(ResolutionDag);

/// Model-bound CDCL/RUP refutation of an exactly recognized SAT/ReLU model.
///
/// Original clauses are deliberately not retained: replay must reconstruct
/// them from the source model. The two digests bind the artifact to both that
/// exact model and the ordered CNF, while the derived RUP steps are the only
/// proof data that must cross the `.ayc` boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatReluInfeasibilityCertificate {
    format: u32,
    model_canon_sha256: [u8; 32],
    cnf_sha256: [u8; 32],
    num_vars: usize,
    num_original_clauses: usize,
    derived: Vec<RupStep>,
    empty_clause_id: u64,
}

impl SatReluInfeasibilityCertificate {
    fn from_validated_dag(
        model: &Model,
        plan: &SatReluPlan,
        validated: ValidatedSatReluDag,
        deadline: Option<Instant>,
    ) -> Result<Self, SatReluInfeasibilityVerificationError> {
        let ResolutionDag {
            num_vars,
            original_clauses,
            derived,
            empty_clause_id,
        } = validated.0;
        if num_vars != plan.num_vars() || original_clauses.len() != plan.clauses().len() {
            return Err(SatReluInfeasibilityVerificationError::ProjectionMismatch);
        }
        for (index, ((id, actual), expected)) in
            original_clauses.iter().zip(plan.clauses()).enumerate()
        {
            if *id != index as u64 + 1 || actual != expected {
                return Err(SatReluInfeasibilityVerificationError::ProjectionMismatch);
            }
        }
        // The source plan is now the authoritative original-clause copy. Drop
        // the API's identity-check copy before hashing the model/CNF so the two
        // full original databases are not retained across those scans.
        drop(original_clauses);
        let model_canon_sha256 = crate::cert_io::canonical_digest_bytes_bounded(
            model,
            deadline,
            MAX_CANONICAL_MODEL_BYTES,
        )
        .ok_or(SatReluInfeasibilityVerificationError::ResourceLimit)?;
        Ok(Self {
            format: SAT_RELU_CERTIFICATE_FORMAT,
            model_canon_sha256,
            cnf_sha256: cnf_digest(plan.num_vars(), plan.clauses(), deadline)
                .ok_or(SatReluInfeasibilityVerificationError::ResourceLimit)?,
            num_vars,
            num_original_clauses: plan.clauses().len(),
            derived,
            empty_clause_id,
        })
    }

    pub(crate) fn from_wire_parts(
        format: u32,
        model_canon_sha256: [u8; 32],
        cnf_sha256: [u8; 32],
        num_vars: usize,
        num_original_clauses: usize,
        derived: Vec<RupStep>,
        empty_clause_id: u64,
    ) -> Self {
        Self {
            format,
            model_canon_sha256,
            cnf_sha256,
            num_vars,
            num_original_clauses,
            derived,
            empty_clause_id,
        }
    }

    pub(crate) fn format(&self) -> u32 {
        self.format
    }

    pub(crate) fn model_canon_sha256(&self) -> &[u8; 32] {
        &self.model_canon_sha256
    }

    pub(crate) fn cnf_sha256(&self) -> &[u8; 32] {
        &self.cnf_sha256
    }

    pub(crate) fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub(crate) fn num_original_clauses(&self) -> usize {
        self.num_original_clauses
    }

    pub(crate) fn derived(&self) -> &[RupStep] {
        &self.derived
    }

    pub(crate) fn empty_clause_id(&self) -> u64 {
        self.empty_clause_id
    }
}

/// Why a SAT/ReLU resolution artifact did not replay against a source model.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SatReluInfeasibilityVerificationError {
    /// The artifact uses an unknown wire/replay format.
    #[error("unsupported SAT/ReLU certificate format {0}")]
    UnsupportedFormat(u32),
    /// The source no longer has the exact recognized layout.
    #[error("source model is not an exact SAT/ReLU model within the replay budget")]
    SourceNotRecognized,
    /// The artifact names a different canonical source model.
    #[error("SAT/ReLU certificate model digest differs from the source model")]
    ModelDigestMismatch,
    /// The artifact names a different variable/clause database.
    #[error("resolution artifact clause database differs from the exact source projection")]
    ProjectionMismatch,
    /// Replay exceeded its fixed deadline, byte, or allocation envelope.
    #[error("SAT/ReLU certificate replay exceeded its fixed resource envelope")]
    ResourceLimit,
    /// The RUP derivation is malformed or does not derive the empty clause.
    #[error("resolution DAG replay failed: {0}")]
    InvalidDag(String),
}

fn cnf_digest(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    deadline: Option<Instant>,
) -> Option<[u8; 32]> {
    let mut digest = Sha256::new();
    digest.update(b"ay-milp-sat-relu-cnf-v1\0");
    digest.update(u64::try_from(num_vars).ok()?.to_le_bytes());
    digest.update(u64::try_from(clauses.len()).ok()?.to_le_bytes());
    for (clause_index, clause) in clauses.iter().enumerate() {
        if clause_index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        digest.update(u64::try_from(clause.len()).ok()?.to_le_bytes());
        for (literal_index, literal) in clause.iter().enumerate() {
            if literal_index & 0x3ff == 0 && deadline_reached(deadline) {
                return None;
            }
            let variable = i32::try_from(literal.variable().index())
                .ok()?
                .checked_add(1)?;
            let dimacs = if literal.is_positive() {
                variable
            } else {
                -variable
            };
            digest.update(dimacs.to_le_bytes());
        }
    }
    if deadline_reached(deadline) {
        return None;
    }
    Some(digest.finalize().into())
}

impl SatReluPlan {
    pub(crate) fn num_vars(&self) -> usize {
        self.gadget.n
    }

    pub(crate) fn clauses(&self) -> &[Vec<Literal>] {
        &self.gadget.clauses
    }

    fn proof_memory_bytes(&self, caller_budget: Option<usize>) -> Option<usize> {
        caller_budget.map_or(Some(MAX_PROOF_MEMORY_BYTES), |total| {
            if total < self.peak_bytes {
                return None;
            }
            total
                .checked_sub(self.retained_bytes)?
                .checked_sub(self.exact_scratch_bytes)
        })
    }

    #[cfg(test)]
    fn retained_bytes(&self) -> usize {
        self.retained_bytes
    }

    #[cfg(test)]
    fn peak_bytes(&self) -> usize {
        self.peak_bytes
    }

    #[cfg(test)]
    fn exact_scratch_bytes(&self) -> usize {
        self.exact_scratch_bytes
    }

    /// Solve once, returning either a checked point or model-bound refutation.
    ///
    /// The producer has hard deadline/count/logical retained-output and replay
    /// work caps; route-owned buffers are preflighted and grown fallibly. Rust
    /// allocator transients and the whole SAT solver's process peak remain the
    /// caller's RSS-watchdog responsibility. Any timeout, unsupported proof
    /// step, or resource exhaustion is an ordinary decline.
    pub(crate) fn try_solve_with_proof(
        &self,
        model: &Model,
        deadline: Option<Instant>,
        memory_budget: Option<usize>,
    ) -> Option<SatReluProofDecision> {
        let started = Instant::now();
        if deadline_reached(deadline) {
            trace_proof_attempt(self, started, "DECLINE", "deadline-before-start");
            return None;
        }
        let Some(proof_memory_bytes) = self.proof_memory_bytes(memory_budget) else {
            trace_proof_attempt(self, started, "DECLINE", "memory-plan-retained");
            return None;
        };
        let Some(limits) = proof_limits(deadline, proof_memory_bytes) else {
            trace_proof_attempt(self, started, "DECLINE", "memory-preflight");
            return None;
        };
        #[cfg(test)]
        TEST_BOUNDED_CDCL_INVOCATIONS.with(|count| count.set(count.get() + 1));
        let solved =
            match solve_resolution_dag_with_limits(self.num_vars(), self.clauses(), &limits) {
                Ok(solved) => solved,
                Err(error) => {
                    if trace_enabled() {
                        eprintln!(
                            "--trace sat-relu-proof: vars={} clauses={} outcome=DECLINE \
                         reason={error} wall={:.6}s",
                            self.num_vars(),
                            self.clauses().len(),
                            started.elapsed().as_secs_f64(),
                        );
                    }
                    return None;
                }
            };
        match solved {
            ResolutionSolveOutcome::Sat(assignment) => {
                if proof_memory_bytes < self.sat_completion_bytes {
                    trace_proof_attempt(self, started, "DECLINE", "memory-sat-completion");
                    return None;
                }
                let Some(checked) =
                    lift_and_check_assignment(model, &assignment, deadline, |assignment| {
                        reconstruct(model, &self.gadget, assignment, deadline)
                    })
                else {
                    trace_proof_attempt(self, started, "DECLINE", "sat-lift-rejected");
                    return None;
                };
                trace_proof_attempt(self, started, "SAT", "checked-point");
                Some(SatReluProofDecision::Sat(checked))
            }
            ResolutionSolveOutcome::Unsat(dag) => {
                if deadline_reached(deadline) {
                    trace_proof_attempt(self, started, "DECLINE", "deadline-after-replay");
                    return None;
                }
                // The bounded ay-sat API has already replayed this exact DAG.
                // The private wrapper carries that fact to the model-binding
                // constructor; repeating RUP replay would double proof work.
                let Ok(certificate) = SatReluInfeasibilityCertificate::from_validated_dag(
                    model,
                    self,
                    ValidatedSatReluDag(dag),
                    deadline,
                ) else {
                    trace_proof_attempt(self, started, "DECLINE", "model-binding-rejected");
                    return None;
                };
                if deadline_reached(deadline) {
                    trace_proof_attempt(self, started, "DECLINE", "deadline-after-binding");
                    return None;
                }
                trace_proof_attempt(self, started, "UNSAT", "checked-rup");
                Some(SatReluProofDecision::Unsat(certificate))
            }
        }
    }

    /// Solve the retained exact CNF and lift a SAT assignment once.
    pub(crate) fn solve(
        &self,
        model: &Model,
        deadline: Option<Instant>,
    ) -> Option<SatReluDecision> {
        let started = Instant::now();
        #[cfg(test)]
        TEST_CDCL_INVOCATIONS.with(|count| count.set(count.get() + 1));
        let decision = solve_and_lift(
            model,
            self.gadget.n,
            &self.gadget.clauses,
            deadline,
            |assignment| reconstruct(model, &self.gadget, assignment, deadline),
        );
        if deadline_reached(deadline) {
            return None;
        }
        if let Some(ref decision) = decision {
            if trace_enabled() {
                let verdict = match decision {
                    SatReluDecision::Sat(_) => "SAT",
                    SatReluDecision::Unsat => "UNSAT",
                };
                eprintln!(
                    "--trace sat-relu: vars={} clauses={} verdict={verdict} wall={:.6}s",
                    self.gadget.n,
                    self.gadget.clauses.len(),
                    started.elapsed().as_secs_f64(),
                );
            }
        }
        decision
    }
}

fn trace_proof_attempt(plan: &SatReluPlan, started: Instant, outcome: &str, reason: &str) {
    if trace_enabled() {
        eprintln!(
            "--trace sat-relu-proof: vars={} clauses={} outcome={outcome} reason={reason} \
             wall={:.6}s",
            plan.num_vars(),
            plan.clauses().len(),
            started.elapsed().as_secs_f64(),
        );
    }
}

pub(crate) fn trace_ordinary_fallback() {
    if trace_enabled() {
        eprintln!("--trace sat-relu-proof: fallback=ordinary-cdcl");
    }
}

fn validation_limits(deadline: Option<Instant>, max_bytes: usize) -> ResolutionValidationLimits {
    ResolutionValidationLimits {
        deadline,
        max_original_clauses: MAX_PROOF_CLAUSES,
        max_original_literals: MAX_PROOF_LITERALS,
        max_derived_steps: MAX_PROOF_STEPS,
        max_derived_literals: MAX_PROOF_LITERALS,
        max_hints: MAX_PROOF_HINTS,
        max_work: MAX_PROOF_REPLAY_WORK,
        max_bytes,
    }
}

fn proof_limits(
    deadline: Option<Instant>,
    proof_memory_bytes: usize,
) -> Option<ResolutionProofLimits> {
    let total = proof_memory_bytes.min(MAX_PROOF_MEMORY_BYTES);
    if total < MIN_PROOF_MEMORY_BYTES {
        return None;
    }
    let quarter = total / 4;
    let half = total / 2;
    let limits = ResolutionProofLimits {
        deadline,
        max_num_vars: MAX_PROOF_VARS,
        max_input_clauses: MAX_PROOF_CLAUSES,
        max_input_literals: MAX_PROOF_LITERALS,
        max_input_clause_literals: MAX_PROOF_ITEMS_PER_CLAUSE,
        max_input_bytes: quarter,
        max_conflicts: Some(5_000_000),
        max_decisions: Some(50_000_000),
        solver_clause_db_reduction_threshold_bytes: quarter,
        max_proof_output_bytes: quarter,
        max_derived_steps: MAX_PROOF_STEPS,
        max_derived_literals: MAX_PROOF_LITERALS,
        max_hints: MAX_PROOF_HINTS,
        max_pending_deletions: (quarter / size_of::<u64>()).min(MAX_PROOF_CLAUSES),
        max_codec_bytes: half,
        max_backward_reconstruction_bytes: quarter,
        validation: validation_limits(deadline, half),
    };
    // In the solve phase, one bounded input scratch buffer, the proof stream,
    // pending deletions, and backward-reconstruction state can coexist. In the
    // parse/replay phase, the codec footprint and validation footprint can
    // coexist. Keep both conservative phase sums inside the one allowance;
    // the SAT solver arena itself remains under the documented RSS envelope.
    let pending_deletion_bytes = limits.max_pending_deletions.checked_mul(size_of::<u64>())?;
    let solve_phase_bytes = limits
        .max_input_bytes
        .checked_add(limits.max_proof_output_bytes)?
        .checked_add(pending_deletion_bytes)?
        .checked_add(limits.max_backward_reconstruction_bytes)?;
    let parse_replay_phase_bytes = limits
        .max_codec_bytes
        .checked_add(limits.validation.max_bytes)?;
    if solve_phase_bytes > total || parse_replay_phase_bytes > total {
        return None;
    }
    Some(limits)
}

fn replay_payload_within_limits(
    plan: &SatReluPlan,
    certificate: &SatReluInfeasibilityCertificate,
    limits: &ResolutionValidationLimits,
    deadline: Option<Instant>,
) -> Option<()> {
    if plan.clauses().len() > limits.max_original_clauses
        || certificate.derived().len() > limits.max_derived_steps
    {
        return None;
    }
    let mut original_literals = 0usize;
    for (index, clause) in plan.clauses().iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        if clause.len() > MAX_PROOF_ITEMS_PER_CLAUSE {
            return None;
        }
        original_literals = original_literals.checked_add(clause.len())?;
        if original_literals > limits.max_original_literals {
            return None;
        }
    }
    let mut derived_literals = 0usize;
    let mut hints = 0usize;
    for (index, step) in certificate.derived().iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        if step.clause.len() > MAX_PROOF_ITEMS_PER_CLAUSE
            || step.rup_hints.len() > MAX_PROOF_ITEMS_PER_CLAUSE
        {
            return None;
        }
        derived_literals = derived_literals.checked_add(step.clause.len())?;
        hints = hints.checked_add(step.rup_hints.len())?;
        if derived_literals > limits.max_derived_literals || hints > limits.max_hints {
            return None;
        }
    }

    let bytes = size_of::<ResolutionDag>()
        .checked_add(
            plan.clauses()
                .len()
                .checked_mul(size_of::<(u64, Vec<Literal>)>())?,
        )?
        .checked_add(original_literals.checked_mul(size_of::<Literal>())?)?
        .checked_add(
            certificate
                .derived()
                .len()
                .checked_mul(size_of::<RupStep>())?,
        )?
        .checked_add(derived_literals.checked_mul(size_of::<Literal>())?)?
        .checked_add(hints.checked_mul(size_of::<u64>())?)?;
    if bytes > limits.max_bytes || deadline_reached(deadline) {
        return None;
    }
    Some(())
}

fn replay_source_retained_bytes(
    plan: &SatReluPlan,
    certificate: &SatReluInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> Option<usize> {
    if deadline_reached(deadline) {
        return None;
    }
    // `plan.retained_bytes` was measured from every completed Vec's actual
    // capacity during recognition. The wire parser can likewise leave spare
    // geometric capacity in both the outer step Vec and its nested payloads;
    // all of it remains live while the independently materialized DAG exists.
    let mut retained = plan
        .retained_bytes
        .checked_add(plan.exact_scratch_bytes)?
        .checked_add(size_of::<SatReluInfeasibilityCertificate>())?
        .checked_add(
            certificate
                .derived
                .capacity()
                .checked_mul(size_of::<RupStep>())?,
        )?;
    for (index, step) in certificate.derived().iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        retained = retained
            .checked_add(step.clause.capacity().checked_mul(size_of::<Literal>())?)?
            .checked_add(step.rup_hints.capacity().checked_mul(size_of::<u64>())?)?;
    }
    (!deadline_reached(deadline)).then_some(retained)
}

fn replay_limits_after_retained_source(
    plan: &SatReluPlan,
    certificate: &SatReluInfeasibilityCertificate,
    deadline: Option<Instant>,
    total_budget: usize,
) -> Option<ResolutionValidationLimits> {
    let retained = replay_source_retained_bytes(plan, certificate, deadline)?;
    Some(validation_limits(
        deadline,
        total_budget.checked_sub(retained)?,
    ))
}

fn clone_literals_bounded(literals: &[Literal]) -> Option<Vec<Literal>> {
    let mut cloned = Vec::new();
    cloned.try_reserve_exact(literals.len()).ok()?;
    cloned.extend_from_slice(literals);
    Some(cloned)
}

fn clone_hints_bounded(hints: &[u64]) -> Option<Vec<u64>> {
    let mut cloned = Vec::new();
    cloned.try_reserve_exact(hints.len()).ok()?;
    cloned.extend_from_slice(hints);
    Some(cloned)
}

fn materialize_replay_dag(
    plan: &SatReluPlan,
    certificate: &SatReluInfeasibilityCertificate,
    limits: &ResolutionValidationLimits,
    deadline: Option<Instant>,
) -> Option<ResolutionDag> {
    replay_payload_within_limits(plan, certificate, limits, deadline)?;

    let mut original_clauses = Vec::new();
    original_clauses
        .try_reserve_exact(plan.clauses().len())
        .ok()?;
    for (index, clause) in plan.clauses().iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        original_clauses.push((
            u64::try_from(index).ok()?.checked_add(1)?,
            clone_literals_bounded(clause)?,
        ));
    }

    let mut derived = Vec::new();
    derived
        .try_reserve_exact(certificate.derived().len())
        .ok()?;
    for (index, step) in certificate.derived().iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        derived.push(RupStep {
            id: step.id,
            clause: clone_literals_bounded(&step.clause)?,
            rup_hints: clone_hints_bounded(&step.rup_hints)?,
        });
    }
    if deadline_reached(deadline) {
        return None;
    }
    Some(ResolutionDag {
        num_vars: plan.num_vars(),
        original_clauses,
        derived,
        empty_clause_id: certificate.empty_clause_id(),
    })
}

/// Rebuild the exact SAT/ReLU CNF and independently replay a resolution DAG.
///
/// Source reconstruction, clause comparison, and independent DAG replay use
/// explicit finite count/logical-byte/work caps and the caller's absolute
/// deadline. Whole-process peak memory remains an external RSS-cap concern.
pub fn verify_infeasibility_certificate(
    model: &Model,
    certificate: &SatReluInfeasibilityCertificate,
    deadline: Option<Instant>,
) -> Result<(), SatReluInfeasibilityVerificationError> {
    if certificate.format() != SAT_RELU_CERTIFICATE_FORMAT {
        return Err(SatReluInfeasibilityVerificationError::UnsupportedFormat(
            certificate.format(),
        ));
    }
    if deadline_reached(deadline) {
        return Err(SatReluInfeasibilityVerificationError::ResourceLimit);
    }
    let plan = match prepare(model, deadline) {
        Some(plan) => plan,
        None if deadline_reached(deadline) => {
            return Err(SatReluInfeasibilityVerificationError::ResourceLimit)
        }
        None => return Err(SatReluInfeasibilityVerificationError::SourceNotRecognized),
    };
    if deadline_reached(deadline) {
        return Err(SatReluInfeasibilityVerificationError::ResourceLimit);
    }
    let model_digest =
        crate::cert_io::canonical_digest_bytes_bounded(model, deadline, MAX_CANONICAL_MODEL_BYTES)
            .ok_or(SatReluInfeasibilityVerificationError::ResourceLimit)?;
    if certificate.model_canon_sha256() != &model_digest {
        return Err(SatReluInfeasibilityVerificationError::ModelDigestMismatch);
    }
    if deadline_reached(deadline) {
        return Err(SatReluInfeasibilityVerificationError::ResourceLimit);
    }
    let projected_digest = cnf_digest(plan.num_vars(), plan.clauses(), deadline)
        .ok_or(SatReluInfeasibilityVerificationError::ResourceLimit)?;
    if certificate.num_vars() != plan.num_vars()
        || certificate.num_original_clauses() != plan.clauses().len()
        || certificate.cnf_sha256() != &projected_digest
    {
        return Err(SatReluInfeasibilityVerificationError::ProjectionMismatch);
    }
    if deadline_reached(deadline) {
        return Err(SatReluInfeasibilityVerificationError::ResourceLimit);
    }
    // The rebuilt projection and parsed wire certificate remain live while the
    // replay DAG is cloned and validated. Subtract both retained source
    // objects first, then give the remainder to `validate_with_limits`, whose
    // own byte meter covers the materialized DAG plus conservative replay
    // scratch. This makes 128 MiB one concurrent logical envelope instead of
    // three independent 128 MiB claims. Allocator transients and the caller's
    // source `Model` remain the external RSS cap's responsibility.
    let replay_budget = MAX_PROOF_MEMORY_BYTES / 2;
    let limits = replay_limits_after_retained_source(&plan, certificate, deadline, replay_budget)
        .ok_or(SatReluInfeasibilityVerificationError::ResourceLimit)?;
    let dag = materialize_replay_dag(&plan, certificate, &limits, deadline)
        .ok_or(SatReluInfeasibilityVerificationError::ResourceLimit)?;
    match dag.validate_with_limits(&limits) {
        Ok(()) => {}
        Err(ResolutionValidationError::Invalid(error)) => {
            return Err(SatReluInfeasibilityVerificationError::InvalidDag(
                error.to_string(),
            ));
        }
        Err(
            ResolutionValidationError::LimitExceeded { .. }
            | ResolutionValidationError::DeadlineExceeded
            | ResolutionValidationError::Cancelled
            | ResolutionValidationError::AccountingOverflow { .. }
            | ResolutionValidationError::AllocationFailed { .. },
        ) => return Err(SatReluInfeasibilityVerificationError::ResourceLimit),
    }
    if deadline_reached(deadline) {
        return Err(SatReluInfeasibilityVerificationError::ResourceLimit);
    }
    Ok(())
}

/// Legacy verdict-only SAT/ReLU helper, declining every unrecognized model.
///
/// `Unsat` relies on the SAT solver's checked search result but does not carry
/// a model-level artifact. Certificate-requiring callers use [`prepare`] plus
/// [`SatReluPlan::try_solve_with_proof`] instead. A SAT result crosses either
/// boundary only after reconstruction and an exact check against `model`.
#[cfg(test)]
pub(crate) fn try_solve(model: &Model, deadline: Option<Instant>) -> Option<SatReluDecision> {
    prepare(model, deadline)?.solve(model, deadline)
}

/// Rebuild under the route's fixed internal plan cap (legacy/verifier posture).
pub(crate) fn prepare(model: &Model, deadline: Option<Instant>) -> Option<SatReluPlan> {
    prepare_with_memory_budget(model, deadline, None)
}

/// Rebuild the complete exact SAT/ReLU plan once, declining fail-closed.
///
/// An explicit caller budget is the total route-owned logical envelope. Reserve
/// the bounded producer's minimum before recognition, then enforce the smaller
/// remainder and the fixed plan cap before every bulk allocation. With no
/// caller budget, recognition and proof retain their independent documented
/// static caps; whole-process allocator transients remain RSS-watchdog scope.
pub(crate) fn prepare_with_memory_budget(
    model: &Model,
    deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Option<SatReluPlan> {
    if deadline_reached(deadline) {
        return None;
    }
    let plan_budget = memory_budget.map_or(Some(MAX_PLAN_BYTES), |total| {
        total
            .checked_sub(MIN_PROOF_MEMORY_BYTES)
            .map(|bytes| bytes.min(MAX_PLAN_BYTES))
    })?;
    let (mut gadget, mut peak_bytes, exact_scratch_bytes) = detect(model, deadline, plan_budget)?;
    append_fixed_phase_clauses(&mut gadget, deadline, plan_budget, &mut peak_bytes)?;
    if deadline_reached(deadline) {
        return None;
    }
    let retained_bytes = retained_plan_bytes(&gadget)?;
    let sat_completion_bytes = sat_completion_bytes(model.num_cols(), gadget.n)?;
    admit_peak(
        &mut peak_bytes,
        retained_bytes
            .checked_add(exact_scratch_bytes)?
            .checked_add(sat_completion_bytes)?,
        plan_budget,
    )?;
    Some(SatReluPlan {
        gadget,
        retained_bytes,
        peak_bytes,
        exact_scratch_bytes,
        sat_completion_bytes,
    })
}

fn projected_retained_plan_bytes(
    k: usize,
    clause_count: usize,
    clause_literals: usize,
    affine_terms: usize,
) -> Option<usize> {
    size_of::<SatReluPlan>()
        .checked_add(clause_count.checked_mul(size_of::<Vec<Literal>>())?)?
        .checked_add(clause_literals.checked_mul(size_of::<Literal>())?)?
        .checked_add(k.checked_mul(size_of::<Affine>())?)?
        .checked_add(affine_terms.checked_mul(size_of::<(usize, Rational)>())?)?
        .checked_add(k.checked_mul(size_of::<Option<bool>>())?)
}

fn sat_completion_bytes(model_cols: usize, n: usize) -> Option<usize> {
    // Reconstruct first in AY's inline rational representation, then retain the
    // exact boundary vector concurrently. The returned Boolean assignment also
    // remains live until lifting completes.
    model_cols
        .checked_mul(size_of::<Rational>())?
        .checked_add(model_cols.checked_mul(size_of::<BigRational>())?)?
        .checked_add(n)
}

fn recognition_output_scratch_bytes(n: usize, c: usize) -> Option<usize> {
    c.checked_add(1)?
        .max(n.checked_mul(2)?.checked_add(1)?)
        .checked_mul(size_of::<(usize, f64)>())
}

fn projected_plan_peak_bytes(
    model_cols: usize,
    n: usize,
    c: usize,
    k: usize,
    clause_count: usize,
    clause_literals: usize,
    max_clause_literals: usize,
    affine_terms: usize,
) -> Option<usize> {
    let retained = projected_retained_plan_bytes(k, clause_count, clause_literals, affine_terms)?;
    let scratch = sat_completion_bytes(model_cols, n)?
        .max(recognition_output_scratch_bytes(n, c)?)
        .max(max_clause_literals.checked_mul(size_of::<Literal>())?);
    retained.checked_add(scratch)
}

fn plan_shape_within_limits(
    model_cols: usize,
    n: usize,
    c: usize,
    k: usize,
    clause_count: usize,
    clause_literals: usize,
    max_clause_literals: usize,
    affine_terms: usize,
    max_plan_bytes: usize,
) -> bool {
    model_cols <= MAX_PLAN_MODEL_COLS
        && n <= MAX_PROOF_VARS
        && k <= MAX_PLAN_AFFINES
        && clause_count <= MAX_PROOF_CLAUSES
        && clause_literals <= MAX_PROOF_LITERALS
        && max_clause_literals <= MAX_PROOF_ITEMS_PER_CLAUSE
        && projected_plan_peak_bytes(
            model_cols,
            n,
            c,
            k,
            clause_count,
            clause_literals,
            max_clause_literals,
            affine_terms,
        )
        .is_some_and(|bytes| bytes <= max_plan_bytes.min(MAX_PLAN_BYTES))
}

fn retained_plan_bytes(gadget: &Gadget) -> Option<usize> {
    let clause_literals = gadget.clauses.iter().try_fold(0usize, |bytes, clause| {
        bytes.checked_add(clause.capacity().checked_mul(size_of::<Literal>())?)
    })?;
    let affine_terms = gadget.affine.iter().try_fold(0usize, |bytes, affine| {
        bytes.checked_add(
            affine
                .terms
                .capacity()
                .checked_mul(size_of::<(usize, Rational)>())?,
        )
    })?;
    size_of::<SatReluPlan>()
        .checked_add(
            gadget
                .clauses
                .capacity()
                .checked_mul(size_of::<Vec<Literal>>())?,
        )?
        .checked_add(clause_literals)?
        .checked_add(gadget.affine.capacity().checked_mul(size_of::<Affine>())?)?
        .checked_add(affine_terms)?
        .checked_add(
            gadget
                .fixed_phases
                .capacity()
                .checked_mul(size_of::<Option<bool>>())?,
        )
}

fn admit_peak(peak: &mut usize, bytes: usize, budget: usize) -> Option<()> {
    if bytes > budget.min(MAX_PLAN_BYTES) {
        return None;
    }
    *peak = (*peak).max(bytes);
    Some(())
}

fn admit_peak_with_scratch(
    peak: &mut usize,
    retained_or_scratch: usize,
    exact_scratch_bytes: usize,
    budget: usize,
) -> Option<()> {
    admit_peak(
        peak,
        retained_or_scratch.checked_add(exact_scratch_bytes)?,
        budget,
    )
}

/// Constant-time rejection of models that cannot have the SAT/ReLU layout.
///
/// This route runs before other exact engines in every evidence posture, so a
/// generic MILP must not pay the later whole-model objective/column scans just
/// to learn that its outer shape is wrong. Every accepted gadget has at least one input
/// and one clause, hence at least 12 columns and 16 rows, a finite continuous
/// input first, and two free continuous network outputs last.
fn cheap_shape_gate(model: &Model) -> bool {
    let cols = &model.cols;
    if cols.len() < 12
        || cols.len() > MAX_PLAN_MODEL_COLS
        || model.rows.len() < 16
        || model.rows.len() > MAX_PLAN_MODEL_ROWS
        || !(model.rows.len() - 4).is_multiple_of(4)
    {
        return false;
    }
    let Some(first) = cols.first() else {
        return false;
    };
    first.kind == ColKind::Continuous
        && first.lb.is_finite()
        && first.ub.is_finite()
        && cols[cols.len() - 2..].iter().all(is_free_continuous)
}

#[cfg(test)]
fn reset_test_cdcl_invocations() {
    TEST_CDCL_INVOCATIONS.with(|count| count.set(0));
    TEST_BOUNDED_CDCL_INVOCATIONS.with(|count| count.set(0));
}

#[cfg(test)]
fn test_cdcl_invocations() -> usize {
    TEST_CDCL_INVOCATIONS.with(std::cell::Cell::get)
}

#[cfg(test)]
fn test_bounded_cdcl_invocations() -> usize {
    TEST_BOUNDED_CDCL_INVOCATIONS.with(std::cell::Cell::get)
}

#[cfg(test)]
fn set_test_post_solve_delay(delay: std::time::Duration) {
    TEST_POST_SOLVE_DELAY.with(|configured| configured.set(delay));
}

#[cfg(test)]
pub(crate) fn test_wait_before_session_finish() {
    TEST_POST_SOLVE_DELAY.with(|configured| {
        let delay = configured.replace(std::time::Duration::ZERO);
        if !delay.is_zero() {
            std::thread::sleep(delay);
        }
    });
}

/// Materialize every clause implied by fixed ReLU phases into the route plan.
/// Keeping the complete CNF as data lets all exact routes share one SAT boundary
/// and prepares this recognizer for model-bound proof coverage later.
fn append_fixed_phase_clauses(
    gadget: &mut Gadget,
    deadline: Option<Instant>,
    plan_budget: usize,
    peak_bytes: &mut usize,
) -> Option<()> {
    // A fixed phase transports to the rounded Boolean assignment as follows.
    // Clause-active plus output0=1 makes that clause affine exactly zero, so
    // precisely one of its literals is true. An inactive identity fixes x=0.
    // The 2x-1 ReLU phase fixes x on the corresponding side of 1/2.
    let mut pair_clauses = 0usize;
    let mut additional_clauses = 0usize;
    let mut additional_literals = 0usize;
    for (i, fixed) in gadget.fixed_phases.iter().copied().enumerate() {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let Some(active) = fixed else { continue };
        if i < gadget.c {
            if active {
                let clause_len = gadget.clauses.get(i)?.len();
                let pairs = clause_len.checked_mul(clause_len.saturating_sub(1))? / 2;
                pair_clauses = pair_clauses.checked_add(pairs)?;
                if pair_clauses > MAX_FIXED_ACTIVE_PAIR_CLAUSES {
                    return None;
                }
                additional_clauses = additional_clauses.checked_add(pairs)?;
                additional_literals = additional_literals.checked_add(pairs.checked_mul(2)?)?;
            }
        } else if i < gadget.c + gadget.n {
            if !active {
                additional_clauses = additional_clauses.checked_add(1)?;
                additional_literals = additional_literals.checked_add(1)?;
            }
        } else {
            additional_clauses = additional_clauses.checked_add(1)?;
            additional_literals = additional_literals.checked_add(1)?;
        }
    }

    let existing_literals = gadget
        .clauses
        .iter()
        .try_fold(0usize, |count, clause| count.checked_add(clause.len()))?;
    let affine_terms = gadget.affine.iter().try_fold(0usize, |count, affine| {
        count.checked_add(affine.terms.len())
    })?;
    let final_clause_count = gadget.clauses.len().checked_add(additional_clauses)?;
    let final_clause_literals = existing_literals.checked_add(additional_literals)?;
    let max_clause_literals = gadget
        .clauses
        .iter()
        .map(Vec::len)
        .max()
        .unwrap_or(0)
        .max(2);
    let model_cols = gadget
        .n
        .checked_add(gadget.k.checked_mul(3)?)?
        .checked_add(2)?;
    if !plan_shape_within_limits(
        model_cols,
        gadget.n,
        gadget.c,
        gadget.k,
        final_clause_count,
        final_clause_literals,
        max_clause_literals,
        affine_terms,
        plan_budget,
    ) || deadline_reached(deadline)
    {
        return None;
    }
    gadget.clauses.try_reserve_exact(additional_clauses).ok()?;
    let mut retained_bytes = retained_plan_bytes(gadget)?;
    admit_peak(peak_bytes, retained_bytes, plan_budget)?;

    let mut emitted_pair_clauses = 0usize;
    for (i, fixed) in gadget.fixed_phases.iter().copied().enumerate() {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let Some(active) = fixed else { continue };
        if i < gadget.c {
            if active {
                let source = &gadget.clauses[i];
                let mut clause = Vec::new();
                clause.try_reserve_exact(source.len()).ok()?;
                let clone_bytes = clause.capacity().checked_mul(size_of::<Literal>())?;
                admit_peak(
                    peak_bytes,
                    retained_bytes.checked_add(clone_bytes)?,
                    plan_budget,
                )?;
                clause.extend_from_slice(source);
                for left in 0..clause.len() {
                    for right in (left + 1)..clause.len() {
                        if emitted_pair_clauses & 0x3ff == 0 && deadline_reached(deadline) {
                            return None;
                        }
                        let mut pair = Vec::new();
                        pair.try_reserve_exact(2).ok()?;
                        let pair_bytes = pair.capacity().checked_mul(size_of::<Literal>())?;
                        admit_peak(
                            peak_bytes,
                            retained_bytes
                                .checked_add(clone_bytes)?
                                .checked_add(pair_bytes)?,
                            plan_budget,
                        )?;
                        pair.push(clause[left].negated());
                        pair.push(clause[right].negated());
                        gadget.clauses.push(pair);
                        retained_bytes = retained_bytes.checked_add(pair_bytes)?;
                        emitted_pair_clauses += 1;
                    }
                }
            }
        } else if i < gadget.c + gadget.n {
            if !active {
                let var = Variable::new(u32::try_from(i - gadget.c).ok()?);
                let mut unit = Vec::new();
                unit.try_reserve_exact(1).ok()?;
                let unit_bytes = unit.capacity().checked_mul(size_of::<Literal>())?;
                admit_peak(
                    peak_bytes,
                    retained_bytes.checked_add(unit_bytes)?,
                    plan_budget,
                )?;
                unit.push(Literal::negative(var));
                gadget.clauses.push(unit);
                retained_bytes = retained_bytes.checked_add(unit_bytes)?;
            }
        } else {
            let var = Variable::new(u32::try_from(i - gadget.c - gadget.n).ok()?);
            let lit = if active {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            };
            let mut unit = Vec::new();
            unit.try_reserve_exact(1).ok()?;
            let unit_bytes = unit.capacity().checked_mul(size_of::<Literal>())?;
            admit_peak(
                peak_bytes,
                retained_bytes.checked_add(unit_bytes)?,
                plan_budget,
            )?;
            unit.push(lit);
            gadget.clauses.push(unit);
            retained_bytes = retained_bytes.checked_add(unit_bytes)?;
        }
    }
    if emitted_pair_clauses != pair_clauses || deadline_reached(deadline) {
        return None;
    }
    let actual_retained = retained_plan_bytes(gadget)?;
    if actual_retained != retained_bytes {
        return None;
    }
    admit_peak(peak_bytes, actual_retained, plan_budget)?;
    Some(())
}

fn bigint_payload_bytes(value: &num_bigint::BigInt) -> Option<usize> {
    let bytes = usize::try_from(value.bits().checked_add(7)? / 8).ok()?;
    let word = size_of::<usize>();
    bytes
        .checked_add(word.checked_sub(1)?)?
        .checked_div(word)?
        .checked_mul(word)
}

fn exact_payload_bytes(value: &BigRational) -> Option<usize> {
    bigint_payload_bytes(value.numer())?.checked_add(bigint_payload_bytes(value.denom())?)
}

fn exact_source_scratch_bytes(model: &Model, deadline: Option<Instant>) -> Option<usize> {
    // Inspect borrowed side-store values before any exact accessor clones one.
    // A normalized row check has fewer than ten exact values live at once;
    // charging 64 payloads covers both those clones and the at-most-2x bit
    // growth of one multiply/divide.  Derived results are independently capped
    // by `bounded_rational`, so this fixed coexistence license cannot be
    // exceeded by a hostile numerator or denominator.
    let mut max_payload = F64_EXACT_PAYLOAD_CEILING;
    let mut inspected = 0usize;
    let mut inspect = |value: &BigRational| -> Option<()> {
        if inspected & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        inspected = inspected.checked_add(1)?;
        if value.numer().bits() > MAX_EXACT_SOURCE_BITS
            || value.denom().bits() > MAX_EXACT_SOURCE_BITS
        {
            return None;
        }
        max_payload = max_payload.max(exact_payload_bytes(value)?);
        Some(())
    };
    for value in model.exact_obj.values() {
        inspect(value)?;
    }
    if let Some(value) = &model.exact_obj_offset {
        inspect(value)?;
    }
    for row in model.exact_rows.values() {
        for value in row.coeffs.values() {
            inspect(value)?;
        }
        if let Some(value) = &row.lb {
            inspect(value)?;
        }
        if let Some(value) = &row.ub {
            inspect(value)?;
        }
    }
    if deadline_reached(deadline) {
        return None;
    }
    max_payload
        .checked_mul(EXACT_SCRATCH_LIVE_VALUES)?
        .checked_add(EXACT_SCRATCH_LIVE_VALUES.checked_mul(size_of::<Rational>())?)
        .filter(|bytes| *bytes <= MAX_EXACT_SCRATCH_BYTES)
}

fn bounded_rational(value: Rational) -> Option<Rational> {
    match &value {
        Rational::Small(_, _) => Some(value),
        Rational::Big(big)
            if big.numer().bits() <= MAX_EXACT_DERIVED_BITS
                && big.denom().bits() <= MAX_EXACT_DERIVED_BITS =>
        {
            Some(value)
        }
        Rational::Big(_) => None,
    }
}

fn detect(
    model: &Model,
    deadline: Option<Instant>,
    plan_budget: usize,
) -> Option<(Gadget, usize, usize)> {
    // The exact side store is authoritative.  Parsed MPS decimal coefficients
    // commonly need it, so rejecting the whole model here would reject the
    // production input format.  Every verdict-critical read below goes through
    // the exact accessors; proxy zero/sign classes are not semantic authority.
    // Objective offsets do not affect feasibility, but every genuine objective
    // coefficient must be zero.
    if !cheap_shape_gate(model) {
        return None;
    }
    let exact_scratch_bytes = exact_source_scratch_bytes(model, deadline)?;
    let recognition_budget = plan_budget.checked_sub(exact_scratch_bytes)?;
    let mut peak_bytes = exact_scratch_bytes;
    admit_peak(&mut peak_bytes, exact_scratch_bytes, plan_budget)?;
    for (index, col) in model.cols.iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let column = u32::try_from(index).ok()?;
        if !model.obj_coeff_exact_at(column, col.obj).is_zero() {
            return None;
        }
    }

    let total_cols = model.cols.len();
    let mut n = 0usize;
    while n < total_cols {
        if n & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let col = &model.cols[n];
        if col.kind != ColKind::Continuous || !col.lb.is_finite() || !col.ub.is_finite() {
            break;
        }
        n += 1;
    }
    if n == 0 {
        return None;
    }

    let remainder = total_cols.checked_sub(n.checked_add(2)?)?;
    if remainder % 3 != 0 {
        return None;
    }
    let k = remainder / 3;
    let c = k.checked_sub(n.checked_mul(2)?)?;
    if c == 0 || model.rows.len() != k.checked_mul(4)?.checked_add(4)? {
        return None;
    }
    if n > MAX_PROOF_VARS || k > MAX_PLAN_AFFINES || c > MAX_PROOF_CLAUSES {
        return None;
    }
    let mut base_clause_literals = 0usize;
    let mut max_clause_literals = 0usize;
    for (index, row) in model.rows[..c].iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let prospective = row.coeffs.len().checked_sub(1)?;
        if prospective > MAX_PROOF_ITEMS_PER_CLAUSE {
            return None;
        }
        base_clause_literals = base_clause_literals.checked_add(prospective)?;
        max_clause_literals = max_clause_literals.max(prospective);
        if base_clause_literals > MAX_PROOF_LITERALS {
            return None;
        }
    }
    let affine_terms = base_clause_literals.checked_add(n.checked_mul(2)?)?;
    if !plan_shape_within_limits(
        total_cols,
        n,
        c,
        k,
        c,
        base_clause_literals,
        max_clause_literals,
        affine_terms,
        recognition_budget,
    ) {
        return None;
    }
    let one = Rational::one();
    let mut lower_padding = Rational::zero();
    let mut upper_padding = Rational::zero();
    let mut uniform_input_box = None;
    let mut input_box_is_uniform = true;
    for (index, col) in model.cols[..n].iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        if col.kind != ColKind::Continuous
            || !col.lb.is_finite()
            || !col.ub.is_finite()
            || col.lb > 0.0
            || col.ub < 1.0
        {
            return None;
        }
        let lb = bounded_rational(exact_small(col.lb)?)?;
        let ub = bounded_rational(exact_small(col.ub)?)?;
        match &uniform_input_box {
            None => uniform_input_box = Some((lb.clone(), ub.clone())),
            Some((first_lb, first_ub)) if first_lb != &lb || first_ub != &ub => {
                input_box_is_uniform = false;
            }
            Some(_) => {}
        }
        if lb < Rational::zero() {
            lower_padding = bounded_rational(lower_padding - lb)?;
        }
        if ub > one {
            upper_padding = bounded_rational(upper_padding + ub - one.clone())?;
        }
    }
    let outward_padding =
        bounded_rational(lower_padding + bounded_rational(upper_padding * Rational::from(2))?)?;
    if outward_padding >= one {
        return None;
    }
    let uniform_input_box = input_box_is_uniform.then_some(uniform_input_box).flatten();
    // Canonical column order: inputs, preactivations, alternating ReLU/phase
    // pairs, then the two network outputs.
    for (index, col) in model.cols[n..n + k].iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        if !is_free_continuous(col) {
            return None;
        }
    }
    let pair_start = n + k;
    let mut retained_bytes = size_of::<SatReluPlan>();
    let mut fixed_phases = Vec::new();
    fixed_phases.try_reserve_exact(k).ok()?;
    retained_bytes = retained_bytes.checked_add(
        fixed_phases
            .capacity()
            .checked_mul(size_of::<Option<bool>>())?,
    )?;
    admit_peak_with_scratch(
        &mut peak_bytes,
        retained_bytes,
        exact_scratch_bytes,
        plan_budget,
    )?;
    for i in 0..k {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let y = &model.cols[pair_start + 2 * i];
        let phase = &model.cols[pair_start + 2 * i + 1];
        if y.kind != ColKind::Continuous || y.lb != 0.0 || !y.ub.is_finite() || y.ub <= 0.0 {
            return None;
        }
        let fixed = fixed_binary(phase)?;
        // MPS can round-trip a `BV` column as a general integer. Integrality
        // plus one of the exact boxes [0,1], [0,0], or [1,1] is still Boolean.
        if phase.kind != ColKind::Binary && phase.kind != ColKind::Integer {
            return None;
        }
        fixed_phases.push(fixed);
    }
    if !model.cols[total_cols - 2..].iter().all(is_free_continuous) {
        return None;
    }
    let mut clauses = Vec::new();
    clauses.try_reserve_exact(c).ok()?;
    retained_bytes =
        retained_bytes.checked_add(clauses.capacity().checked_mul(size_of::<Vec<Literal>>())?)?;
    admit_peak_with_scratch(
        &mut peak_bytes,
        retained_bytes,
        exact_scratch_bytes,
        plan_budget,
    )?;
    let mut affine = Vec::new();
    affine.try_reserve_exact(k).ok()?;
    retained_bytes =
        retained_bytes.checked_add(affine.capacity().checked_mul(size_of::<Affine>())?)?;
    admit_peak_with_scratch(
        &mut peak_bytes,
        retained_bytes,
        exact_scratch_bytes,
        plan_budget,
    )?;
    for i in 0..c {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let row = &model.rows[i];
        if !is_equality(model, i, row) {
            return None;
        }
        let &(z_column, z_coefficient) = row
            .coeffs
            .iter()
            .find(|&&(column, _)| column as usize == n + i)?;
        let scale = bounded_rational(-row_coefficient_exact(model, i, z_column, z_coefficient)?)?;
        if scale <= Rational::zero() {
            return None;
        }
        let inner_capacity = row.coeffs.len().checked_sub(1)?;
        let mut literals = Vec::new();
        literals.try_reserve_exact(inner_capacity).ok()?;
        let mut terms = Vec::new();
        terms.try_reserve_exact(inner_capacity).ok()?;
        retained_bytes = retained_bytes
            .checked_add(literals.capacity().checked_mul(size_of::<Literal>())?)?
            .checked_add(
                terms
                    .capacity()
                    .checked_mul(size_of::<(usize, Rational)>())?,
            )?;
        admit_peak_with_scratch(
            &mut peak_bytes,
            retained_bytes,
            exact_scratch_bytes,
            plan_budget,
        )?;
        let mut saw_z = false;
        let mut negative_literals = 0usize;
        for (term_index, &(column, coefficient)) in row.coeffs.iter().enumerate() {
            if term_index & 0x3ff == 0 && deadline_reached(deadline) {
                return None;
            }
            let column = usize::try_from(column).ok()?;
            let exact_coefficient = row_coefficient_exact(model, i, column as u32, coefficient)?;
            if column == n + i && exact_coefficient == -scale.clone() {
                saw_z = true;
                continue;
            }
            if column >= n {
                return None;
            }
            let normalized = inline_rational(bounded_rational(exact_coefficient / scale.clone())?)?;
            let var = Variable::new(u32::try_from(column).ok()?);
            let literal = if normalized == -Rational::one() {
                Literal::positive(var)
            } else if normalized == Rational::one() {
                negative_literals += 1;
                Literal::negative(var)
            } else {
                return None;
            };
            literals.push(literal);
            terms.push((column, normalized));
        }
        let rhs = inline_rational(bounded_rational(
            row_lower_exact(model, i, row)?? / scale.clone(),
        )?)?;
        if !saw_z || literals.is_empty() || rhs != Rational::from(negative_literals as i64 - 1) {
            return None;
        }
        clauses.push(literals);
        affine.push(Affine { terms, rhs });
    }

    for input in 0..n {
        if input & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let i = c + input;
        let expected = [(input, 1.0), (n + i, -1.0)];
        if !row_matches(model, i, &model.rows[i], 0.0, 0.0, &expected) {
            return None;
        }
        let mut terms = Vec::new();
        terms.try_reserve_exact(1).ok()?;
        retained_bytes = retained_bytes.checked_add(
            terms
                .capacity()
                .checked_mul(size_of::<(usize, Rational)>())?,
        )?;
        admit_peak_with_scratch(
            &mut peak_bytes,
            retained_bytes,
            exact_scratch_bytes,
            plan_budget,
        )?;
        terms.push((input, Rational::one()));
        affine.push(Affine {
            terms,
            rhs: Rational::zero(),
        });
    }
    for input in 0..n {
        if input & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let i = c + n + input;
        let expected = [(input, 2.0), (n + i, -1.0)];
        if !row_matches(model, i, &model.rows[i], 1.0, 1.0, &expected) {
            return None;
        }
        let mut terms = Vec::new();
        terms.try_reserve_exact(1).ok()?;
        retained_bytes = retained_bytes.checked_add(
            terms
                .capacity()
                .checked_mul(size_of::<(usize, Rational)>())?,
        )?;
        admit_peak_with_scratch(
            &mut peak_bytes,
            retained_bytes,
            exact_scratch_bytes,
            plan_budget,
        )?;
        terms.push((input, Rational::from(2)));
        affine.push(Affine {
            terms,
            rhs: Rational::one(),
        });
    }

    // Each three-row block must be exactly
    //   y - z >= 0
    //   y - z + M b <= M
    //   y - U b <= 0,
    // with y in [0,U]. M and U must cover the exact affine interval over the
    // padded input box, so this is an exact ReLU graph rather than a restriction.
    for (i, definition) in affine.iter().enumerate() {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let z = n + i;
        let y = pair_start + 2 * i;
        let phase = y + 1;
        let base = k + 3 * i;
        if !row_matches(
            model,
            base,
            &model.rows[base],
            0.0,
            f64::INFINITY,
            &[(z, -1.0), (y, 1.0)],
        ) {
            return None;
        }

        let middle = &model.rows[base + 1];
        let middle_scale = row_coefficient(model, base + 1, middle, y)?;
        let middle_bound = row_upper_exact(model, base + 1, middle)??;
        let m = bounded_rational(&middle_bound / &middle_scale)?;
        if row_lower_exact(model, base + 1, middle)?.is_some()
            || !middle.ub.is_finite()
            || middle.coeffs.len() != 3
            || middle_scale <= Rational::zero()
            || m < Rational::zero()
            || row_coefficient(model, base + 1, middle, z)? != -middle_scale.clone()
            || row_coefficient(model, base + 1, middle, phase)? != middle_bound
        {
            return None;
        }

        let u = model.cols[y].ub;
        if !row_matches(
            model,
            base + 2,
            &model.rows[base + 2],
            f64::NEG_INFINITY,
            0.0,
            &[(y, 1.0), (phase, -u)],
        ) {
            return None;
        }

        let (lo, hi) = affine_interval(model, definition, uniform_input_box.as_ref(), deadline)?;
        if m < -lo || bounded_rational(exact_small(u)?)? < hi {
            return None;
        }
    }
    let output0 = total_cols - 2;
    let output1 = total_cols - 1;
    let mut first_output = Vec::new();
    first_output.try_reserve_exact(c.checked_add(1)?).ok()?;
    let first_output_bytes = first_output
        .capacity()
        .checked_mul(size_of::<(usize, f64)>())?;
    admit_peak_with_scratch(
        &mut peak_bytes,
        retained_bytes.checked_add(first_output_bytes)?,
        exact_scratch_bytes,
        plan_budget,
    )?;
    for i in 0..c {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        first_output.push((pair_start + 2 * i, -1.0));
    }
    first_output.push((output0, -1.0));
    if !row_matches(model, 4 * k, &model.rows[4 * k], -1.0, -1.0, &first_output) {
        return None;
    }
    // Keep the two potentially large output-row scratch vectors disjoint.
    drop(first_output);

    let mut second_output = Vec::new();
    second_output
        .try_reserve_exact(n.checked_mul(2)?.checked_add(1)?)
        .ok()?;
    let second_output_bytes = second_output
        .capacity()
        .checked_mul(size_of::<(usize, f64)>())?;
    admit_peak_with_scratch(
        &mut peak_bytes,
        retained_bytes.checked_add(second_output_bytes)?,
        exact_scratch_bytes,
        plan_budget,
    )?;
    for i in c..c + n {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        second_output.push((pair_start + 2 * i, 1.0));
    }
    for i in c + n..k {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        second_output.push((pair_start + 2 * i, -1.0));
    }
    second_output.push((output1, -1.0));
    if !row_matches(
        model,
        4 * k + 1,
        &model.rows[4 * k + 1],
        0.0,
        0.0,
        &second_output,
    ) || !row_matches(
        model,
        4 * k + 2,
        &model.rows[4 * k + 2],
        1.0,
        f64::INFINITY,
        &[(output0, 1.0)],
    ) || !row_matches(
        model,
        4 * k + 3,
        &model.rows[4 * k + 3],
        f64::NEG_INFINITY,
        0.0,
        &[(output1, 1.0)],
    ) {
        return None;
    }

    drop(second_output);
    let gadget = Gadget {
        n,
        c,
        k,
        clauses,
        affine,
        fixed_phases,
    };
    let actual_retained = retained_plan_bytes(&gadget)?;
    if actual_retained != retained_bytes {
        // Every heap capacity was metered immediately after reservation. This
        // equality catches a future retained allocation that forgets the meter.
        return None;
    }
    admit_peak_with_scratch(
        &mut peak_bytes,
        actual_retained,
        exact_scratch_bytes,
        plan_budget,
    )?;
    Some((gadget, peak_bytes, exact_scratch_bytes))
}

fn reconstruct(
    model: &Model,
    gadget: &Gadget,
    assignment: &[bool],
    deadline: Option<Instant>,
) -> Option<Vec<BigRational>> {
    if assignment.len() < gadget.n {
        return None;
    }
    // Reconstruct in AY's inline exact rational representation.  Canonical
    // SAT-ReLU coefficients and Boolean values stay allocation-free here; an
    // unusually large affine sum promotes exactly.  Convert each final column
    // once at the public model boundary instead of allocating BigRationals for
    // every intermediate literal addition and ReLU/output sum.
    let mut values = Vec::new();
    values.try_reserve_exact(model.cols.len()).ok()?;
    values.resize(model.cols.len(), Rational::zero());
    for (input, &value) in assignment[..gadget.n].iter().enumerate() {
        if input & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        values[input] = if value {
            Rational::one()
        } else {
            Rational::zero()
        };
    }

    for (i, definition) in gadget.affine.iter().enumerate() {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let mut z = -definition.rhs.clone();
        for (term_index, (input, coefficient)) in definition.terms.iter().enumerate() {
            if term_index & 0x3ff == 0 && deadline_reached(deadline) {
                return None;
            }
            // Inputs are exactly Boolean here, so no multiplication is needed.
            if assignment[*input] {
                z += coefficient;
            }
        }
        values[gadget.n + i] = z;
    }

    let pair_start = gadget.n + gadget.k;
    for i in 0..gadget.k {
        if i & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let z = values[gadget.n + i].clone();
        let y_col = pair_start + 2 * i;
        let phase_col = y_col + 1;
        values[y_col] = if z > Rational::zero() {
            z.clone()
        } else {
            Rational::zero()
        };
        let active = if z > Rational::zero() {
            true
        } else if z < Rational::zero() {
            false
        } else {
            // Both phases describe ReLU(0)=0. Honor a prefix-fixed phase when
            // present; otherwise choose the inactive phase deterministically.
            gadget.fixed_phases[i].unwrap_or(false)
        };
        values[phase_col] = if active {
            Rational::one()
        } else {
            Rational::zero()
        };
    }

    let output0 = model.cols.len() - 2;
    let output1 = model.cols.len() - 1;
    let mut y0 = Rational::one();
    for i in 0..gadget.c {
        y0 -= &values[pair_start + 2 * i];
    }
    values[output0] = y0;

    let mut y1 = Rational::zero();
    for i in gadget.c..gadget.c + gadget.n {
        y1 += &values[pair_start + 2 * i];
    }
    for i in gadget.c + gadget.n..gadget.k {
        y1 -= &values[pair_start + 2 * i];
    }
    values[output1] = y1;
    let mut exact_values = Vec::new();
    exact_values.try_reserve_exact(values.len()).ok()?;
    for (index, value) in values.iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        exact_values.push(value.to_big());
    }
    if deadline_reached(deadline) {
        return None;
    }
    Some(exact_values)
}

fn affine_interval(
    model: &Model,
    affine: &Affine,
    uniform_input_box: Option<&(Rational, Rational)>,
    deadline: Option<Instant>,
) -> Option<(Rational, Rational)> {
    if let Some((lb, ub)) = uniform_input_box {
        // The production W1 encoding gives every input the same padded box.
        // Sum coefficients by sign before applying that box: this is exactly
        // the same interval expression as the term-at-a-time path below, but
        // converts and multiplies the potentially heap-backed bounds once per
        // affine instead of once per literal.
        let mut positive = Rational::zero();
        let mut negative = Rational::zero();
        for (index, (_, coefficient)) in affine.terms.iter().enumerate() {
            if index & 0x3ff == 0 && deadline_reached(deadline) {
                return None;
            }
            if coefficient >= &Rational::zero() {
                positive = bounded_rational(&positive + coefficient)?;
            } else {
                negative = bounded_rational(&negative + coefficient)?;
            }
        }
        let base = bounded_rational(-affine.rhs.clone())?;
        let lo = bounded_rational(
            base.clone() + bounded_rational(&positive * lb)? + bounded_rational(&negative * ub)?,
        )?;
        let hi = bounded_rational(
            base + bounded_rational(positive * ub)? + bounded_rational(negative * lb)?,
        )?;
        return Some((lo, hi));
    }

    let mut lo = bounded_rational(-affine.rhs.clone())?;
    let mut hi = lo.clone();
    for (index, (input, coefficient)) in affine.terms.iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let col = &model.cols[*input];
        let lb = bounded_rational(exact_small(col.lb)?)?;
        let ub = bounded_rational(exact_small(col.ub)?)?;
        if coefficient >= &Rational::zero() {
            lo = bounded_rational(lo + bounded_rational(coefficient * &lb)?)?;
            hi = bounded_rational(hi + bounded_rational(coefficient * &ub)?)?;
        } else {
            lo = bounded_rational(lo + bounded_rational(coefficient * &ub)?)?;
            hi = bounded_rational(hi + bounded_rational(coefficient * &lb)?)?;
        }
    }
    Some((lo, hi))
}

fn fixed_binary(col: &ColSpec) -> Option<Option<bool>> {
    match (col.lb, col.ub) {
        (0.0, 0.0) => Some(Some(false)),
        (1.0, 1.0) => Some(Some(true)),
        (0.0, 1.0) => Some(None),
        _ => None,
    }
}

fn is_free_continuous(col: &ColSpec) -> bool {
    col.kind == ColKind::Continuous && col.lb == f64::NEG_INFINITY && col.ub == f64::INFINITY
}

fn inline_rational(value: Rational) -> Option<Rational> {
    match value {
        small @ Rational::Small(_, _) => Some(small),
        Rational::Big(_) => None,
    }
}

fn row_coefficient_exact(model: &Model, row: usize, column: u32, advice: f64) -> Option<Rational> {
    bounded_rational(model.row_coeff_exact_small(row, column, advice))
}

fn row_lower_exact(model: &Model, index: usize, row: &RowSpec) -> Option<Option<Rational>> {
    match model.row_lb_exact_small(index, row.lb) {
        None => (row.lb == f64::NEG_INFINITY).then_some(None),
        Some(truth) => bounded_rational(truth).map(Some),
    }
}

fn row_upper_exact(model: &Model, index: usize, row: &RowSpec) -> Option<Option<Rational>> {
    match model.row_ub_exact_small(index, row.ub) {
        None => (row.ub == f64::INFINITY).then_some(None),
        Some(truth) => bounded_rational(truth).map(Some),
    }
}

fn is_equality(model: &Model, index: usize, row: &RowSpec) -> bool {
    matches!(
        (row_lower_exact(model, index, row), row_upper_exact(model, index, row)),
        (Some(Some(lower)), Some(Some(upper))) if lower == upper
    )
}

fn row_matches(
    model: &Model,
    row_index: usize,
    row: &RowSpec,
    lb: f64,
    ub: f64,
    expected: &[(usize, f64)],
) -> bool {
    let expected_len = expected
        .iter()
        .filter(|(_, coefficient)| *coefficient != 0.0)
        .count();
    let Some(&(first_column, first_coefficient)) =
        expected.iter().find(|(_, coefficient)| *coefficient != 0.0)
    else {
        return false;
    };
    if row.coeffs.len() != expected_len || u32::try_from(first_column).ok() != Some(row.coeffs[0].0)
    {
        return false;
    }
    let Some(actual0) = row_coefficient_exact(model, row_index, row.coeffs[0].0, row.coeffs[0].1)
    else {
        return false;
    };
    let Some(first_coefficient) = exact_small(first_coefficient).and_then(bounded_rational) else {
        return false;
    };
    let Some(scale) = bounded_rational(actual0 / first_coefficient) else {
        return false;
    };
    let Some(lower) = row_lower_exact(model, row_index, row) else {
        return false;
    };
    let Some(upper) = row_upper_exact(model, row_index, row) else {
        return false;
    };
    if scale <= Rational::zero()
        || !scaled_bound_matches(lower.as_ref(), row.lb, lb, &scale)
        || !scaled_bound_matches(upper.as_ref(), row.ub, ub, &scale)
    {
        return false;
    }

    let mut previous = None;
    for (&(actual_column, actual), &(want_column, want)) in row.coeffs.iter().zip(
        expected
            .iter()
            .filter(|(_, coefficient)| *coefficient != 0.0),
    ) {
        let Some(want_column) = u32::try_from(want_column).ok() else {
            return false;
        };
        // All recognizer call sites construct expected rows in column order.
        // Rejecting a future unordered caller is safer than silently paying to
        // sort and obscuring that structural contract in this hot loop.
        if previous.is_some_and(|column| column >= want_column) {
            return false;
        }
        previous = Some(want_column);
        let exact_actual = row_coefficient_exact(model, row_index, actual_column, actual);
        let exact_want = exact_small(want).and_then(bounded_rational);
        if actual_column != want_column
            || !exact_actual.is_some_and(|value| {
                exact_want
                    .and_then(|want| bounded_rational(want * &scale))
                    .is_some_and(|want| value == want)
            })
        {
            return false;
        }
    }
    true
}

fn scaled_bound_matches(
    actual: Option<&Rational>,
    actual_proxy: f64,
    expected: f64,
    scale: &Rational,
) -> bool {
    if expected.is_infinite() {
        return actual.is_none() && actual_proxy == expected;
    }
    actual_proxy.is_finite()
        && actual.is_some_and(|value| {
            exact_small(expected)
                .and_then(bounded_rational)
                .and_then(|want| bounded_rational(want * scale))
                .is_some_and(|want| value == &want)
        })
}

fn row_coefficient(
    model: &Model,
    row_index: usize,
    row: &RowSpec,
    column: usize,
) -> Option<Rational> {
    row.coeffs
        .iter()
        .find(|&&(candidate, _)| candidate as usize == column)
        .and_then(|&(candidate, coefficient)| {
            row_coefficient_exact(model, row_index, candidate, coefficient)
        })
}

fn trace_enabled() -> bool {
    // Cached: the ratchet in `tests/env_ledger.rs` counts a bare `env::var_os`
    // on the solve path as a LIVE read — a fresh `getenv` a concurrent
    // `set_var` can race, which priming cannot help. `OnceLock` is the shape
    // that ratchet asks for and `simplex.rs` already uses.
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BabSession, Col, Outcome, Sense, SolveOpts};
    use std::fmt::Write as _;

    const EPS: f64 = 1.0 / 1_048_576.0;

    /// `(variable, true)` is a positive literal; `false` is negated.
    fn gadget(
        n: usize,
        clauses: &[Vec<(usize, bool)>],
        epsilon: f64,
        fixed_phases: &[(usize, bool)],
    ) -> Model {
        let c = clauses.len();
        let k = c + 2 * n;
        let mut definitions: Vec<(Vec<(usize, f64)>, f64)> = Vec::with_capacity(k);
        for clause in clauses {
            let negative = clause.iter().filter(|(_, positive)| !positive).count();
            definitions.push((
                clause
                    .iter()
                    .map(|&(variable, positive)| {
                        assert!(variable < n);
                        (variable, if positive { -1.0 } else { 1.0 })
                    })
                    .collect(),
                negative as f64 - 1.0,
            ));
        }
        for input in 0..n {
            definitions.push((vec![(input, 1.0)], 0.0));
        }
        for input in 0..n {
            definitions.push((vec![(input, 2.0)], 1.0));
        }

        let input_lb = -epsilon;
        let input_ub = 1.0 + epsilon;
        let interval = |terms: &[(usize, f64)], rhs: f64| {
            let mut lo = -rhs;
            let mut hi = -rhs;
            for &(_, coefficient) in terms {
                if coefficient > 0.0 {
                    lo += coefficient * input_lb;
                    hi += coefficient * input_ub;
                } else {
                    lo += coefficient * input_ub;
                    hi += coefficient * input_lb;
                }
            }
            (lo, hi)
        };

        let mut model = Model::new();
        let inputs: Vec<Col> = (0..n).map(|_| model.add_col(input_lb, input_ub)).collect();
        let preacts: Vec<Col> = (0..k)
            .map(|_| model.add_col(f64::NEG_INFINITY, f64::INFINITY))
            .collect();
        let mut relus = Vec::with_capacity(k);
        let mut phases = Vec::with_capacity(k);
        let mut intervals = Vec::with_capacity(k);
        for (i, (terms, rhs)) in definitions.iter().enumerate() {
            let (lo, hi) = interval(terms, *rhs);
            assert!(lo < 0.0 && hi > 0.0);
            let y = model.add_col(0.0, hi);
            let phase = model.add_binary_col();
            if let Some(&(_, value)) = fixed_phases.iter().find(|(index, _)| *index == i) {
                model.fix_col(phase, if value { 1.0 } else { 0.0 });
            }
            relus.push(y);
            phases.push(phase);
            intervals.push((lo, hi));
        }
        let output0 = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let output1 = model.add_col(f64::NEG_INFINITY, f64::INFINITY);

        for (i, (terms, rhs)) in definitions.iter().enumerate() {
            let mut row: Vec<(Col, f64)> = terms
                .iter()
                .map(|&(input, coefficient)| (inputs[input], coefficient))
                .collect();
            row.push((preacts[i], -1.0));
            model.add_row(*rhs, *rhs, &row);
        }
        for i in 0..k {
            let (lo, hi) = intervals[i];
            let m = -lo;
            model.add_row(0.0, f64::INFINITY, &[(relus[i], 1.0), (preacts[i], -1.0)]);
            model.add_row(
                f64::NEG_INFINITY,
                m,
                &[(relus[i], 1.0), (preacts[i], -1.0), (phases[i], m)],
            );
            model.add_row(f64::NEG_INFINITY, 0.0, &[(relus[i], 1.0), (phases[i], -hi)]);
        }

        let mut y0: Vec<(Col, f64)> = relus[..c].iter().map(|&y| (y, -1.0)).collect();
        y0.push((output0, -1.0));
        model.add_row(-1.0, -1.0, &y0);

        let mut y1: Vec<(Col, f64)> = relus[c..c + n].iter().map(|&y| (y, 1.0)).collect();
        y1.extend(relus[c + n..].iter().map(|&y| (y, -1.0)));
        y1.push((output1, -1.0));
        model.add_row(0.0, 0.0, &y1);
        model.add_row(1.0, f64::INFINITY, &[(output0, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(output1, 1.0)]);
        model
    }

    fn gadget_mps(model: &Model) -> String {
        // The production NY capture emits the complete decimal expansion of
        // every finite dyadic f64.  All values constructed by `gadget` are
        // integer multiples of 2^-20, so twenty fractional digits preserve
        // the exact f64 rational instead of merely round-tripping to it.  A
        // shortest decimal can denote a different rational; the MPS reader
        // correctly turns such a continuous bound into a singleton row, which
        // would make this synthetic fixture a different model shape.
        let number = |value: f64| format!("{value:.20}");
        let mut text = String::from("NAME SATRELU\nROWS\n N OBJ\n");
        for (index, row) in model.rows.iter().enumerate() {
            let kind = if row.lb.is_finite() && row.ub.is_finite() && row.lb == row.ub {
                'E'
            } else if row.lb.is_finite() && row.ub == f64::INFINITY {
                'G'
            } else if row.lb == f64::NEG_INFINITY && row.ub.is_finite() {
                'L'
            } else {
                panic!("test MPS helper does not support ranged/free rows")
            };
            let _ = writeln!(text, " {kind} R{index}");
        }
        text.push_str("COLUMNS\n");
        for column in 0..model.num_cols() {
            for (row_index, row) in model.rows.iter().enumerate() {
                if let Some((_, coefficient)) = row
                    .coeffs
                    .iter()
                    .find(|(candidate, _)| *candidate as usize == column)
                {
                    let _ = writeln!(text, " C{column} R{row_index} {}", number(*coefficient));
                }
            }
        }
        text.push_str("RHS\n");
        for (index, row) in model.rows.iter().enumerate() {
            let rhs = if row.lb.is_finite() { row.lb } else { row.ub };
            let _ = writeln!(text, " RHS1 R{index} {}", number(rhs));
        }
        text.push_str("BOUNDS\n");
        for column in 0..model.num_cols() {
            let handle = Col(u32::try_from(column).expect("small test model"));
            let (lb, ub) = model.col_bounds(handle);
            match model.col_kind(handle) {
                ColKind::Binary => {
                    let _ = writeln!(text, " BV BND C{column}");
                }
                ColKind::Continuous => {
                    if lb == f64::NEG_INFINITY && ub == f64::INFINITY {
                        let _ = writeln!(text, " FR BND C{column}");
                    } else {
                        if lb == f64::NEG_INFINITY {
                            let _ = writeln!(text, " MI BND C{column}");
                        } else {
                            let _ = writeln!(text, " LO BND C{column} {}", number(lb));
                        }
                        if ub.is_finite() {
                            let _ = writeln!(text, " UP BND C{column} {}", number(ub));
                        }
                    }
                }
                ColKind::Integer => panic!("test MPS helper only needs binary integrality"),
            }
        }
        text.push_str("ENDATA\n");
        text
    }

    fn scale_first_gadget_mps_row(text: &str) -> String {
        // An odd 54-bit factor survives the reader's power-of-two row
        // normalizer with 54 significant bits.  Its f64 advice is therefore
        // inexact, while exact normalization still recovers the same canonical
        // clause equation.  This deliberately exercises a side-store value
        // produced by the MPS reader rather than manufacturing one afterward.
        const SCALE: u64 = (1_u64 << 53) + 1;
        let mut scaled = String::with_capacity(text.len());
        let mut replacements = 0usize;
        for line in text.lines() {
            let fields: Vec<&str> = line.split_whitespace().collect();
            if fields.len() == 3 && fields[1] == "R0" {
                assert_eq!(fields[2], "-1.00000000000000000000");
                let _ = writeln!(scaled, " {} {} -{SCALE}", fields[0], fields[1]);
                replacements += 1;
            } else {
                let _ = writeln!(scaled, "{line}");
            }
        }
        assert_eq!(replacements, 3, "two coefficients and one RHS");
        scaled
    }

    fn emit_session_ayc(
        session: &BabSession,
        model_text: &str,
        names: &[String],
        scale: &BigRational,
        outcome: &Outcome,
    ) -> String {
        let ctx = crate::cert_io::EmitCtx {
            model: session.model(),
            model_text,
            col_names: names,
            obj_scale: scale,
            provenance: "sat-relu-rup-e2e-test",
            replay_claims: session.replay_claims(),
            affine_aggregation_certificate: session.affine_aggregation_certificate(),
            parity_infeasibility_certificate: session.parity_infeasibility_certificate(),
            sat_relu_infeasibility_certificate: session.sat_relu_infeasibility_certificate(),
            network_design_infeasibility_certificate: session
                .network_design_infeasibility_certificate(),
            network_design_optimality_certificate: session.network_design_optimality_certificate(),
            block_angular_optimality_certificate: session.block_angular_optimality_certificate(),
            single_machine_scheduling_optimality_certificate: session
                .single_machine_scheduling_optimality_certificate(),
            single_row_dp_infeasibility_certificate: session
                .single_row_dp_infeasibility_certificate(),
            multi_row_bdd_infeasibility_certificate: session
                .multi_row_bdd_infeasibility_certificate(),
            open_domain_single_row_dp_infeasibility_certificate: session
                .open_domain_single_row_dp_infeasibility_certificate(),
            open_domain_multi_row_bdd_infeasibility_certificate: session
                .open_domain_multi_row_bdd_infeasibility_certificate(),
            open_domain_hybrid_pb_lp_infeasibility_certificate: session
                .open_domain_hybrid_pb_lp_infeasibility_certificate(),
            open_domain_hybrid_integer_lift_infeasibility_certificate: session
                .open_domain_hybrid_integer_lift_infeasibility_certificate(),
            hybrid_pb_lp_infeasibility_certificate: session
                .hybrid_pb_lp_infeasibility_certificate(),
            hybrid_integer_lift_infeasibility_certificate: session
                .hybrid_integer_lift_infeasibility_certificate(),
            max_bytes: None,
        };
        crate::cert_io::emit(&ctx, outcome)
    }

    fn reseal_ayc(text: &str) -> String {
        let mut body = String::new();
        for line in text
            .lines()
            .take_while(|line| !line.trim_start().starts_with("%END"))
        {
            body.push_str(line);
            body.push('\n');
        }
        let digest = crate::cert_io::sha256_hex(body.as_bytes());
        format!("{body}%END sha256:{digest}\n")
    }

    fn flip_hex_after(text: &str, marker: &str) -> String {
        let mut changed = text.to_owned();
        let index = changed.find(marker).expect("tamper marker exists") + marker.len();
        let replacement = if &changed[index..index + 1] == "0" {
            "1"
        } else {
            "0"
        };
        changed.replace_range(index..index + 1, replacement);
        reseal_ayc(&changed)
    }

    fn invalidate_first_nonempty_rup_clause(text: &str) -> String {
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        let line = lines
            .iter_mut()
            .find(|line| {
                line.starts_with("step ")
                    && line
                        .split_whitespace()
                        .nth(2)
                        .and_then(|token| token.strip_prefix("lits="))
                        .is_some_and(|count| count != "0")
            })
            .expect("fixture proof has a nonempty derived clause");
        let mut fields: Vec<String> = line.split_whitespace().map(str::to_owned).collect();
        // Zero is never a resolution literal, so this cannot accidentally be
        // another valid RUP clause on a symmetric contradiction.
        fields[3] = "0".to_owned();
        *line = fields.join(" ");
        reseal_ayc(&lines.join("\n"))
    }

    fn invalidate_a_rup_hint(text: &str) -> String {
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        let line = lines
            .iter_mut()
            .find(|line| {
                line.starts_with("step ")
                    && line.split_whitespace().any(|token| {
                        token
                            .strip_prefix("hints=")
                            .and_then(|count| count.parse::<usize>().ok())
                            .is_some_and(|count| count >= 2)
                    })
            })
            .expect("fixture proof has a step with at least two RUP hints");
        let mut fields: Vec<String> = line.split_whitespace().map(str::to_owned).collect();
        let hint_header = fields
            .iter()
            .position(|field| field.starts_with("hints="))
            .expect("hint header");
        // A step cannot cite itself. This is a deterministic forward-hint
        // corruption, unlike deleting/repeating a potentially redundant hint.
        fields[hint_header + 1] = fields[1].clone();
        *line = fields.join(" ");
        reseal_ayc(&lines.join("\n"))
    }

    fn sat_point(model: &Model) -> Vec<BigRational> {
        match try_solve(model, None) {
            Some(SatReluDecision::Sat(point)) => point.into_values(),
            Some(SatReluDecision::Unsat) => panic!("expected SAT, got UNSAT"),
            None => panic!("canonical gadget was declined"),
        }
    }

    fn rescale_exact_row(model: &mut Model, row_index: usize, scale: &BigRational) {
        let row = model.rows[row_index].clone();
        let handle = model.row_at(row_index).expect("row");
        // Scale the authoritative row, not its rounded MPS advice. This helper
        // is also used on an already parsed source in the digest-binding test.
        let coefficients: Vec<_> = row
            .coeffs
            .iter()
            .map(|&(column, advice)| {
                (
                    column,
                    model.row_coeff_exact(row_index, column, advice) * scale,
                )
            })
            .collect();
        let lower = model.row_lb_exact(row_index, row.lb);
        let upper = model.row_ub_exact(row_index, row.ub);
        for (column, coefficient) in coefficients {
            model.record_inexact_row_coeff(handle, column, coefficient);
        }
        if let Some(lower) = lower {
            model.record_inexact_row_bound(handle, true, lower * scale);
        }
        if let Some(upper) = upper {
            model.record_inexact_row_bound(handle, false, upper * scale);
        }
    }

    #[test]
    fn recovers_positive_and_negative_literals() {
        let model = gadget(2, &[vec![(0, true)], vec![(1, false)]], EPS, &[]);
        let point = sat_point(&model);
        assert_eq!(point[0], BigRational::one());
        assert_eq!(point[1], BigRational::zero());
        assert!(model.check_point(&point).is_ok());
    }

    #[test]
    fn returns_an_exact_sat_witness() {
        let model = gadget(
            2,
            &[vec![(0, true), (1, true)], vec![(0, false), (1, true)]],
            EPS,
            &[],
        );
        let point = sat_point(&model);
        assert_eq!(point.len(), model.num_cols());
        assert!(model.check_point(&point).is_ok());
    }

    #[test]
    fn returns_unsat_for_contradictory_clauses() {
        let model = gadget(1, &[vec![(0, true)], vec![(0, false)]], EPS, &[]);
        assert!(matches!(
            try_solve(&model, None),
            Some(SatReluDecision::Unsat)
        ));
    }

    #[test]
    fn fixed_active_clause_enforces_exactly_one_literal() {
        // The two unit clauses force both literals true. The first clause's
        // active phase fixes its preactivation at zero, hence at most one true.
        let model = gadget(
            2,
            &[vec![(0, true), (1, true)], vec![(0, true)], vec![(1, true)]],
            EPS,
            &[(0, true)],
        );
        assert!(matches!(
            try_solve(&model, None),
            Some(SatReluDecision::Unsat)
        ));
    }

    #[test]
    fn mps_style_fixed_integer_phase_is_accepted() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[(0, false)]);
        let phase_column = 1 + 3 + 1;
        model.cols[phase_column].kind = ColKind::Integer;
        assert!(matches!(
            try_solve(&model, None),
            Some(SatReluDecision::Sat(_))
        ));
    }

    #[test]
    fn mps_style_live_integer_phases_are_accepted() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let pair_start = 1 + 3;
        for phase in (0..3).map(|i| pair_start + 2 * i + 1) {
            model.cols[phase].kind = ColKind::Integer;
        }
        assert!(matches!(
            try_solve(&model, None),
            Some(SatReluDecision::Sat(_))
        ));
    }

    #[test]
    fn positive_row_scaling_is_accepted() {
        let mut model = gadget(2, &[vec![(0, true), (1, false)]], EPS, &[]);
        for index in 0..model.rows.len() {
            let row = model.rows[index].clone();
            let scale = 8.0;
            let coeffs: Vec<(Col, f64)> = row
                .coeffs
                .iter()
                .map(|&(column, coefficient)| (Col(column), coefficient * scale))
                .collect();
            let scaled = |bound: f64| {
                if bound.is_finite() {
                    bound * scale
                } else {
                    bound
                }
            };
            model.set_row(
                model.row_at(index).expect("row"),
                scaled(row.lb),
                scaled(row.ub),
                &coeffs,
            );
        }
        let point = sat_point(&model);
        assert!(model.check_point(&point).is_ok());
    }

    #[test]
    fn uniform_heap_backed_input_box_matches_generic_exact_interval() {
        let epsilon = f64::from(f32::from_bits(1));
        let lower = -epsilon;
        let upper = 1.0 + f64::from(f32::EPSILON);
        let mut model = Model::new();
        for _ in 0..4 {
            model.add_col(lower, upper);
        }
        let affine = Affine {
            terms: vec![
                (0, Rational::from(3)),
                (1, Rational::from(-2)),
                (2, Rational::from(5)),
                (3, Rational::from(-7)),
            ],
            rhs: Rational::from(1),
        };
        let input_box = (
            bounded_rational(exact_small(lower).expect("finite lower bound")).expect("bounded"),
            bounded_rational(exact_small(upper).expect("finite upper bound")).expect("bounded"),
        );
        assert!(matches!(input_box.0, Rational::Big(_)));
        assert_eq!(
            affine_interval(&model, &affine, Some(&input_box), None),
            affine_interval(&model, &affine, None, None),
            "sign aggregation must preserve the exact generic interval"
        );
    }

    #[test]
    fn nonuniform_input_box_uses_the_generic_interval() {
        let mut model = gadget(2, &[vec![(0, true), (1, false)]], EPS, &[]);
        model.cols[1].lb = -EPS / 2.0;
        assert!(
            prepare(&model, None).is_some(),
            "a sound nonuniform model must retain the term-at-a-time path"
        );
    }

    #[test]
    fn uniform_heap_backed_input_box_is_detected_end_to_end() {
        let mut model = gadget(
            2,
            &[vec![(0, true)], vec![(0, false)], vec![(1, true)]],
            EPS,
            &[],
        );
        let lower = -f64::from(f32::from_bits(1));
        let upper = 1.0 + f64::from(f32::EPSILON);
        for input in &mut model.cols[..2] {
            input.lb = lower;
            input.ub = upper;
        }
        assert!(matches!(
            exact_small(lower).expect("finite lower bound"),
            Rational::Big(_)
        ));
        assert!(
            prepare(&model, None).is_some(),
            "recognition must select and accept the exact uniform-box path"
        );
        assert!(matches!(
            try_solve(&model, None),
            Some(SatReluDecision::Unsat)
        ));
    }

    #[test]
    fn uniform_interval_still_rejects_an_insufficient_big_m() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let row_index = 4usize;
        let row = model.rows[row_index].clone();
        let phase = 5u32;
        let smaller_m = row.ub / 2.0;
        let coeffs: Vec<(Col, f64)> = row
            .coeffs
            .iter()
            .map(|&(column, coefficient)| {
                (
                    Col(column),
                    if column == phase {
                        smaller_m
                    } else {
                        coefficient
                    },
                )
            })
            .collect();
        model.set_row(
            model.row_at(row_index).expect("middle ReLU row"),
            row.lb,
            smaller_m,
            &coeffs,
        );
        assert!(
            prepare(&model, None).is_none(),
            "sign aggregation must not weaken exact Big-M coverage"
        );
    }

    #[test]
    fn parsed_mps_side_store_uses_the_bounded_route() {
        let source = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let model_text = scale_first_gadget_mps_row(&gadget_mps(&source));
        let parsed = crate::read_mps(&model_text).expect("gadget MPS parses");
        assert!(parsed.model.has_inexact_coeffs());
        reset_test_cdcl_invocations();
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(parsed.model, &opts).expect("session");
        assert!(matches!(
            session.check().expect("solve"),
            Outcome::Optimal { .. }
        ));
        assert_eq!(test_cdcl_invocations(), 0);
        assert_eq!(test_bounded_cdcl_invocations(), 1);
    }

    #[test]
    fn authoritative_noncanonical_row_override_is_declined() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        model.record_inexact_row_coeff(crate::Row(0), 0, BigRational::new(3.into(), 2.into()));
        assert!(prepare(&model, None).is_none());
    }

    #[test]
    fn authoritative_identity_override_is_declined_by_scaled_row_match() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        // c=1, so row 1 is the identity preactivation `x - z = 0`.
        model.record_inexact_row_coeff(crate::Row(1), 0, BigRational::new(3.into(), 2.into()));
        assert!(prepare(&model, None).is_none());
    }

    #[test]
    fn authoritative_middle_relu_side_override_is_declined() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        // k=3; row k+1 is the first ReLU block's y-z+M b <= M side.
        let row_index = 4usize;
        let row = &model.rows[row_index];
        let wrong = crate::model::exact(row.ub).expect("finite M") + BigRational::one();
        model.record_inexact_row_bound(model.row_at(row_index).expect("row"), false, wrong);
        assert!(prepare(&model, None).is_none());
    }

    #[test]
    fn authoritative_big_whole_row_scale_normalizes_to_small_terms() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let scale = BigRational::from_integer(
            (num_bigint::BigInt::one() << 80usize) + num_bigint::BigInt::one(),
        );
        for row in 0..model.num_rows() {
            rescale_exact_row(&mut model, row, &scale);
        }
        assert!(model.has_inexact_coeffs());
        let point = sat_point(&model);
        assert!(model.check_point(&point).is_ok());
        let plan = prepare(&model, None).expect("big raw scale normalizes exactly");
        assert!(plan
            .gadget
            .affine
            .iter()
            .flat_map(|affine| affine.terms.iter().map(|(_, value)| value))
            .all(Rational::is_small));
    }

    #[test]
    fn authoritative_objective_truth_owns_both_proxy_zero_classes() {
        let mut exact_nonzero = gadget(1, &[vec![(0, true)]], EPS, &[]);
        exact_nonzero.record_inexact_obj_coeff(0, BigRational::one());
        assert!(prepare(&exact_nonzero, None).is_none());

        let mut exact_zero = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let input = exact_zero.col_at(0).expect("input");
        exact_zero.set_objective(&[(input, 1.0)], Sense::Minimize);
        exact_zero.record_inexact_obj_coeff(0, BigRational::zero());
        assert!(prepare(&exact_zero, None).is_some());
    }

    #[test]
    fn oversized_exact_source_declines_before_cdcl() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let oversized = num_bigint::BigInt::one() << (MAX_EXACT_SOURCE_BITS as usize + 1);
        model.record_inexact_row_coeff(crate::Row(0), 0, BigRational::from_integer(oversized));
        reset_test_cdcl_invocations();
        assert!(prepare(&model, None).is_none());
        assert_eq!(test_cdcl_invocations(), 0);
        assert_eq!(test_bounded_cdcl_invocations(), 0);
    }

    #[test]
    fn derived_exact_bit_cap_is_inclusive_and_fail_closed() {
        let at_cap = BigRational::from_integer(
            num_bigint::BigInt::one() << (MAX_EXACT_DERIVED_BITS as usize - 1),
        );
        let over_cap =
            BigRational::from_integer(num_bigint::BigInt::one() << MAX_EXACT_DERIVED_BITS as usize);
        assert!(bounded_rational(Rational::from_big(at_cap)).is_some());
        assert!(bounded_rational(Rational::from_big(over_cap)).is_none());
    }

    #[test]
    fn expired_deadline_declines_without_a_late_verdict() {
        let model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let deadline = Instant::now() - std::time::Duration::from_millis(1);
        assert!(try_solve(&model, Some(deadline)).is_none());
    }

    #[test]
    fn session_returns_and_rechecks_the_sat_witness() {
        let model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        reset_test_cdcl_invocations();
        let opts = SolveOpts::new();
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(matches!(outcome, Outcome::Feasible { .. }));
        assert!(session.replay_claims().is_empty());
        assert_eq!(test_cdcl_invocations(), 0, "no ordinary-CDCL prepass");
        assert_eq!(test_bounded_cdcl_invocations(), 1, "one bounded pass");
    }

    #[test]
    fn nonmatching_binary_model_declines_before_cdcl() {
        let mut model = Model::new();
        for _ in 0..4096 {
            model.add_binary_col();
        }
        reset_test_cdcl_invocations();
        assert!(!cheap_shape_gate(&model));
        assert!(try_solve(&model, None).is_none());
        assert_eq!(test_cdcl_invocations(), 0);
        assert_eq!(test_bounded_cdcl_invocations(), 0);
    }

    #[test]
    fn plan_shape_caps_precede_route_owned_capacities() {
        assert!(plan_shape_within_limits(
            12,
            1,
            1,
            3,
            1,
            1,
            1,
            3,
            MAX_PLAN_BYTES,
        ));
        assert!(!plan_shape_within_limits(
            MAX_PLAN_MODEL_COLS + 1,
            1,
            1,
            3,
            1,
            1,
            1,
            3,
            MAX_PLAN_BYTES,
        ));
        assert!(!plan_shape_within_limits(
            12,
            MAX_PROOF_VARS + 1,
            1,
            3,
            1,
            1,
            1,
            3,
            MAX_PLAN_BYTES,
        ));
        assert!(!plan_shape_within_limits(
            12,
            1,
            1,
            MAX_PLAN_AFFINES + 1,
            1,
            1,
            1,
            3,
            MAX_PLAN_BYTES,
        ));
        assert!(!plan_shape_within_limits(
            12,
            1,
            1,
            3,
            MAX_PROOF_CLAUSES + 1,
            1,
            1,
            3,
            MAX_PLAN_BYTES,
        ));
        assert!(!plan_shape_within_limits(
            12,
            1,
            1,
            3,
            1,
            MAX_PROOF_LITERALS + 1,
            1,
            3,
            MAX_PLAN_BYTES,
        ));
        assert_eq!(
            projected_plan_peak_bytes(usize::MAX, 1, 1, 3, 1, 1, 1, 3),
            None,
            "size arithmetic must fail closed on overflow"
        );
    }

    #[test]
    fn replay_limits_are_checked_before_clone_materialization() {
        let model = gadget(1, &[vec![(0, true)], vec![(0, false)]], EPS, &[]);
        let plan = prepare(&model, None).expect("plan");
        let mut derived = Vec::with_capacity(8);
        let clause = Vec::<Literal>::with_capacity(7);
        let rup_hints = Vec::<u64>::with_capacity(9);
        derived.push(RupStep {
            id: plan.clauses().len() as u64 + 1,
            clause,
            rup_hints,
        });
        let certificate = SatReluInfeasibilityCertificate::from_wire_parts(
            1,
            [0; 32],
            [0; 32],
            plan.num_vars(),
            plan.clauses().len(),
            derived,
            plan.clauses().len() as u64 + 1,
        );
        assert!(certificate.derived.capacity() > certificate.derived.len());
        assert!(certificate.derived[0].clause.capacity() > certificate.derived[0].clause.len());
        assert!(
            certificate.derived[0].rup_hints.capacity() > certificate.derived[0].rup_hints.len()
        );
        let mut limits = validation_limits(None, MAX_PROOF_MEMORY_BYTES / 2);
        limits.max_derived_steps = 0;
        assert!(materialize_replay_dag(&plan, &certificate, &limits, None).is_none());
        limits.max_derived_steps = 1;
        limits.max_bytes = 0;
        assert!(materialize_replay_dag(&plan, &certificate, &limits, None).is_none());

        let retained = replay_source_retained_bytes(&plan, &certificate, None)
            .expect("bounded retained-source accounting");
        let expected_retained = plan
            .retained_bytes()
            .checked_add(plan.exact_scratch_bytes())
            .and_then(|bytes| bytes.checked_add(size_of::<SatReluInfeasibilityCertificate>()))
            .and_then(|bytes| {
                bytes.checked_add(
                    certificate
                        .derived
                        .capacity()
                        .checked_mul(size_of::<RupStep>())?,
                )
            })
            .and_then(|bytes| {
                bytes.checked_add(
                    certificate.derived[0]
                        .clause
                        .capacity()
                        .checked_mul(size_of::<Literal>())?,
                )
            })
            .and_then(|bytes| {
                bytes.checked_add(
                    certificate.derived[0]
                        .rup_hints
                        .capacity()
                        .checked_mul(size_of::<u64>())?,
                )
            })
            .expect("test accounting");
        assert_eq!(retained, expected_retained);
        assert!(
            replay_limits_after_retained_source(
                &plan,
                &certificate,
                None,
                retained.saturating_sub(1),
            )
            .is_none(),
            "the plan and wire certificate must fit before DAG cloning starts"
        );
        let exact = replay_limits_after_retained_source(&plan, &certificate, None, retained)
            .expect("an exact retained-source budget leaves a zero replay allowance");
        assert_eq!(exact.max_bytes, 0);
    }

    #[test]
    fn session_withholds_checked_point_when_finalization_crosses_deadline() {
        let model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        reset_test_cdcl_invocations();
        set_test_post_solve_delay(std::time::Duration::from_millis(75));
        let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_millis(50));
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(matches!(
            outcome,
            Outcome::Unknown {
                reason: crate::UnknownReason::Timeout
            }
        ));
        assert_eq!(test_cdcl_invocations(), 0, "no ordinary-CDCL prepass");
        assert_eq!(
            test_bounded_cdcl_invocations(),
            1,
            "point came from one proof-enabled pass"
        );
    }

    #[test]
    fn witness_posture_preserves_explicit_zero_objective_semantics() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        model.set_objective(&[], Sense::Minimize);
        let opts = SolveOpts::new();
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(matches!(
            outcome,
            Outcome::Optimal { ref value, .. } if value.is_zero()
        ));
        assert!(session.replay_claims().is_empty());
    }

    #[test]
    fn full_posture_certifies_an_explicit_zero_objective_from_one_sat_pass() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        model.set_objective(&[], Sense::Minimize);
        reset_test_cdcl_invocations();
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(matches!(
            outcome,
            Outcome::Optimal {
                ref value,
                cert: Some(_),
                ..
            } if value.is_zero()
        ));
        assert_eq!(test_cdcl_invocations(), 0, "no ordinary-CDCL prepass");
        assert_eq!(test_bounded_cdcl_invocations(), 1, "one bounded pass");
    }

    #[test]
    fn full_sat_ayc_round_trip_is_verified_optimality() {
        let source_model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let model_text = gadget_mps(&source_model);
        let parsed = crate::read_mps(&model_text).expect("test gadget MPS parses");
        assert!(parsed.model.has_objective(), "the MPS COST row is explicit");
        let names = parsed.col_names;
        let scale = parsed.obj_scale;
        reset_test_cdcl_invocations();
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(parsed.model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(matches!(&outcome, Outcome::Optimal { cert: Some(_), .. }));
        assert_eq!(test_cdcl_invocations(), 0, "no ordinary-CDCL prepass");
        assert_eq!(test_bounded_cdcl_invocations(), 1, "one bounded pass");

        let wire = emit_session_ayc(&session, &model_text, &names, &scale, &outcome);
        assert!(wire.contains("evidence primal SUCCINCT witness"), "{wire}");
        assert!(wire.contains("evidence dual SUCCINCT optcert"), "{wire}");
        let report = crate::cert_io::check(&wire, &model_text);
        assert_eq!(
            report.status,
            crate::cert_io::CheckStatus::Verified,
            "{report:#?}\n{wire}"
        );
    }

    #[test]
    fn witness_posture_runs_one_proof_enabled_pass_and_exports_checked_rup() {
        // This contradiction is intentionally small enough for a sealed PB
        // proof route to claim. The matching SAT/ReLU engine owns it first and
        // publishes its own model-bound proof instead of paying the unrelated
        // 500 ms PB portfolio cascade.
        let model = gadget(1, &[vec![(0, true)], vec![(0, false)]], EPS, &[]);

        // LANE LEVEL first, so a routing change can never make the rest vacuous.
        assert!(matches!(
            try_solve(&model, None),
            Some(SatReluDecision::Unsat)
        ));
        reset_test_cdcl_invocations();

        let opts = SolveOpts::new();
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(outcome.is_infeasible(), "{outcome:?}");
        assert_eq!(test_cdcl_invocations(), 0, "no ordinary-CDCL prepass");
        assert_eq!(test_bounded_cdcl_invocations(), 1, "one bounded pass");
        assert!(
            session
                .replay_claims()
                .iter()
                .all(|claim| claim.claim != "sat-relu-cnf-unsat"),
            "a checked RUP artifact must replace the old replay handoff: {:?}",
            session.replay_claims()
        );
        let certificate = session
            .sat_relu_infeasibility_certificate()
            .expect("matching UNSAT exports typed resolution evidence");
        verify_infeasibility_certificate(session.model(), certificate, None)
            .expect("session only retains independently replayed evidence");
    }

    #[test]
    fn certificate_required_posture_goes_directly_to_proof_cdcl() {
        let model = gadget(1, &[vec![(0, true)], vec![(0, false)]], EPS, &[]);
        reset_test_cdcl_invocations();
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(
            outcome.is_infeasible(),
            "full posture must retain a verified model-level refutation: {outcome:?}"
        );
        assert_eq!(
            test_cdcl_invocations(),
            0,
            "full posture must not pay an ordinary-CDCL prepass"
        );
        assert_eq!(test_bounded_cdcl_invocations(), 1, "one bounded pass");
        let certificate = session
            .sat_relu_infeasibility_certificate()
            .expect("full posture returns the route's typed proof");
        verify_infeasibility_certificate(session.model(), certificate, None)
            .expect("full-posture proof replays");
        assert!(session
            .replay_claims()
            .iter()
            .all(|claim| claim.claim != "sat-relu-cnf-unsat"));
    }

    #[test]
    fn explicit_budget_below_plan_peak_declines_before_cdcl() {
        let model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let static_plan = prepare(&model, None).expect("static-cap plan");
        let total = static_plan
            .peak_bytes()
            .checked_add(MIN_PROOF_MEMORY_BYTES)
            .and_then(|bytes| bytes.checked_sub(1))
            .expect("small test budget");
        drop(static_plan);

        reset_test_cdcl_invocations();
        assert!(prepare_with_memory_budget(&model, None, Some(total)).is_none());
        assert_eq!(test_cdcl_invocations(), 0);
        assert_eq!(
            test_bounded_cdcl_invocations(),
            0,
            "recognition must reserve the proof minimum before CDCL"
        );
    }

    #[test]
    fn retained_plan_with_insufficient_proof_budget_declines_before_cdcl() {
        let model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let plan = prepare(&model, None).expect("static-cap plan");
        let total = plan
            .retained_bytes()
            .checked_add(plan.exact_scratch_bytes())
            .expect("small exact scratch")
            .checked_add(MIN_PROOF_MEMORY_BYTES - 1)
            .expect("small test budget");
        assert!(
            total >= plan.peak_bytes(),
            "this boundary must isolate the proof allowance from recognition"
        );
        reset_test_cdcl_invocations();
        let deadline = Instant::now() + std::time::Duration::from_secs(5);
        assert!(plan
            .try_solve_with_proof(&model, Some(deadline), Some(total))
            .is_none());
        assert_eq!(test_cdcl_invocations(), 0);
        assert_eq!(
            test_bounded_cdcl_invocations(),
            0,
            "proof preflight must decline before constructing ay-sat"
        );
    }

    #[test]
    fn plan_peak_plus_proof_minimum_succeeds_inside_one_caller_budget() {
        let model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let static_plan = prepare(&model, None).expect("static-cap plan");
        let total = static_plan
            .peak_bytes()
            .checked_add(MIN_PROOF_MEMORY_BYTES)
            .expect("small test budget");
        drop(static_plan);

        let plan = prepare_with_memory_budget(&model, None, Some(total))
            .expect("plan peak plus the proof minimum is admissible");
        let proof_bytes = plan
            .proof_memory_bytes(Some(total))
            .expect("retained plan leaves a proof allowance");
        let deadline = Instant::now() + std::time::Duration::from_secs(5);
        let limits = proof_limits(Some(deadline), proof_bytes).expect("bounded proof limits");
        let pending_bytes = limits
            .max_pending_deletions
            .checked_mul(size_of::<u64>())
            .expect("pending-deletion accounting");
        let solve_phase_bytes = limits
            .max_input_bytes
            .checked_add(limits.max_proof_output_bytes)
            .and_then(|bytes| bytes.checked_add(pending_bytes))
            .and_then(|bytes| bytes.checked_add(limits.max_backward_reconstruction_bytes))
            .expect("solve-phase accounting");
        let parse_replay_phase_bytes = limits
            .max_codec_bytes
            .checked_add(limits.validation.max_bytes)
            .expect("parse/replay accounting");
        for phase_bytes in [solve_phase_bytes, parse_replay_phase_bytes] {
            assert!(phase_bytes <= proof_bytes);
            assert!(
                plan.retained_bytes()
                    .checked_add(plan.exact_scratch_bytes())
                    .and_then(|bytes| bytes.checked_add(phase_bytes))
                    .is_some_and(|bytes| bytes <= total),
                "retained plan, exact scratch, and every proof phase stay within the caller budget"
            );
        }
        assert!(plan.peak_bytes() <= total);
        assert!(plan.sat_completion_bytes <= proof_bytes);
        assert!(
            plan.retained_bytes()
                .checked_add(plan.exact_scratch_bytes())
                .and_then(|bytes| bytes.checked_add(plan.sat_completion_bytes))
                .is_some_and(|bytes| bytes <= total),
            "retained plan, exact scratch, and SAT completion share one caller budget"
        );

        reset_test_cdcl_invocations();
        assert!(matches!(
            plan.try_solve_with_proof(&model, Some(deadline), Some(total)),
            Some(SatReluProofDecision::Sat(_))
        ));
        assert_eq!(test_cdcl_invocations(), 0);
        assert_eq!(test_bounded_cdcl_invocations(), 1);
    }

    #[test]
    fn sat_relu_rup_ayc_round_trip_and_tamper_matrix() {
        let source_model = gadget(
            2,
            &[
                vec![(0, true), (1, true)],
                vec![(0, true), (1, false)],
                vec![(0, false), (1, true)],
                vec![(0, false), (1, false)],
            ],
            0.125,
            &[],
        );
        let model_text = gadget_mps(&source_model);
        let parsed = crate::read_mps(&model_text).expect("test gadget MPS parses");
        assert!(
            prepare(&parsed.model, None).is_some(),
            "MPS model is recognized"
        );
        let names = parsed.col_names;
        let scale = parsed.obj_scale;
        let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs(5));
        let mut session = BabSession::new(parsed.model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(outcome.is_infeasible(), "{outcome:?}");
        let certificate = session
            .sat_relu_infeasibility_certificate()
            .expect("SAT/ReLU proof is retained");
        let ctx = crate::cert_io::EmitCtx {
            model: session.model(),
            model_text: &model_text,
            col_names: &names,
            obj_scale: &scale,
            provenance: "sat-relu-rup-e2e-test",
            replay_claims: session.replay_claims(),
            parity_infeasibility_certificate: session.parity_infeasibility_certificate(),
            affine_aggregation_certificate: None,
            sat_relu_infeasibility_certificate: Some(certificate),
            network_design_infeasibility_certificate: session
                .network_design_infeasibility_certificate(),
            network_design_optimality_certificate: session.network_design_optimality_certificate(),
            block_angular_optimality_certificate: session.block_angular_optimality_certificate(),
            single_machine_scheduling_optimality_certificate: session
                .single_machine_scheduling_optimality_certificate(),
            single_row_dp_infeasibility_certificate: session
                .single_row_dp_infeasibility_certificate(),
            multi_row_bdd_infeasibility_certificate: session
                .multi_row_bdd_infeasibility_certificate(),
            open_domain_single_row_dp_infeasibility_certificate: session
                .open_domain_single_row_dp_infeasibility_certificate(),
            open_domain_multi_row_bdd_infeasibility_certificate: session
                .open_domain_multi_row_bdd_infeasibility_certificate(),
            open_domain_hybrid_pb_lp_infeasibility_certificate: session
                .open_domain_hybrid_pb_lp_infeasibility_certificate(),
            open_domain_hybrid_integer_lift_infeasibility_certificate: session
                .open_domain_hybrid_integer_lift_infeasibility_certificate(),
            hybrid_pb_lp_infeasibility_certificate: session
                .hybrid_pb_lp_infeasibility_certificate(),
            hybrid_integer_lift_infeasibility_certificate: session
                .hybrid_integer_lift_infeasibility_certificate(),
            max_bytes: None,
        };
        let wire = crate::cert_io::emit(&ctx, &outcome);
        assert!(wire.contains("evidence infeasible SUCCINCT sat-relu-rup"));
        assert!(wire.contains("sat-relu-rup format=1"));
        let decoded = crate::cert_io::parse(&wire).expect("typed block parses");
        assert!(decoded.sat_relu_infeasibility.is_some());
        let report = crate::cert_io::check(&wire, &model_text);
        assert_eq!(
            report.status,
            crate::cert_io::CheckStatus::Verified,
            "{report:#?}"
        );
        let mut exact_rescaled = session.model().clone();
        let exact_scale = BigRational::from_integer(
            (num_bigint::BigInt::one() << 80usize) + num_bigint::BigInt::one(),
        );
        for row in 0..exact_rescaled.num_rows() {
            rescale_exact_row(&mut exact_rescaled, row, &exact_scale);
        }
        assert!(
            prepare(&exact_rescaled, None).is_some(),
            "positive exact-only whole-row scaling preserves the SAT projection"
        );
        assert!(matches!(
            verify_infeasibility_certificate(&exact_rescaled, certificate, None),
            Err(SatReluInfeasibilityVerificationError::ModelDigestMismatch)
        ));

        let model_digest = flip_hex_after(&wire, "sat-relu-rup format=1 model=sha256:");
        let cnf_digest = flip_hex_after(&wire, " cnf=sha256:");
        let clause = invalidate_first_nonempty_rup_clause(&wire);
        let hint = invalidate_a_rup_hint(&wire);
        let empty_id = {
            let header = wire
                .lines()
                .find(|line| line.starts_with("sat-relu-rup "))
                .expect("proof header");
            let empty = header
                .split_whitespace()
                .find_map(|token| token.strip_prefix("empty="))
                .expect("empty id");
            reseal_ayc(&wire.replacen(
                &format!(" empty={empty}"),
                &format!(" empty={}", empty.parse::<u64>().expect("id") + 1),
                1,
            ))
        };
        let truncated = reseal_ayc(&wire.replacen("\nend\n", "\n", 1));
        let mislabelled = reseal_ayc(&wire.replacen(
            "evidence infeasible SUCCINCT sat-relu-rup",
            "evidence infeasible SUCCINCT parity-gf2",
            1,
        ));
        for (name, tampered) in [
            ("model digest", model_digest),
            ("CNF digest", cnf_digest),
            ("derived clause", clause),
            ("RUP hint", hint),
            ("empty id", empty_id),
            ("truncated block", truncated),
            ("mislabelled source", mislabelled),
        ] {
            let rejected = crate::cert_io::check(&tampered, &model_text);
            assert_ne!(
                rejected.status,
                crate::cert_io::CheckStatus::Verified,
                "{name} tamper was accepted: {rejected:#?}"
            );
        }

        let mut altered = session.model().clone();
        let row = altered.rows[0].clone();
        let coeffs: Vec<(Col, f64)> = row
            .coeffs
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient))
            .collect();
        altered.set_row(
            altered.row_at(0).expect("row"),
            row.lb + 1.0,
            row.ub + 1.0,
            &coeffs,
        );
        assert!(verify_infeasibility_certificate(&altered, certificate, None).is_err());
    }

    #[test]
    fn malformed_affine_row_is_declined() {
        let mut model = gadget(1, &[vec![(0, true)]], EPS, &[]);
        let row = model.rows[0].clone();
        let coeffs: Vec<(Col, f64)> = row
            .coeffs
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient))
            .collect();
        model.set_row(
            model.row_at(0).expect("row"),
            row.lb + 1.0,
            row.ub + 1.0,
            &coeffs,
        );
        assert!(try_solve(&model, None).is_none());
    }

    #[test]
    fn excessive_outward_padding_is_declined() {
        let model = gadget(1, &[vec![(0, true)]], 0.4, &[]);
        assert!(try_solve(&model, None).is_none());
    }

    #[test]
    fn nonzero_objective_is_declined_but_constant_is_harmless() {
        let mut constant = gadget(1, &[vec![(0, true)]], EPS, &[]);
        constant.set_objective_offset(7.0);
        assert!(matches!(
            try_solve(&constant, None),
            Some(SatReluDecision::Sat(_))
        ));

        let mut linear = gadget(1, &[vec![(0, true)]], EPS, &[]);
        linear.set_objective(&[(linear.col_at(0).expect("input"), 1.0)], Sense::Minimize);
        assert!(try_solve(&linear, None).is_none());
    }
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}
