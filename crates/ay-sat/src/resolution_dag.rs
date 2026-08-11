// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-memory, consumable CDCL refutation for the bit-blasted BV fragment.
//!
//! # Why this module exists
//!
//! `proof_manager.rs` already records the solver's refutation, but it only
//! *emits* it as an LRAT byte stream that is gated behind the file-emission and
//! external-checker authority handshakes (`LearnedLrat*`,
//! `validate_*_main_proof_authority`). There is no public, in-memory accessor
//! that returns the refutation as a resolution/RUP DAG a downstream zero-trust
//! reconstructor (`ay-proof`'s `bv_blast_export`) can replay.
//!
//! This module adds exactly that, **without** touching or weakening the
//! authority-gated LRAT path:
//!
//! * [`prove_unsat_resolution_dag`] drives a fresh [`Solver`] over a CNF with a
//!   plain in-memory LRAT text writer (`ProofOutput::lrat_text(Vec, n)`), solves
//!   it, and on UNSAT parses the emitted LRAT text into a [`ResolutionDag`].
//! * The plain LRAT writer path is the ordinary CDCL proof channel; it is *not*
//!   the `LearnedLrat*` materializer/authority channel, so no handshake is
//!   bypassed — that channel is for theory-lemma materialization and is left
//!   fully intact.
//!
//! # What is surfaced (honest scope)
//!
//! Each derived clause is surfaced as a [`RupStep`] carrying its **positive
//! RUP antecedent clause-ids** — the exact hint chain the LRAT line encodes.
//! This is precisely what a checker needs to re-derive the clause by reverse
//! unit propagation, and what `ay-proof` expands into pairwise resolution.
//!
//! What is deliberately **not** surfaced here (fail-closed):
//! * RAT steps (negative/signed hints): the BV bit-blast fragment is refuted by
//!   pure RUP, so any negative hint makes [`prove_unsat_resolution_dag`] return
//!   [`ResolutionDagError::RatStepUnsupported`] rather than emit something a
//!   pairwise-resolution consumer cannot check.
//! * Clause-deletion provenance and learned-clause materializer provenance:
//!   deletions are dropped (they do not affect soundness of a forward replay),
//!   and the theory-lemma materializer/authority records stay in
//!   `proof_manager.rs` untouched.

use crate::literal::Literal;
use crate::proof::{LratBoundedResourceFailure, ProofOutput};
use crate::resolution_validate::{ResolutionValidationError, ResolutionValidationLimits};
use crate::solver::backward_proof::{
    BackwardProofFailure, BackwardProofLimits, BackwardProofResource,
};
use crate::solver::{SatResult, SatUnknownReason, Solver};
use ay_core::time::Instant;
use std::io::{self, Write};
use std::mem::size_of;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::Arc;

/// One derived clause of the refutation together with the positive RUP
/// antecedent clause-ids the solver used to derive it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RupStep {
    /// LRAT clause id of this derived clause (unique, monotone, `> num_clauses`).
    pub id: u64,
    /// The derived clause literals.
    pub clause: Vec<Literal>,
    /// Positive RUP antecedent clause-ids (the LRAT hint chain), in order.
    pub rup_hints: Vec<u64>,
}

/// A consumable, in-memory CDCL refutation: the original clauses (with their
/// solver-assigned LRAT ids) plus the ordered list of derived RUP steps, the
/// last of which is the empty clause.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolutionDag {
    /// Number of Boolean variables.
    pub num_vars: usize,
    /// Original clauses paired with their LRAT id. Ids are `1..=clauses.len()`
    /// in input order (the LRAT convention the writer uses).
    pub original_clauses: Vec<(u64, Vec<Literal>)>,
    /// Derived clauses in derivation order; the final step is the empty clause.
    pub derived: Vec<RupStep>,
    /// LRAT id of the final (empty) derived clause.
    pub empty_clause_id: u64,
}

/// Failure modes for [`prove_unsat_resolution_dag`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ResolutionDagError {
    /// The CNF was satisfiable; there is no refutation to surface.
    #[error("formula is satisfiable: no refutation")]
    Satisfiable,
    /// The solver returned Unknown (resource limit / interruption).
    #[error("solver returned unknown; no refutation produced")]
    Unknown,
    /// The proof writer could not be recovered or flushed.
    #[error("proof writer unavailable or flush failed")]
    ProofWriterUnavailable,
    /// The emitted LRAT proof was not valid UTF-8 text.
    #[error("emitted LRAT proof is not UTF-8 text")]
    ProofNotUtf8,
    /// An LRAT line could not be parsed.
    #[error("malformed LRAT line: {0}")]
    MalformedLratLine(String),
    /// The proof used a RAT step (signed/negative hint), which this surfacing
    /// path intentionally does not lift (fail-closed; pure-RUP only).
    #[error("proof contains a RAT step (negative hint); not surfaced (RUP-only)")]
    RatStepUnsupported,
    /// The emitted proof did not end in the empty clause.
    #[error("emitted LRAT proof does not derive the empty clause")]
    NoEmptyClause,
}

/// Resource guarded by [`ResolutionProofLimits`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolutionProofResource {
    /// Declared Boolean variables.
    Variables,
    /// Input/original clauses.
    InputClauses,
    /// Literals in the input/original clauses.
    InputLiterals,
    /// Literals in one input clause.
    InputClauseLiterals,
    /// Logical input bytes plus conservative preflight/ingestion scratch.
    InputBytes,
    /// Bytes emitted by the binary LRAT writer.
    ProofOutputBytes,
    /// Parsed derived RUP steps.
    DerivedSteps,
    /// Parsed derived clause literals.
    DerivedLiterals,
    /// Parsed RUP hints.
    Hints,
    /// LRAT deletion IDs waiting to be emitted.
    PendingDeletions,
    /// Binary proof buffer plus materialized DAG bytes.
    CodecBytes,
    /// Retained logical allocation during backward LRAT reconstruction.
    BackwardReconstructionBytes,
    /// Deterministic solver conflicts.
    Conflicts,
    /// Deterministic solver decisions.
    Decisions,
}

/// Phase in which an absolute proof deadline expired.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolutionProofPhase {
    /// Input validation and accounting.
    Preflight,
    /// SAT solving / LRAT production.
    Solve,
    /// Binary LRAT decoding and DAG materialization.
    Parse,
    /// Independent RUP replay.
    Validate,
}

/// Explicit finite limits for production-safe in-memory refutation export.
#[derive(Clone, Debug)]
pub struct ResolutionProofLimits {
    /// Required absolute end-to-end deadline. `None` is rejected by the
    /// bounded APIs because conflict/decision counters do not cover every
    /// restart/control-loop iteration.
    pub deadline: Option<Instant>,
    /// Maximum declared Boolean variables.
    pub max_num_vars: usize,
    /// Maximum input/original clauses.
    pub max_input_clauses: usize,
    /// Maximum literals across all input clauses.
    pub max_input_literals: usize,
    /// Maximum literals in one input clause.
    pub max_input_clause_literals: usize,
    /// Maximum logical input bytes plus conservative per-clause preflight and
    /// ingestion scratch (only one such buffer is live at a time).
    pub max_input_bytes: usize,
    /// Deterministic solver conflict budget and accepted-result cap, or `None`.
    pub max_conflicts: Option<u64>,
    /// Deterministic solver decision budget and accepted-result cap, or `None`.
    /// The solver polls this budget at amortized checkpoints, so execution may
    /// briefly overshoot; an outcome beyond the cap is never returned.
    pub max_decisions: Option<u64>,
    /// Clause-database byte threshold for aggressive learned-clause reduction.
    /// This is not a solver-wide memory ceiling; process-wide enforcement is
    /// the caller's responsibility.
    pub solver_clause_db_reduction_threshold_bytes: usize,
    /// Maximum binary LRAT bytes retained in memory.
    pub max_proof_output_bytes: usize,
    /// Maximum parsed derived steps.
    pub max_derived_steps: usize,
    /// Maximum parsed literals across derived steps.
    pub max_derived_literals: usize,
    /// Maximum parsed hints across derived steps.
    pub max_hints: usize,
    /// Maximum LRAT deletion IDs retained between proof additions.
    pub max_pending_deletions: usize,
    /// Maximum binary buffer plus materialized DAG footprint.
    pub max_codec_bytes: usize,
    /// Maximum retained logical allocation for the deferred backward LRAT
    /// reconstruction pass. Allocator transients and the solver arena require
    /// an external process/RSS envelope.
    pub max_backward_reconstruction_bytes: usize,
    /// Independent replay limits. Its deadline is clamped to the earlier of
    /// this deadline and `validation.deadline`.
    pub validation: ResolutionValidationLimits,
}

impl Default for ResolutionProofLimits {
    fn default() -> Self {
        Self {
            deadline: None,
            max_num_vars: 2_000_000,
            max_input_clauses: 2_000_000,
            max_input_literals: 16_000_000,
            max_input_clause_literals: 60_000,
            max_input_bytes: 256 * 1024 * 1024,
            max_conflicts: Some(5_000_000),
            max_decisions: Some(50_000_000),
            solver_clause_db_reduction_threshold_bytes: 256 * 1024 * 1024,
            max_proof_output_bytes: 256 * 1024 * 1024,
            max_derived_steps: 2_000_000,
            max_derived_literals: 16_000_000,
            max_hints: 32_000_000,
            max_pending_deletions: 2_000_000,
            max_codec_bytes: 768 * 1024 * 1024,
            max_backward_reconstruction_bytes: 256 * 1024 * 1024,
            validation: ResolutionValidationLimits::default(),
        }
    }
}

/// Fail-closed errors from [`prove_unsat_resolution_dag_with_limits`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ResolutionProofError {
    /// A caller-supplied literal names a variable outside the declared range.
    #[error(
        "input clause {clause_index}, literal {literal_index}: variable {var} out of range for {num_vars} variables"
    )]
    InputLiteralOutOfRange {
        /// Input clause index.
        clause_index: usize,
        /// Literal index within the clause.
        literal_index: usize,
        /// Referenced zero-based variable.
        var: usize,
        /// Declared variable count.
        num_vars: usize,
    },
    /// A source clause repeats the exact same literal. The solver normalizes
    /// such clauses, so accepting one would break exact original replay.
    #[error(
        "input clause {clause_index}: literal at index {literal_index} duplicates index {first_index}"
    )]
    DuplicateInputLiteral {
        /// Input clause index.
        clause_index: usize,
        /// Later duplicate position.
        literal_index: usize,
        /// First position carrying the same literal.
        first_index: usize,
    },
    /// No absolute end-to-end deadline was supplied.
    #[error("bounded resolution proof requires an absolute deadline")]
    UnboundedSearch,
    /// A finite producer limit was exceeded.
    #[error("resolution proof {resource:?} limit exceeded: limit {limit}, actual {actual}")]
    LimitExceeded {
        /// Exhausted resource.
        resource: ResolutionProofResource,
        /// Configured limit.
        limit: u128,
        /// Observed or attempted value.
        actual: u128,
    },
    /// Overflow occurred during size or format accounting.
    #[error("resolution proof accounting overflow for {resource:?}")]
    AccountingOverflow {
        /// Resource being accounted.
        resource: ResolutionProofResource,
    },
    /// A fallible proof-buffer or DAG allocation failed.
    #[error("resolution proof allocation failed for {resource:?}")]
    AllocationFailed {
        /// Resource being allocated.
        resource: ResolutionProofResource,
    },
    /// The absolute end-to-end deadline expired.
    #[error("resolution proof deadline exceeded during {phase:?}")]
    DeadlineExceeded {
        /// Phase observing the deadline.
        phase: ResolutionProofPhase,
    },
    /// The formula is satisfiable and therefore has no refutation.
    #[error("formula is satisfiable: no refutation")]
    Satisfiable,
    /// The solver returned Unknown before producing a refutation.
    #[error("solver returned unknown ({reason:?}); no refutation produced")]
    SolverUnknown {
        /// Solver's structured reason, when available.
        reason: Option<SatUnknownReason>,
    },
    /// The proof writer could not be recovered or finalized.
    #[error("proof writer unavailable or finalization failed")]
    ProofWriterUnavailable,
    /// The binary LRAT stream was malformed.
    #[error("malformed binary LRAT at byte {offset}: {detail}")]
    MalformedBinaryProof {
        /// Byte offset at or immediately after the defect.
        offset: usize,
        /// Stable defect classification.
        detail: &'static str,
    },
    /// A RAT step was encountered; this API surfaces pure RUP only.
    #[error("proof contains a RAT step (negative hint); not surfaced (RUP-only)")]
    RatStepUnsupported,
    /// The parsed proof did not terminate in an empty clause.
    #[error("emitted LRAT proof does not derive the empty clause")]
    NoEmptyClause,
    /// The returned DAG did not preserve an input clause byte-for-byte and in
    /// the same position/id namespace.
    #[error("resolution DAG original clause identity mismatch at index {index}")]
    OriginalClauseMismatch {
        /// First mismatching index (or the common prefix length).
        index: usize,
    },
    /// Independent replay rejected the solver-emitted DAG.
    #[error("solver-emitted resolution DAG failed bounded replay: {0}")]
    Validation(#[from] ResolutionValidationError),
}

/// Result of one bounded, proof-capable SAT pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolutionSolveOutcome {
    /// The checked satisfying assignment returned by the solver.
    Sat(Vec<bool>),
    /// An independently replayed pure-RUP refutation.
    Unsat(ResolutionDag),
}

/// Drive a fresh solver over `clauses` (over `num_vars` variables) with an
/// in-memory LRAT writer, and on UNSAT surface the refutation as a
/// [`ResolutionDag`].
///
/// This is the ungated, consumable accessor referenced in the module docs. It
/// uses the ordinary CDCL LRAT channel only; the authority-gated learned-LRAT
/// materializer path in `proof_manager.rs` is not involved.
///
/// # Errors
/// See [`ResolutionDagError`] — notably [`ResolutionDagError::Satisfiable`] when
/// the obligation is SAT (so no bogus refutation is produced) and
/// [`ResolutionDagError::RatStepUnsupported`] when the proof is not pure RUP.
pub fn prove_unsat_resolution_dag(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> Result<ResolutionDag, ResolutionDagError> {
    let mut solver = Solver::with_proof_output(
        num_vars,
        ProofOutput::lrat_text(Vec::<u8>::new(), clauses.len() as u64),
    );
    // This API promises a directly consumable pure-RUP refutation.  Keep its
    // producer on the ordinary CDCL lane: preprocessing can perform
    // equisatisfiable transforms whose trust classification cannot be encoded
    // in LRAT, causing an otherwise valid UNSAT result to fail closed to
    // Unknown (or leaving a hint chain that is not a forward RUP derivation).
    // The formulas served here are already bit-blasted CNF, so preprocessing
    // is neither part of the contract nor required for completeness.
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }

    match solver.solve().into_inner() {
        SatResult::Unsat(_) => {}
        SatResult::Sat(_) => return Err(ResolutionDagError::Satisfiable),
        SatResult::Unknown => return Err(ResolutionDagError::Unknown),
    }

    let writer = solver
        .take_proof_writer()
        .ok_or(ResolutionDagError::ProofWriterUnavailable)?;
    let bytes = writer
        .into_vec()
        .map_err(|_| ResolutionDagError::ProofWriterUnavailable)?;
    let text = String::from_utf8(bytes).map_err(|_| ResolutionDagError::ProofNotUtf8)?;

    let original_clauses: Vec<(u64, Vec<Literal>)> = clauses
        .iter()
        .enumerate()
        .map(|(i, c)| (i as u64 + 1, c.clone()))
        .collect();

    parse_lrat_text_into_dag(num_vars, original_clauses, &text)
}

/// Produce and independently replay a pure-RUP refutation under explicit
/// limits, rejecting a satisfying formula.
pub fn prove_unsat_resolution_dag_with_limits(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
) -> Result<ResolutionDag, ResolutionProofError> {
    match solve_resolution_dag_with_limits(num_vars, clauses, limits)? {
        ResolutionSolveOutcome::Sat(_) => Err(ResolutionProofError::Satisfiable),
        ResolutionSolveOutcome::Unsat(dag) => Ok(dag),
    }
}

/// Solve once under explicit resource limits, returning either the checked SAT
/// assignment or an independently replayed pure-RUP refutation.
///
/// This path emits binary LRAT into a
/// fallibly-growing writer whose retained bytes can never exceed
/// `max_proof_output_bytes`. It preflights the original CNF, forwards absolute
/// wall and deterministic search budgets to the solver, decodes with bounded
/// step/literal/hint/footprint accounting, confirms exact original-clause
/// identity, and finally invokes [`ResolutionDag::validate_with_limits`].
/// Allocator reallocation transients plus solver/proof-manager working state
/// are not included in the retained-byte counters; callers needing a
/// process-wide peak-memory envelope must run the solve under an RSS/process
/// limit.
pub fn solve_resolution_dag_with_limits(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
) -> Result<ResolutionSolveOutcome, ResolutionProofError> {
    preflight_input(num_vars, clauses, limits)?;
    check_deadline(limits.deadline, ResolutionProofPhase::Preflight)?;

    let codec_reserved = original_codec_reservation(clauses, limits.deadline)?;
    enforce_proof_limit(
        ResolutionProofResource::CodecBytes,
        codec_reserved,
        limits.max_codec_bytes,
    )?;
    let codec_writer_allowance = limits.max_codec_bytes - codec_reserved;
    let writer_limit = limits.max_proof_output_bytes.min(codec_writer_allowance);
    let (proof_buffer, proof_handle) = BoundedProofBuffer::new(writer_limit, limits.deadline);
    let proof_output = ProofOutput::lrat_binary_bounded(
        proof_buffer,
        u64::try_from(clauses.len()).map_err(|_| ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::InputClauses,
        })?,
        limits.max_pending_deletions,
        proof_handle.failed_flag(),
    );
    let mut solver = Solver::with_proof_output(num_vars, proof_output);
    solver.set_bounded_in_memory_proof_posture();
    solver.set_backward_proof_limits(BackwardProofLimits {
        deadline: limits.deadline,
        max_steps: limits.max_derived_steps,
        max_literals: limits.max_derived_literals,
        max_hints: limits.max_hints,
        max_bytes: limits.max_backward_reconstruction_bytes,
    });
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    solver.set_solve_deadline(limits.deadline);
    solver.set_conflict_budget(limits.max_conflicts);
    solver.set_decision_budget(limits.max_decisions);
    solver.set_max_clause_db_bytes(Some(limits.solver_clause_db_reduction_threshold_bytes));
    solver.set_interrupt(proof_handle.failed_flag());
    let logical_input_bytes = logical_input_bytes(clauses, limits.deadline)?;
    let mut add_buffer: Vec<Literal> = Vec::new();
    for clause in clauses {
        check_deadline(limits.deadline, ResolutionProofPhase::Solve)?;
        if add_buffer.capacity() < clause.len() {
            let requested_bytes = clause.len().checked_mul(size_of::<Literal>()).ok_or(
                ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::InputBytes,
                },
            )?;
            let requested_peak = logical_input_bytes.checked_add(requested_bytes).ok_or(
                ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::InputBytes,
                },
            )?;
            enforce_proof_limit(
                ResolutionProofResource::InputBytes,
                requested_peak,
                limits.max_input_bytes,
            )?;
            add_buffer
                .try_reserve_exact(clause.len() - add_buffer.len())
                .map_err(|_| ResolutionProofError::AllocationFailed {
                    resource: ResolutionProofResource::InputLiterals,
                })?;
            let actual_bytes = add_buffer
                .capacity()
                .checked_mul(size_of::<Literal>())
                .ok_or(ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::InputBytes,
                })?;
            let actual_peak = logical_input_bytes.checked_add(actual_bytes).ok_or(
                ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::InputBytes,
                },
            )?;
            enforce_proof_limit(
                ResolutionProofResource::InputBytes,
                actual_peak,
                limits.max_input_bytes,
            )?;
        }
        add_buffer.extend_from_slice(clause);
        solver.add_clause_reusing_buffer(&mut add_buffer);
        check_deadline(limits.deadline, ResolutionProofPhase::Solve)?;
    }

    let failed = proof_handle.failed_flag();
    let deadline = limits.deadline;
    let result = solver
        .solve_interruptible_without_artifact(move || {
            failed.load(Ordering::Relaxed) || deadline.is_some_and(|end| Instant::now() >= end)
        })
        .into_inner();
    let unknown_reason = solver.last_unknown_reason();
    let conflicts = solver.num_conflicts();
    let decisions = solver.num_decisions();
    let backward_failure = solver.take_backward_proof_failure();

    let output = solver
        .take_proof_writer_without_artifact()
        .ok_or(ResolutionProofError::ProofWriterUnavailable)?;
    let pending_deletion_failure = output.lrat_bounded_resource_failure();
    let inner_result = output.into_inner();
    drop(solver);

    if let Some(failure) = backward_failure {
        return Err(map_backward_proof_failure(failure));
    }

    if let Some(failure) = proof_handle.failure() {
        return Err(match failure {
            ProofBufferFailure::Limit { attempted } => {
                if writer_limit < limits.max_proof_output_bytes {
                    ResolutionProofError::LimitExceeded {
                        resource: ResolutionProofResource::CodecBytes,
                        limit: limits.max_codec_bytes as u128,
                        actual: codec_reserved.saturating_add(attempted) as u128,
                    }
                } else {
                    ResolutionProofError::LimitExceeded {
                        resource: ResolutionProofResource::ProofOutputBytes,
                        limit: limits.max_proof_output_bytes as u128,
                        actual: attempted as u128,
                    }
                }
            }
            ProofBufferFailure::AccountingOverflow => ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::ProofOutputBytes,
            },
            ProofBufferFailure::Allocation => ResolutionProofError::AllocationFailed {
                resource: ResolutionProofResource::ProofOutputBytes,
            },
            ProofBufferFailure::Deadline => ResolutionProofError::DeadlineExceeded {
                phase: ResolutionProofPhase::Solve,
            },
        });
    }
    if let Some(failure) = pending_deletion_failure {
        return Err(match failure {
            LratBoundedResourceFailure::PendingDeletionLimit { limit, attempted } => {
                ResolutionProofError::LimitExceeded {
                    resource: ResolutionProofResource::PendingDeletions,
                    limit: limit as u128,
                    actual: attempted as u128,
                }
            }
            LratBoundedResourceFailure::PendingDeletionAllocation => {
                ResolutionProofError::AllocationFailed {
                    resource: ResolutionProofResource::PendingDeletions,
                }
            }
        });
    }
    check_deadline(limits.deadline, ResolutionProofPhase::Solve)?;

    // Public solver budgets are polled at documented amortized checkpoints.
    // A result found between decision polls is accepted only if its final
    // counter is still within the caller's hard acceptance cap.
    if let Some(limit) = limits.max_conflicts.filter(|limit| conflicts > *limit) {
        return Err(ResolutionProofError::LimitExceeded {
            resource: ResolutionProofResource::Conflicts,
            limit: u128::from(limit),
            actual: u128::from(conflicts),
        });
    }
    if let Some(limit) = limits.max_decisions.filter(|limit| decisions > *limit) {
        return Err(ResolutionProofError::LimitExceeded {
            resource: ResolutionProofResource::Decisions,
            limit: u128::from(limit),
            actual: u128::from(decisions),
        });
    }

    match result {
        SatResult::Sat(model) => return Ok(ResolutionSolveOutcome::Sat(model)),
        SatResult::Unknown => {
            if limits.deadline.is_some_and(|end| Instant::now() >= end) {
                return Err(ResolutionProofError::DeadlineExceeded {
                    phase: ResolutionProofPhase::Solve,
                });
            }
            if let Some(limit) = limits.max_conflicts.filter(|limit| conflicts >= *limit) {
                return Err(ResolutionProofError::LimitExceeded {
                    resource: ResolutionProofResource::Conflicts,
                    limit: u128::from(limit),
                    actual: u128::from(conflicts),
                });
            }
            if let Some(limit) = limits.max_decisions.filter(|limit| decisions >= *limit) {
                return Err(ResolutionProofError::LimitExceeded {
                    resource: ResolutionProofResource::Decisions,
                    limit: u128::from(limit),
                    actual: u128::from(decisions),
                });
            }
            return Err(ResolutionProofError::SolverUnknown {
                reason: unknown_reason,
            });
        }
        SatResult::Unsat(_) => {}
    }
    let boxed_writer = inner_result.map_err(|_| ResolutionProofError::ProofWriterUnavailable)?;
    let bytes = boxed_writer
        .into_typed::<BoundedProofBuffer>()
        .ok_or(ResolutionProofError::ProofWriterUnavailable)?
        .into_bytes();
    check_deadline(limits.deadline, ResolutionProofPhase::Parse)?;

    let mut codec = CodecMeter::new(bytes.capacity(), limits.max_codec_bytes, limits.deadline)?;
    codec.charge(
        size_of::<ResolutionDag>(),
        ResolutionProofResource::CodecBytes,
    )?;
    let originals = clone_originals_bounded(clauses, &mut codec, limits.deadline)?;
    let dag = parse_binary_lrat_into_dag(num_vars, originals, &bytes, limits, &mut codec)?;
    // Release the encoded stream before validation; validation's independent
    // byte budget accounts only the certificate plus its own scratch.
    drop(bytes);

    if dag.original_clauses.len() != clauses.len() {
        return Err(ResolutionProofError::OriginalClauseMismatch {
            index: dag.original_clauses.len().min(clauses.len()),
        });
    }
    for (index, ((id, actual), expected)) in dag.original_clauses.iter().zip(clauses).enumerate() {
        if index % 1024 == 0 {
            check_deadline(limits.deadline, ResolutionProofPhase::Parse)?;
        }
        let expected_id = u64::try_from(index)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or(ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::InputClauses,
            })?;
        if *id != expected_id || actual != expected {
            return Err(ResolutionProofError::OriginalClauseMismatch { index });
        }
    }
    check_deadline(limits.deadline, ResolutionProofPhase::Parse)?;

    let mut validation_limits = limits.validation.clone();
    validation_limits.deadline = earliest_deadline(limits.deadline, validation_limits.deadline);
    match dag.validate_with_limits(&validation_limits) {
        Ok(()) => {}
        Err(ResolutionValidationError::DeadlineExceeded) => {
            return Err(ResolutionProofError::DeadlineExceeded {
                phase: ResolutionProofPhase::Validate,
            });
        }
        Err(error) => return Err(ResolutionProofError::Validation(error)),
    }
    Ok(ResolutionSolveOutcome::Unsat(dag))
}

fn map_backward_proof_resource(resource: BackwardProofResource) -> ResolutionProofResource {
    match resource {
        BackwardProofResource::Steps => ResolutionProofResource::DerivedSteps,
        BackwardProofResource::Literals => ResolutionProofResource::DerivedLiterals,
        BackwardProofResource::Hints => ResolutionProofResource::Hints,
        BackwardProofResource::Visited
        | BackwardProofResource::Queue
        | BackwardProofResource::Seed
        | BackwardProofResource::Bytes
        | BackwardProofResource::ClauseIds => ResolutionProofResource::BackwardReconstructionBytes,
    }
}

fn map_backward_proof_failure(failure: BackwardProofFailure) -> ResolutionProofError {
    match failure {
        BackwardProofFailure::Deadline => ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Solve,
        },
        BackwardProofFailure::Limit {
            resource,
            limit,
            actual,
        } => ResolutionProofError::LimitExceeded {
            resource: map_backward_proof_resource(resource),
            limit: limit as u128,
            actual: actual as u128,
        },
        BackwardProofFailure::AccountingOverflow { resource } => {
            ResolutionProofError::AccountingOverflow {
                resource: map_backward_proof_resource(resource),
            }
        }
        BackwardProofFailure::Allocation { resource } => ResolutionProofError::AllocationFailed {
            resource: map_backward_proof_resource(resource),
        },
    }
}

fn earliest_deadline(lhs: Option<Instant>, rhs: Option<Instant>) -> Option<Instant> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
        (Some(deadline), None) | (None, Some(deadline)) => Some(deadline),
        (None, None) => None,
    }
}

fn check_deadline(
    deadline: Option<Instant>,
    phase: ResolutionProofPhase,
) -> Result<(), ResolutionProofError> {
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(ResolutionProofError::DeadlineExceeded { phase });
    }
    Ok(())
}

fn enforce_proof_limit(
    resource: ResolutionProofResource,
    actual: usize,
    limit: usize,
) -> Result<(), ResolutionProofError> {
    if actual > limit {
        return Err(ResolutionProofError::LimitExceeded {
            resource,
            limit: limit as u128,
            actual: actual as u128,
        });
    }
    Ok(())
}

fn preflight_input(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
) -> Result<(), ResolutionProofError> {
    if limits.deadline.is_none() {
        return Err(ResolutionProofError::UnboundedSearch);
    }
    enforce_proof_limit(
        ResolutionProofResource::Variables,
        num_vars,
        limits.max_num_vars.min(i32::MAX as usize),
    )?;
    enforce_proof_limit(
        ResolutionProofResource::InputClauses,
        clauses.len(),
        limits.max_input_clauses,
    )?;
    if clauses.len() as u128 > u128::from(crate::proof::MAX_LRAT_ORIGINAL_CLAUSES) {
        return Err(ResolutionProofError::LimitExceeded {
            resource: ResolutionProofResource::InputClauses,
            limit: u128::from(crate::proof::MAX_LRAT_ORIGINAL_CLAUSES),
            actual: clauses.len() as u128,
        });
    }

    let mut total_literals = 0usize;
    for (clause_index, clause) in clauses.iter().enumerate() {
        if clause_index % 1024 == 0 {
            check_deadline(limits.deadline, ResolutionProofPhase::Preflight)?;
        }
        enforce_proof_limit(
            ResolutionProofResource::InputClauseLiterals,
            clause.len(),
            limits.max_input_clause_literals.min(60_000),
        )?;
        total_literals = total_literals.checked_add(clause.len()).ok_or(
            ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::InputLiterals,
            },
        )?;
        enforce_proof_limit(
            ResolutionProofResource::InputLiterals,
            total_literals,
            limits.max_input_literals,
        )?;
    }
    let records = clauses.len().checked_mul(size_of::<Vec<Literal>>()).ok_or(
        ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::InputBytes,
        },
    )?;
    let literal_bytes = total_literals.checked_mul(size_of::<Literal>()).ok_or(
        ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::InputBytes,
        },
    )?;
    let input_bytes =
        records
            .checked_add(literal_bytes)
            .ok_or(ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::InputBytes,
            })?;
    enforce_proof_limit(
        ResolutionProofResource::InputBytes,
        input_bytes,
        limits.max_input_bytes,
    )?;

    for (clause_index, clause) in clauses.iter().enumerate() {
        if clause_index % 1024 == 0 {
            check_deadline(limits.deadline, ResolutionProofPhase::Preflight)?;
        }
        let requested_scratch =
            clause
                .len()
                .checked_mul(32)
                .ok_or(ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::InputBytes,
                })?;
        let requested_peak = input_bytes.checked_add(requested_scratch).ok_or(
            ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::InputBytes,
            },
        )?;
        enforce_proof_limit(
            ResolutionProofResource::InputBytes,
            requested_peak,
            limits.max_input_bytes,
        )?;
        let mut seen = std::collections::HashMap::<u32, usize>::new();
        seen.try_reserve(clause.len())
            .map_err(|_| ResolutionProofError::AllocationFailed {
                resource: ResolutionProofResource::InputLiterals,
            })?;
        // `HashMap::capacity` reflects implementation load-factor slack. A
        // conservative 32-byte slot estimate covers `(u32, usize)`, control
        // bytes and alignment. Only one clause map is live at a time.
        let scratch_bytes =
            seen.capacity()
                .checked_mul(32)
                .ok_or(ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::InputBytes,
                })?;
        let peak_input_bytes = input_bytes.checked_add(scratch_bytes).ok_or(
            ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::InputBytes,
            },
        )?;
        enforce_proof_limit(
            ResolutionProofResource::InputBytes,
            peak_input_bytes,
            limits.max_input_bytes,
        )?;
        for (literal_index, literal) in clause.iter().enumerate() {
            if literal_index % 1024 == 0 {
                check_deadline(limits.deadline, ResolutionProofPhase::Preflight)?;
            }
            let var = literal.variable().index();
            if var >= num_vars {
                return Err(ResolutionProofError::InputLiteralOutOfRange {
                    clause_index,
                    literal_index,
                    var,
                    num_vars,
                });
            }
            if let Some(first_index) = seen.insert(literal.raw(), literal_index) {
                return Err(ResolutionProofError::DuplicateInputLiteral {
                    clause_index,
                    literal_index,
                    first_index,
                });
            }
        }
    }
    Ok(())
}

fn logical_input_bytes(
    clauses: &[Vec<Literal>],
    deadline: Option<Instant>,
) -> Result<usize, ResolutionProofError> {
    let mut literals = 0usize;
    for (index, clause) in clauses.iter().enumerate() {
        if index % 1024 == 0 {
            check_deadline(deadline, ResolutionProofPhase::Solve)?;
        }
        literals =
            literals
                .checked_add(clause.len())
                .ok_or(ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::InputBytes,
                })?;
    }
    check_deadline(deadline, ResolutionProofPhase::Solve)?;
    clauses
        .len()
        .checked_mul(size_of::<Vec<Literal>>())
        .and_then(|records| {
            literals
                .checked_mul(size_of::<Literal>())
                .and_then(|literal_bytes| records.checked_add(literal_bytes))
        })
        .ok_or(ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::InputBytes,
        })
}

fn original_codec_reservation(
    clauses: &[Vec<Literal>],
    deadline: Option<Instant>,
) -> Result<usize, ResolutionProofError> {
    let mut literals = 0usize;
    for (index, clause) in clauses.iter().enumerate() {
        if index % 1024 == 0 {
            check_deadline(deadline, ResolutionProofPhase::Preflight)?;
        }
        literals =
            literals
                .checked_add(clause.len())
                .ok_or(ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::CodecBytes,
                })?;
    }
    let original_records = clauses
        .len()
        .checked_mul(size_of::<(u64, Vec<Literal>)>())
        .ok_or(ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::CodecBytes,
        })?;
    let literal_bytes = literals.checked_mul(size_of::<Literal>()).ok_or(
        ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::CodecBytes,
        },
    )?;
    size_of::<ResolutionDag>()
        .checked_add(original_records)
        .and_then(|bytes| bytes.checked_add(literal_bytes))
        .ok_or(ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::CodecBytes,
        })
}

#[derive(Clone, Copy, Debug)]
enum ProofBufferFailure {
    Limit { attempted: usize },
    AccountingOverflow,
    Allocation,
    Deadline,
}

const PROOF_BUFFER_FAILURE_NONE: u8 = 0;
const PROOF_BUFFER_FAILURE_LIMIT: u8 = 1;
const PROOF_BUFFER_FAILURE_OVERFLOW: u8 = 2;
const PROOF_BUFFER_FAILURE_ALLOCATION: u8 = 3;
const PROOF_BUFFER_FAILURE_DEADLINE: u8 = 4;

struct BoundedProofBuffer {
    bytes: Vec<u8>,
    limit: usize,
    failure: Option<ProofBufferFailure>,
    failed: Arc<AtomicBool>,
    shared_failure: Arc<AtomicU8>,
    shared_attempted: Arc<AtomicUsize>,
    deadline: Option<Instant>,
    next_deadline_check: usize,
}

struct BoundedProofBufferHandle {
    failed: Arc<AtomicBool>,
    failure: Arc<AtomicU8>,
    attempted: Arc<AtomicUsize>,
}

impl BoundedProofBuffer {
    fn new(limit: usize, deadline: Option<Instant>) -> (Self, BoundedProofBufferHandle) {
        let failed = Arc::new(AtomicBool::new(false));
        let failure = Arc::new(AtomicU8::new(PROOF_BUFFER_FAILURE_NONE));
        let attempted = Arc::new(AtomicUsize::new(0));
        (
            Self {
                bytes: Vec::new(),
                limit,
                failure: None,
                failed: Arc::clone(&failed),
                shared_failure: Arc::clone(&failure),
                shared_attempted: Arc::clone(&attempted),
                deadline,
                next_deadline_check: 0,
            },
            BoundedProofBufferHandle {
                failed,
                failure,
                attempted,
            },
        )
    }

    fn fail(&mut self, failure: ProofBufferFailure) {
        if self.failure.is_none() {
            self.failure = Some(failure);
            let (kind, attempted) = match failure {
                ProofBufferFailure::Limit { attempted } => (PROOF_BUFFER_FAILURE_LIMIT, attempted),
                ProofBufferFailure::AccountingOverflow => {
                    (PROOF_BUFFER_FAILURE_OVERFLOW, usize::MAX)
                }
                ProofBufferFailure::Allocation => {
                    (PROOF_BUFFER_FAILURE_ALLOCATION, self.bytes.len())
                }
                ProofBufferFailure::Deadline => (PROOF_BUFFER_FAILURE_DEADLINE, self.bytes.len()),
            };
            self.shared_attempted.store(attempted, Ordering::Relaxed);
            self.shared_failure.store(kind, Ordering::Release);
        }
        self.failed.store(true, Ordering::Release);
    }

    fn grow_for(&mut self, required: usize) -> io::Result<()> {
        if required <= self.bytes.capacity() {
            return Ok(());
        }
        let current = self.bytes.capacity();
        let target = if current == 0 {
            4096.min(self.limit)
        } else {
            current.saturating_mul(2).min(self.limit)
        }
        .max(required);
        if self
            .bytes
            .try_reserve_exact(target - self.bytes.len())
            .is_err()
        {
            self.fail(ProofBufferFailure::Allocation);
            return Err(io::Error::other("bounded proof buffer allocation failed"));
        }
        self.check_deadline_now()?;
        if self.bytes.capacity() > self.limit {
            let actual = self.bytes.capacity();
            self.bytes = Vec::new();
            self.fail(ProofBufferFailure::Limit { attempted: actual });
            return Err(io::Error::other(
                "bounded proof buffer allocator exceeded byte cap",
            ));
        }
        Ok(())
    }

    fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    fn check_deadline(&mut self, attempted: usize) -> io::Result<()> {
        if attempted < self.next_deadline_check {
            return Ok(());
        }
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.fail(ProofBufferFailure::Deadline);
            return Err(io::Error::other("bounded proof writer deadline exceeded"));
        }
        self.next_deadline_check = attempted.saturating_add(1024);
        Ok(())
    }

    fn check_deadline_now(&mut self) -> io::Result<()> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.fail(ProofBufferFailure::Deadline);
            return Err(io::Error::other("bounded proof writer deadline exceeded"));
        }
        Ok(())
    }
}

impl Write for BoundedProofBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.failure.is_some() {
            return Err(io::Error::other("bounded proof buffer already failed"));
        }
        let Some(attempted) = self.bytes.len().checked_add(buf.len()) else {
            self.fail(ProofBufferFailure::AccountingOverflow);
            return Err(io::Error::other("bounded proof buffer size overflow"));
        };
        if attempted > self.limit {
            self.fail(ProofBufferFailure::Limit { attempted });
            return Err(io::Error::other("bounded proof buffer byte cap exceeded"));
        }
        self.check_deadline(attempted)?;
        self.grow_for(attempted)?;
        self.bytes.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.check_deadline_now()?;
        if self.failed.load(Ordering::Relaxed) {
            return Err(io::Error::other("bounded proof buffer failed"));
        }
        Ok(())
    }
}

impl BoundedProofBufferHandle {
    fn failed_flag(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.failed)
    }

    fn failure(&self) -> Option<ProofBufferFailure> {
        let kind = self.failure.load(Ordering::Acquire);
        let attempted = self.attempted.load(Ordering::Relaxed);
        match kind {
            PROOF_BUFFER_FAILURE_NONE => None,
            PROOF_BUFFER_FAILURE_LIMIT => Some(ProofBufferFailure::Limit { attempted }),
            PROOF_BUFFER_FAILURE_OVERFLOW => Some(ProofBufferFailure::AccountingOverflow),
            PROOF_BUFFER_FAILURE_ALLOCATION => Some(ProofBufferFailure::Allocation),
            PROOF_BUFFER_FAILURE_DEADLINE => Some(ProofBufferFailure::Deadline),
            _ => Some(ProofBufferFailure::AccountingOverflow),
        }
    }
}

struct CodecMeter {
    used: usize,
    limit: usize,
    deadline: Option<Instant>,
}

impl CodecMeter {
    fn new(
        initial: usize,
        limit: usize,
        deadline: Option<Instant>,
    ) -> Result<Self, ResolutionProofError> {
        enforce_proof_limit(ResolutionProofResource::CodecBytes, initial, limit)?;
        check_deadline(deadline, ResolutionProofPhase::Parse)?;
        Ok(Self {
            used: initial,
            limit,
            deadline,
        })
    }

    fn charge(
        &mut self,
        bytes: usize,
        resource: ResolutionProofResource,
    ) -> Result<(), ResolutionProofError> {
        let attempted = self
            .used
            .checked_add(bytes)
            .ok_or(ResolutionProofError::AccountingOverflow { resource })?;
        if attempted > self.limit {
            return Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::CodecBytes,
                limit: self.limit as u128,
                actual: attempted as u128,
            });
        }
        self.used = attempted;
        Ok(())
    }

    fn reserve_exact<T>(
        &mut self,
        vec: &mut Vec<T>,
        additional: usize,
        allocation_resource: ResolutionProofResource,
    ) -> Result<(), ResolutionProofError> {
        let target =
            vec.len()
                .checked_add(additional)
                .ok_or(ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::CodecBytes,
                })?;
        self.reserve_to(vec, target, allocation_resource)
    }

    fn reserve_to<T>(
        &mut self,
        vec: &mut Vec<T>,
        target: usize,
        allocation_resource: ResolutionProofResource,
    ) -> Result<(), ResolutionProofError> {
        let old_capacity = vec.capacity();
        if target <= old_capacity {
            return Ok(());
        }
        let old_bytes = old_capacity.checked_mul(size_of::<T>()).ok_or(
            ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::CodecBytes,
            },
        )?;
        let target_bytes =
            target
                .checked_mul(size_of::<T>())
                .ok_or(ResolutionProofError::AccountingOverflow {
                    resource: ResolutionProofResource::CodecBytes,
                })?;
        // A reallocating allocator may hold both old and target buffers at
        // once. `used` already includes the old capacity, so precharge the
        // entire target allocation before calling it.
        let transient = self.used.checked_add(target_bytes).ok_or(
            ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::CodecBytes,
            },
        )?;
        enforce_proof_limit(ResolutionProofResource::CodecBytes, transient, self.limit)?;
        if vec.try_reserve_exact(target - vec.len()).is_err() {
            return Err(ResolutionProofError::AllocationFailed {
                resource: allocation_resource,
            });
        }
        check_deadline(self.deadline, ResolutionProofPhase::Parse)?;
        let actual_bytes = vec.capacity().checked_mul(size_of::<T>()).ok_or(
            ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::CodecBytes,
            },
        )?;
        let actual_transient = self.used.checked_add(actual_bytes).ok_or(
            ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::CodecBytes,
            },
        )?;
        if actual_transient > self.limit {
            *vec = Vec::new();
            return Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::CodecBytes,
                limit: self.limit as u128,
                actual: actual_transient as u128,
            });
        }
        self.used = self
            .used
            .checked_sub(old_bytes)
            .and_then(|used| used.checked_add(actual_bytes))
            .ok_or(ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::CodecBytes,
            })?;
        Ok(())
    }

    fn push<T>(
        &mut self,
        vec: &mut Vec<T>,
        value: T,
        allocation_resource: ResolutionProofResource,
    ) -> Result<(), ResolutionProofError> {
        if vec.len() == vec.capacity() {
            let target = if vec.capacity() == 0 {
                4
            } else {
                vec.capacity().saturating_mul(2)
            }
            .max(vec.len().saturating_add(1));
            self.reserve_to(vec, target, allocation_resource)?;
        }
        vec.push(value);
        Ok(())
    }
}

fn clone_originals_bounded(
    clauses: &[Vec<Literal>],
    codec: &mut CodecMeter,
    deadline: Option<Instant>,
) -> Result<Vec<(u64, Vec<Literal>)>, ResolutionProofError> {
    let mut originals = Vec::new();
    codec.reserve_exact(
        &mut originals,
        clauses.len(),
        ResolutionProofResource::InputClauses,
    )?;
    check_deadline(deadline, ResolutionProofPhase::Parse)?;
    for (index, clause) in clauses.iter().enumerate() {
        if index % 1024 == 0 {
            check_deadline(deadline, ResolutionProofPhase::Parse)?;
        }
        let mut copy = Vec::new();
        codec.reserve_exact(
            &mut copy,
            clause.len(),
            ResolutionProofResource::InputLiterals,
        )?;
        copy.extend_from_slice(clause);
        let id = u64::try_from(index)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or(ResolutionProofError::AccountingOverflow {
                resource: ResolutionProofResource::InputClauses,
            })?;
        originals.push((id, copy));
    }
    check_deadline(deadline, ResolutionProofPhase::Parse)?;
    Ok(originals)
}

fn parse_binary_lrat_into_dag(
    num_vars: usize,
    original_clauses: Vec<(u64, Vec<Literal>)>,
    bytes: &[u8],
    limits: &ResolutionProofLimits,
    codec: &mut CodecMeter,
) -> Result<ResolutionDag, ResolutionProofError> {
    let mut position = 0usize;
    let mut derived = Vec::new();
    let mut derived_literals = 0usize;
    let mut hints = 0usize;

    while position < bytes.len() {
        if position.is_multiple_of(1024) {
            check_deadline(limits.deadline, ResolutionProofPhase::Parse)?;
        }
        let marker = bytes[position];
        position += 1;
        match marker {
            b'a' => {
                enforce_proof_limit(
                    ResolutionProofResource::DerivedSteps,
                    derived.len().saturating_add(1),
                    limits.max_derived_steps,
                )?;
                let encoded_id = read_binary_value(bytes, &mut position, limits.deadline)?;
                if encoded_id == 0 || encoded_id & 1 != 0 {
                    return Err(ResolutionProofError::MalformedBinaryProof {
                        offset: position,
                        detail: "addition id is zero or negative",
                    });
                }
                let id = encoded_id / 2;

                let mut clause = Vec::new();
                loop {
                    let encoded = read_binary_value(bytes, &mut position, limits.deadline)?;
                    if encoded == 0 {
                        break;
                    }
                    let magnitude = encoded / 2;
                    if magnitude == 0 || magnitude > i32::MAX as u64 {
                        return Err(ResolutionProofError::MalformedBinaryProof {
                            offset: position,
                            detail: "literal magnitude is outside DIMACS range",
                        });
                    }
                    let var = usize::try_from(magnitude - 1).map_err(|_| {
                        ResolutionProofError::MalformedBinaryProof {
                            offset: position,
                            detail: "literal variable is not representable",
                        }
                    })?;
                    if var >= num_vars {
                        return Err(ResolutionProofError::MalformedBinaryProof {
                            offset: position,
                            detail: "literal variable exceeds declared variable count",
                        });
                    }
                    derived_literals = derived_literals.checked_add(1).ok_or(
                        ResolutionProofError::AccountingOverflow {
                            resource: ResolutionProofResource::DerivedLiterals,
                        },
                    )?;
                    enforce_proof_limit(
                        ResolutionProofResource::DerivedLiterals,
                        derived_literals,
                        limits.max_derived_literals,
                    )?;
                    let variable = crate::literal::Variable::new(var as u32);
                    let literal = if encoded & 1 == 0 {
                        Literal::positive(variable)
                    } else {
                        Literal::negative(variable)
                    };
                    codec.push(
                        &mut clause,
                        literal,
                        ResolutionProofResource::DerivedLiterals,
                    )?;
                }

                let mut rup_hints = Vec::new();
                loop {
                    let encoded = read_binary_value(bytes, &mut position, limits.deadline)?;
                    if encoded == 0 {
                        break;
                    }
                    if encoded & 1 != 0 {
                        return Err(ResolutionProofError::RatStepUnsupported);
                    }
                    let hint = encoded / 2;
                    if hint == 0 {
                        return Err(ResolutionProofError::MalformedBinaryProof {
                            offset: position,
                            detail: "zero hint id",
                        });
                    }
                    hints =
                        hints
                            .checked_add(1)
                            .ok_or(ResolutionProofError::AccountingOverflow {
                                resource: ResolutionProofResource::Hints,
                            })?;
                    enforce_proof_limit(ResolutionProofResource::Hints, hints, limits.max_hints)?;
                    codec.push(&mut rup_hints, hint, ResolutionProofResource::Hints)?;
                }
                codec.push(
                    &mut derived,
                    RupStep {
                        id,
                        clause,
                        rup_hints,
                    },
                    ResolutionProofResource::DerivedSteps,
                )?;
            }
            b'd' => loop {
                let encoded = read_binary_value(bytes, &mut position, limits.deadline)?;
                if encoded == 0 {
                    break;
                }
                if encoded & 1 != 0 || encoded / 2 == 0 {
                    return Err(ResolutionProofError::MalformedBinaryProof {
                        offset: position,
                        detail: "deletion id is zero or negative",
                    });
                }
            },
            _ => {
                return Err(ResolutionProofError::MalformedBinaryProof {
                    offset: position - 1,
                    detail: "unknown LRAT record marker",
                });
            }
        }
    }

    let empty_clause_id = derived
        .last()
        .filter(|step| step.clause.is_empty())
        .map(|step| step.id)
        .ok_or(ResolutionProofError::NoEmptyClause)?;
    Ok(ResolutionDag {
        num_vars,
        original_clauses,
        derived,
        empty_clause_id,
    })
}

fn read_binary_value(
    bytes: &[u8],
    position: &mut usize,
    deadline: Option<Instant>,
) -> Result<u64, ResolutionProofError> {
    let start = *position;
    let start_poll_bucket = start / 1024;
    let mut value = 0u64;
    for byte_index in 0..10u32 {
        let Some(&byte) = bytes.get(*position) else {
            return Err(ResolutionProofError::MalformedBinaryProof {
                offset: *position,
                detail: "truncated variable-length integer",
            });
        };
        *position += 1;
        if *position / 1024 != start_poll_bucket {
            check_deadline(deadline, ResolutionProofPhase::Parse)?;
        }
        let payload = u64::from(byte & 0x7f);
        let shift = byte_index * 7;
        if shift == 63 && payload > 1 {
            return Err(ResolutionProofError::MalformedBinaryProof {
                offset: start,
                detail: "variable-length integer overflow",
            });
        }
        value |= payload << shift;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
    }
    Err(ResolutionProofError::MalformedBinaryProof {
        offset: start,
        detail: "variable-length integer exceeds ten bytes",
    })
}

/// Parse plain-text LRAT into a [`ResolutionDag`].
///
/// The LRAT text grammar this consumes (the subset the writer emits):
///   `<id> <lit>* 0 <hint>* 0`      — clause addition (positive hints only here)
///   `<id> d <delid>* 0`            — clause deletion (dropped)
/// A deletion line is recognised by a `d` token in the first field after the id.
fn parse_lrat_text_into_dag(
    num_vars: usize,
    original_clauses: Vec<(u64, Vec<Literal>)>,
    text: &str,
) -> Result<ResolutionDag, ResolutionDagError> {
    let mut derived: Vec<RupStep> = Vec::new();

    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        let mut toks = line.split_whitespace();
        let id: u64 = toks
            .next()
            .and_then(|t| t.parse().ok())
            .ok_or_else(|| ResolutionDagError::MalformedLratLine(line.to_string()))?;

        // Peek the next token: a literal/`0`, or the deletion marker `d`.
        let mut rest = toks.peekable();
        if rest.peek().copied() == Some("d") {
            // Deletion line: irrelevant to a forward resolution replay; drop it.
            continue;
        }

        // Clause literals up to the terminating 0.
        let mut clause: Vec<Literal> = Vec::new();
        for tok in rest.by_ref() {
            let v: i32 = tok
                .parse()
                .map_err(|_| ResolutionDagError::MalformedLratLine(line.to_string()))?;
            if v == 0 {
                break;
            }
            clause.push(Literal::from_dimacs(v));
        }

        // Hint chain up to the terminating 0. Negative hints = RAT (unsupported).
        let mut rup_hints: Vec<u64> = Vec::new();
        for tok in rest {
            let v: i64 = tok
                .parse()
                .map_err(|_| ResolutionDagError::MalformedLratLine(line.to_string()))?;
            if v == 0 {
                break;
            }
            if v < 0 {
                return Err(ResolutionDagError::RatStepUnsupported);
            }
            rup_hints.push(v as u64);
        }

        derived.push(RupStep {
            id,
            clause,
            rup_hints,
        });
    }

    let empty_clause_id = derived
        .iter()
        .rev()
        .find(|s| s.clause.is_empty())
        .map(|s| s.id)
        .ok_or(ResolutionDagError::NoEmptyClause)?;

    Ok(ResolutionDag {
        num_vars,
        original_clauses,
        derived,
        empty_clause_id,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;
    use crate::resolution_validate::ResolutionDagValidateError;
    use std::time::Duration;

    fn p(i: u32) -> Literal {
        Literal::positive(Variable::new(i))
    }
    fn n(i: u32) -> Literal {
        Literal::negative(Variable::new(i))
    }

    fn grid() -> Vec<Vec<Literal>> {
        vec![
            vec![p(0), p(1)],
            vec![p(0), n(1)],
            vec![n(0), p(1)],
            vec![n(0), n(1)],
        ]
    }

    fn bounded_limits() -> ResolutionProofLimits {
        ResolutionProofLimits {
            deadline: Some(Instant::now() + Duration::from_secs(5)),
            ..ResolutionProofLimits::default()
        }
    }

    #[test]
    fn unsat_two_var_grid_surfaces_rup_dag() {
        let clauses = grid();
        let dag = prove_unsat_resolution_dag(2, &clauses).expect("unsat");
        assert_eq!(dag.original_clauses.len(), 4);
        assert_eq!(dag.original_clauses[0].0, 1);
        // Final derived clause is empty, with positive-only hints throughout.
        assert!(dag.derived.last().expect("steps").clause.is_empty());
        assert_eq!(dag.empty_clause_id, dag.derived.last().unwrap().id);
        for step in &dag.derived {
            assert!(step.id > 4, "derived ids namespaced after originals");
        }
    }

    #[test]
    fn sat_formula_yields_satisfiable_error() {
        let clauses = vec![vec![p(0), p(1)]];
        let err = prove_unsat_resolution_dag(2, &clauses).expect_err("sat");
        assert_eq!(err, ResolutionDagError::Satisfiable);
    }

    #[test]
    fn bounded_api_returns_valid_dag_with_exact_original_identity() {
        let clauses = grid();
        let limits = bounded_limits();
        let dag = prove_unsat_resolution_dag_with_limits(2, &clauses, &limits)
            .expect("bounded refutation");
        assert_eq!(dag.original_clauses.len(), clauses.len());
        for (index, ((id, actual), expected)) in
            dag.original_clauses.iter().zip(&clauses).enumerate()
        {
            assert_eq!(*id, index as u64 + 1);
            assert_eq!(actual, expected);
        }
        dag.validate_with_limits(&limits.validation)
            .expect("independent replay");
    }

    #[test]
    fn bounded_api_preserves_authenticated_original_empty_refutation() {
        let clauses = vec![Vec::new()];
        let limits = bounded_limits();
        let dag = prove_unsat_resolution_dag_with_limits(0, &clauses, &limits)
            .expect("original empty clause is conclusively UNSAT");
        assert_eq!(dag.original_clauses, vec![(1, Vec::new())]);
        assert!(dag
            .derived
            .last()
            .is_some_and(|step| step.clause.is_empty()));
        dag.validate_with_limits(&limits.validation)
            .expect("independent replay of original-empty proof");
    }

    #[test]
    fn bounded_original_empty_fast_path_needs_no_backward_memory_and_need_not_be_last() {
        let clauses = vec![Vec::new(), vec![p(0)]];
        let mut limits = bounded_limits();
        limits.max_backward_reconstruction_bytes = 0;
        let dag = prove_unsat_resolution_dag_with_limits(1, &clauses, &limits)
            .expect("authenticated input-time terminal bypasses reconstruction");
        assert_eq!(dag.original_clauses.len(), 2);
        assert_eq!(dag.original_clauses[0], (1, Vec::new()));
        assert_eq!(dag.original_clauses[1], (2, vec![p(0)]));
        dag.validate_with_limits(&limits.validation)
            .expect("independent replay with zero backward memory");
    }

    #[test]
    fn bounded_api_preserves_authenticated_complementary_units_refutation() {
        let clauses = vec![vec![p(0)], vec![n(0)]];
        let limits = bounded_limits();
        let dag = prove_unsat_resolution_dag_with_limits(1, &clauses, &limits)
            .expect("complementary original units are conclusively UNSAT");
        assert_eq!(dag.original_clauses.len(), 2);
        assert!(dag
            .derived
            .last()
            .is_some_and(|step| step.clause.is_empty()));
        dag.validate_with_limits(&limits.validation)
            .expect("independent replay of complementary-units proof");
    }

    #[test]
    fn bounded_finalization_source_guard_uses_only_direct_emission_funnels() {
        let source = include_str!("solver/solve/finalize_unsat.rs");
        let bounded = source
            .split_once("if let Some(limits) = self.cold.backward_proof_limits.clone() {")
            .expect("bounded finalization branch")
            .1
            .split_once("let backward = self.reconstruct_lrat_backward();")
            .expect("legacy finalization branch")
            .0;
        assert!(bounded.contains("manager.emit_bounded_backward_rup_step("));
        assert!(bounded.contains("mark_empty_clause_with_bounded_prevalidated_hints("));
        assert!(!bounded.contains("manager.emit_backward_step("));
        assert!(!bounded.contains("self.mark_empty_clause_with_hints("));
    }

    #[test]
    fn bounded_level0_conflict_source_guard_defers_before_legacy_allocations() {
        let source = include_str!("solver/conflict_analysis_lrat_specialized.rs");
        let deferred = source
            .find("if self.cold.backward_proof_limits.is_some() {")
            .expect("bounded deferred-conflict branch");
        let conflict_clone = source
            .find("let conflict_lits = self.arena.literals(ci).to_vec();")
            .expect("legacy conflict clone");
        let materialize = source
            .find("self.materialize_level0_unit_proofs();")
            .expect("legacy unit materialization");
        let trace_hash = source
            .find("&det_hash_set_new()")
            .expect("legacy trace HashSet");
        assert!(deferred < materialize);
        assert!(deferred < conflict_clone);
        assert!(deferred < trace_hash);
        let branch = &source[deferred..materialize];
        assert!(branch.contains("self.mark_empty_clause_deferred_for_bounded_proof();"));
        assert!(branch.contains("return;"));
    }

    #[test]
    fn bounded_api_sat_fails_closed() {
        let err = prove_unsat_resolution_dag_with_limits(2, &[vec![p(0), p(1)]], &bounded_limits())
            .expect_err("SAT has no refutation");
        assert_eq!(err, ResolutionProofError::Satisfiable);
    }

    #[test]
    fn single_pass_bounded_api_returns_checked_sat_model() {
        let clauses = vec![vec![p(0)], vec![p(1)]];
        let outcome = solve_resolution_dag_with_limits(2, &clauses, &bounded_limits())
            .expect("bounded SAT solve");
        let ResolutionSolveOutcome::Sat(model) = outcome else {
            panic!("expected SAT outcome");
        };
        assert_eq!(model, vec![true, true]);
    }

    #[test]
    fn bounded_default_requires_caller_owned_absolute_deadline() {
        assert!(matches!(
            solve_resolution_dag_with_limits(0, &[], &ResolutionProofLimits::default()),
            Err(ResolutionProofError::UnboundedSearch)
        ));
    }

    #[test]
    fn bounded_api_expired_deadline_fails_before_allocation() {
        let mut limits = bounded_limits();
        limits.deadline = Some(Instant::now());
        let err = prove_unsat_resolution_dag_with_limits(2, &grid(), &limits)
            .expect_err("expired deadline");
        assert!(matches!(
            err,
            ResolutionProofError::DeadlineExceeded {
                phase: ResolutionProofPhase::Preflight
            }
        ));
    }

    #[test]
    fn bounded_api_proof_byte_cap_is_hard() {
        let mut limits = bounded_limits();
        limits.max_proof_output_bytes = 0;
        let err = prove_unsat_resolution_dag_with_limits(2, &grid(), &limits)
            .expect_err("writer must refuse first byte");
        assert!(matches!(
            err,
            ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::ProofOutputBytes,
                limit: 0,
                ..
            }
        ));
    }

    #[test]
    fn bounded_api_step_literal_and_hint_caps_are_hard() {
        let clauses = grid();
        let baseline = prove_unsat_resolution_dag_with_limits(2, &clauses, &bounded_limits())
            .expect("baseline");
        let baseline_literals: usize = baseline.derived.iter().map(|s| s.clause.len()).sum();
        let baseline_hints: usize = baseline.derived.iter().map(|s| s.rup_hints.len()).sum();
        assert!(!baseline.derived.is_empty());
        assert!(baseline_literals > 0);
        assert!(baseline_hints > 0);

        let mut step_limits = bounded_limits();
        step_limits.max_derived_steps = 0;
        assert!(matches!(
            prove_unsat_resolution_dag_with_limits(2, &clauses, &step_limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::DerivedSteps,
                ..
            })
        ));

        let mut literal_limits = bounded_limits();
        literal_limits.max_derived_literals = baseline_literals - 1;
        assert!(matches!(
            prove_unsat_resolution_dag_with_limits(2, &clauses, &literal_limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::DerivedLiterals,
                ..
            })
        ));

        let mut hint_limits = bounded_limits();
        hint_limits.max_hints = baseline_hints - 1;
        assert!(matches!(
            prove_unsat_resolution_dag_with_limits(2, &clauses, &hint_limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::Hints,
                ..
            })
        ));
    }

    #[test]
    fn bounded_api_input_preflight_is_typed() {
        let mut input_limits = bounded_limits();
        input_limits.max_input_literals = 3;
        assert!(matches!(
            prove_unsat_resolution_dag_with_limits(2, &grid(), &input_limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::InputLiterals,
                ..
            })
        ));

        let mut scratch_limits = bounded_limits();
        scratch_limits.max_input_bytes = size_of::<Vec<Literal>>() + size_of::<Literal>();
        assert!(matches!(
            preflight_input(1, &[vec![p(0)]], &scratch_limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::InputBytes,
                ..
            })
        ));
    }

    #[test]
    fn preflight_enforces_format_boundaries_and_source_identity() {
        let mut limits = bounded_limits();
        limits.max_num_vars = usize::MAX;
        limits.max_input_literals = 100_000;
        limits.max_input_bytes = 16 * 1024 * 1024;
        assert!(preflight_input(i32::MAX as usize, &[], &limits).is_ok());
        assert!(matches!(
            preflight_input(i32::MAX as usize + 1, &[], &limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::Variables,
                ..
            })
        ));

        let boundary: Vec<Literal> = (0..60_000).map(p).collect();
        assert!(preflight_input(60_000, std::slice::from_ref(&boundary), &limits).is_ok());
        let over_boundary: Vec<Literal> = (0..60_001).map(p).collect();
        assert!(matches!(
            preflight_input(60_001, std::slice::from_ref(&over_boundary), &limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::InputClauseLiterals,
                ..
            })
        ));
        assert!(matches!(
            preflight_input(1, &[vec![p(0), p(0)]], &limits),
            Err(ResolutionProofError::DuplicateInputLiteral { .. })
        ));
        assert!(preflight_input(1, &[vec![p(0), n(0)]], &limits).is_ok());
    }

    #[test]
    fn tautological_original_is_preserved_exactly_in_valid_refutation() {
        let clauses = vec![vec![p(0), n(0)], vec![p(0)], vec![n(0)]];
        let dag = prove_unsat_resolution_dag_with_limits(1, &clauses, &bounded_limits())
            .expect("tautological source plus contradictory units");
        let originals: Vec<&Vec<Literal>> = dag
            .original_clauses
            .iter()
            .map(|(_, clause)| clause)
            .collect();
        assert_eq!(originals, clauses.iter().collect::<Vec<_>>());
        dag.validate().expect("valid exact-source refutation");
    }

    #[test]
    fn zero_codec_budget_fails_before_solver_construction() {
        let mut limits = bounded_limits();
        limits.max_codec_bytes = 0;
        assert!(matches!(
            solve_resolution_dag_with_limits(2, &grid(), &limits),
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::CodecBytes,
                limit: 0,
                ..
            })
        ));
    }

    #[test]
    fn bounded_solve_skips_ambient_artifact_hook() {
        Solver::reset_fmla_learned_lrat_dry_run_artifact_hook_calls();
        let _ = solve_resolution_dag_with_limits(2, &grid(), &bounded_limits())
            .expect("bounded refutation");
        assert_eq!(Solver::fmla_learned_lrat_dry_run_artifact_hook_calls(), 0);

        let mut ordinary = Solver::new(1);
        ordinary.add_clause(vec![p(0)]);
        assert!(ordinary.solve().is_sat());
        assert_eq!(Solver::fmla_learned_lrat_dry_run_artifact_hook_calls(), 1);
    }

    #[test]
    fn bounded_proof_posture_skips_startup_walk_only() {
        let mut solver = Solver::new(2);
        assert!(solver.is_walk_enabled());
        assert!(solver.is_startup_walk_enabled());

        solver.set_bounded_in_memory_proof_posture();

        assert!(
            solver.is_walk_enabled(),
            "periodic rephase walk remains enabled"
        );
        assert!(
            !solver.is_startup_walk_enabled(),
            "bounded proof solves must enter complete CDCL without startup walk"
        );
    }

    #[test]
    fn bounded_validation_rejects_tamper_and_resource_exhaustion() {
        let clauses = grid();
        let limits = bounded_limits();
        let dag = prove_unsat_resolution_dag_with_limits(2, &clauses, &limits).expect("baseline");

        let mut step_limits = limits.validation.clone();
        step_limits.max_derived_steps = 0;
        assert!(matches!(
            dag.validate_with_limits(&step_limits),
            Err(ResolutionValidationError::LimitExceeded {
                resource: crate::ResolutionValidationResource::DerivedSteps,
                ..
            })
        ));

        let mut work_limits = limits.validation.clone();
        work_limits.max_work = 0;
        assert!(matches!(
            dag.validate_with_limits(&work_limits),
            Err(ResolutionValidationError::LimitExceeded {
                resource: crate::ResolutionValidationResource::Work,
                ..
            })
        ));

        let mut byte_limits = limits.validation.clone();
        byte_limits.max_bytes = 0;
        assert!(matches!(
            dag.validate_with_limits(&byte_limits),
            Err(ResolutionValidationError::LimitExceeded {
                resource: crate::ResolutionValidationResource::Bytes,
                ..
            })
        ));

        let mut deadline_limits = limits.validation.clone();
        deadline_limits.deadline = Some(Instant::now());
        assert_eq!(
            dag.validate_with_limits(&deadline_limits),
            Err(ResolutionValidationError::DeadlineExceeded)
        );

        let mut tampered = dag;
        tampered.derived.last_mut().expect("empty step").rup_hints = vec![u64::MAX];
        assert!(matches!(
            tampered.validate_with_limits(&limits.validation),
            Err(ResolutionValidationError::Invalid(
                ResolutionDagValidateError::UnknownHint { .. }
            ))
        ));
    }

    #[test]
    fn binary_parser_rejects_malformed_truncated_and_overflow_values() {
        let limits = bounded_limits();
        for bytes in [vec![b'x'], vec![b'a'], {
            let mut bytes = vec![b'a'];
            bytes.extend(std::iter::repeat_n(0xff, 10));
            bytes
        }] {
            let mut codec =
                CodecMeter::new(bytes.capacity(), limits.max_codec_bytes, limits.deadline).unwrap();
            let err = parse_binary_lrat_into_dag(0, Vec::new(), &bytes, &limits, &mut codec)
                .expect_err("malformed proof");
            assert!(matches!(
                err,
                ResolutionProofError::MalformedBinaryProof { .. }
            ));
        }
    }
}
