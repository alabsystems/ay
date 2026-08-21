// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed conversion from a solver [`ClauseTrace`] to a checked RUP DAG.
//!
//! A clause trace uses solver-stable clause ids, while [`ResolutionDag`] uses a
//! canonical namespace: original clauses are numbered `1..=N` and derived
//! clauses follow them.  This module validates the trace namespace before
//! translating it, retains an exact mapping back to each original trace entry,
//! and independently replays the translated positive-RUP proof.
//!
//! This conversion deliberately does **not** assign semantic authority to an
//! entry merely because [`ClauseTraceEntry::is_original`] is set.  A downstream
//! SMT proof publisher must separately authenticate every mapped original.
//!
//! Recorded chains that omit antecedents (typically the root-level reason
//! chains conflict analysis never walks) are independently repaired by three
//! escalating, envelope-metered lanes before replay: candidate compaction, a
//! rooted repair over a one-time root-propagation fixpoint plus a
//! literal-keyed occurrence index, and a full-database cone-trimmed
//! synthesis. Repair only ever widens acceptance — whatever chain is
//! produced is still replayed by the ordinary independent DAG validator.

use std::collections::HashMap;
use std::mem::size_of;

use ay_core::time::Instant;

use crate::clause_trace::{ClauseTrace, ClauseTraceEntry, TraceEntries};
use crate::literal::Literal;
use crate::resolution_dag::{ResolutionDag, RupStep};
use crate::resolution_validate::{
    ResolutionDagValidateError, ResolutionValidationError, ResolutionValidationLimits,
    ResolutionValidationResource,
};

/// Conservative bytes per temporary clause-id hash-table entry.
///
/// This deliberately matches the independent replay's hash-table accounting.
const HASH_ENTRY_BYTES: usize = 64;

/// Long conversion loops poll external controls at least this often.
const CONTROL_POLL_INTERVAL: usize = 1024;

#[derive(Clone, Copy, Debug)]
struct TraceIdState {
    trace_index: usize,
    canonical_id: Option<u64>,
}

#[derive(Clone, Copy, Debug, Default)]
struct TraceShape {
    original_clauses: usize,
    original_literals: usize,
    derived_steps: usize,
    derived_literals: usize,
    hints: usize,
    max_row_hints: usize,
    synthesis_scratch_bytes: usize,
    /// Per-derived-row hint width admitted for independent RUP chain
    /// reconstruction. A row may retain at most
    /// `max(recorded_hints, row_hint_budget)` hints. `0` admits only the
    /// producer's own recorded width, so no reconstruction can widen a row.
    row_hint_budget: usize,
    /// Hint-count slack the whole conversion may spend widening individual
    /// rows past their admitted width: the configured `max_hints` minus the
    /// recorded total the plan already accounts. Consuming it per retained
    /// excess hint keeps the running retained total under the configured
    /// limit even though the widened per-row worst case was not admitted.
    widening_hint_slack: usize,
    /// Byte slack between the admitted plan peaks and `max_bytes`, spent in
    /// lockstep with `widening_hint_slack` (8 bytes per excess hint) so the
    /// final retained-byte enforcement can never trip on a widened row.
    widening_byte_slack: usize,
    source_trace_bytes: usize,
    synthesize_terminal_empty: bool,
}

/// Exact origin of one canonical original clause in a converted trace.
#[derive(Clone, Debug)]
pub struct ClauseTraceOriginalMapping {
    canonical_id: u64,
    trace_index: usize,
    trace_entry: ClauseTraceEntry,
}

impl ClauseTraceOriginalMapping {
    /// Canonical id used by the validated [`ResolutionDag`].
    #[must_use]
    pub fn canonical_id(&self) -> u64 {
        self.canonical_id
    }

    /// Position of the original entry in [`ClauseTrace::entries`].
    #[must_use]
    pub fn trace_index(&self) -> usize {
        self.trace_index
    }

    /// Solver-stable id carried by the original trace entry.
    #[must_use]
    pub fn trace_id(&self) -> u64 {
        self.trace_entry.id
    }

    /// Exact owned snapshot of the original trace entry.
    #[must_use]
    pub fn trace_entry(&self) -> &ClauseTraceEntry {
        &self.trace_entry
    }
}

/// A structurally converted trace whose positive-RUP DAG replay succeeded.
///
/// The fields are private so a caller cannot mutate the DAG while continuing
/// to describe it as validated.  Consuming accessors intentionally transfer
/// the plain data without granting semantic authority to its original clauses.
#[derive(Clone, Debug)]
pub struct ValidatedClauseTraceResolution {
    dag: ResolutionDag,
    original_mappings: Vec<ClauseTraceOriginalMapping>,
    validation_work: u64,
    retained_bytes: usize,
}

/// A structurally converted trace whose positive-RUP replay succeeded under
/// an exact ordered set of fixed unit premises.
///
/// This is deliberately a distinct evidence type: a refutation that depends
/// on `check-sat-assuming` literals must never be detached from those literals
/// and later treated as an assumption-free refutation. The unit premises still
/// carry no semantic authority; a downstream SMT publisher must authenticate
/// each one against the exact authored query assumptions.
#[derive(Clone, Debug)]
pub struct ValidatedPremisedClauseTraceResolution {
    resolution: ValidatedClauseTraceResolution,
    unit_premises: Vec<Literal>,
}

impl ValidatedPremisedClauseTraceResolution {
    /// Borrow the independently replayed canonical DAG.
    #[must_use]
    pub fn dag(&self) -> &ResolutionDag {
        self.resolution.dag()
    }

    /// Borrow mappings for the trace's structural original clauses.
    #[must_use]
    pub fn original_mappings(&self) -> &[ClauseTraceOriginalMapping] {
        self.resolution.original_mappings()
    }

    /// Exact ordered unit literals fixed throughout the successful replay.
    #[must_use]
    pub fn unit_premises(&self) -> &[Literal] {
        &self.unit_premises
    }

    /// Aggregate deterministic conversion and replay work already consumed.
    #[must_use]
    pub fn validation_work(&self) -> u64 {
        self.resolution.validation_work()
    }

    /// Retained source, DAG, mapping, and unit-premise bytes after replay.
    #[must_use]
    pub fn retained_bytes(&self) -> usize {
        self.resolution.retained_bytes()
    }
}

impl ValidatedClauseTraceResolution {
    /// Borrow the independently replayed canonical DAG.
    #[must_use]
    pub fn dag(&self) -> &ResolutionDag {
        &self.dag
    }

    /// Mappings in canonical-original order (`canonical_id == index + 1`).
    #[must_use]
    pub fn original_mappings(&self) -> &[ClauseTraceOriginalMapping] {
        &self.original_mappings
    }

    /// Look up the exact trace origin of one canonical original clause.
    #[must_use]
    pub fn original_mapping(&self, canonical_id: u64) -> Option<&ClauseTraceOriginalMapping> {
        let index: usize = canonical_id.checked_sub(1)?.try_into().ok()?;
        self.original_mappings.get(index)
    }

    /// Deterministic work already consumed by conversion and independent RUP
    /// replay. Downstream certificate composition uses this to continue the
    /// same finite allowance instead of silently starting a fresh budget.
    #[must_use]
    pub fn validation_work(&self) -> u64 {
        self.validation_work
    }

    /// Bytes retained by the live source trace, canonical DAG, and exact
    /// original mapping after replay scratch has been released.
    #[must_use]
    pub fn retained_bytes(&self) -> usize {
        self.retained_bytes
    }

    /// Consume the checked wrapper and return the DAG plus its origin mapping.
    #[must_use]
    pub fn into_parts(self) -> (ResolutionDag, Vec<ClauseTraceOriginalMapping>) {
        (self.dag, self.original_mappings)
    }
}

/// Structural or replay failure while converting a [`ClauseTrace`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ClauseTraceResolutionError {
    /// The trace dropped entries after exceeding its memory budget.
    #[error("clause trace is truncated")]
    Truncated,
    /// Search-time proof bookkeeping exceeded its work budget.
    #[error("clause trace proof bookkeeping was exhausted")]
    ProofWorkExhausted,
    /// The trace carries an UNSAT marker but no recorded derived empty clause.
    #[error("clause trace marks UNSAT without a derived empty-clause entry")]
    EmptyMarkerWithoutDerivedEmpty,
    /// The trace has neither an UNSAT marker nor a derived empty clause.
    #[error("clause trace does not contain a derived empty clause")]
    NoDerivedEmptyClause,
    /// Exact fixed unit premises plus every preceding checked trace clause did
    /// not unit-propagate to a contradiction. The out-of-band UNSAT marker is
    /// therefore insufficient to reconstruct a terminal RUP step.
    #[error("fixed unit premises do not RUP-refute the marker-only clause trace")]
    UnitPremisesDoNotRefuteTrace,
    /// An entry uses the reserved zero clause id.
    #[error("clause trace entry {entry_index} uses reserved clause id zero")]
    ZeroClauseId {
        /// Position of the malformed entry.
        entry_index: usize,
    },
    /// Two trace entries use the same stable clause id.
    #[error("clause trace id {id} is duplicated at entries {first_index} and {duplicate_index}")]
    DuplicateClauseId {
        /// Duplicated solver-stable id.
        id: u64,
        /// Position of the first entry.
        first_index: usize,
        /// Position of the duplicate entry.
        duplicate_index: usize,
    },
    /// An original entry is empty, which would treat UNSAT as an input axiom.
    #[error("original clause trace entry {entry_index} (id {id}) is empty")]
    OriginalEmptyClause {
        /// Position of the malformed entry.
        entry_index: usize,
        /// Solver-stable entry id.
        id: u64,
    },
    /// An original entry unexpectedly carries derivation hints.
    #[error("original clause trace entry {entry_index} (id {id}) carries resolution hints")]
    OriginalHasHints {
        /// Position of the malformed entry.
        entry_index: usize,
        /// Solver-stable entry id.
        id: u64,
    },
    /// A derived addition has no positive RUP hint chain.
    #[error("derived clause trace entry {entry_index} (id {id}) has no resolution hints")]
    UnhintedDerivedClause {
        /// Position of the malformed entry.
        entry_index: usize,
        /// Solver-stable entry id.
        id: u64,
    },
    /// A hint uses the reserved zero clause id.
    #[error("derived clause id {entry_id} at entry {entry_index} contains a zero hint")]
    ZeroHint {
        /// Position of the derived entry.
        entry_index: usize,
        /// Solver-stable derived entry id.
        entry_id: u64,
    },
    /// A hint names no trace entry.
    #[error("derived clause id {entry_id} at entry {entry_index} contains unknown hint {hint_id}")]
    UnknownHint {
        /// Position of the derived entry.
        entry_index: usize,
        /// Solver-stable derived entry id.
        entry_id: u64,
        /// Unknown solver-stable hint id.
        hint_id: u64,
    },
    /// A hint names the current entry or an entry added later in the trace.
    #[error(
        "derived clause id {entry_id} at entry {entry_index} contains non-prior hint {hint_id} from entry {hint_entry_index}"
    )]
    FutureHint {
        /// Position of the derived entry.
        entry_index: usize,
        /// Solver-stable derived entry id.
        entry_id: u64,
        /// Solver-stable hint id.
        hint_id: u64,
        /// Position of the hinted entry.
        hint_entry_index: usize,
    },
    /// The trace contains an entry after its terminal derived empty clause.
    #[error(
        "clause trace entry {entry_index} (id {id}) follows terminal empty clause at entry {empty_entry_index}"
    )]
    EntryAfterTerminalEmpty {
        /// Position of the trailing entry.
        entry_index: usize,
        /// Solver-stable trailing entry id.
        id: u64,
        /// Position of the first derived empty entry.
        empty_entry_index: usize,
    },
    /// Canonical clause-id assignment exceeded `u64`.
    #[error("too many clause trace entries to assign canonical u64 ids")]
    CanonicalIdOverflow,
    /// A checked trace entry was unexpectedly absent from the conversion
    /// namespace. This protects against future refactors that split namespace
    /// validation from canonical-id assignment.
    #[error("clause trace entry {entry_index} (id {id}) lost its checked namespace identity")]
    MissingCheckedIdentity {
        /// Position of the affected entry.
        entry_index: usize,
        /// Solver-stable entry id.
        id: u64,
    },
    /// A fixed unit premise references a variable outside the solver-stamped
    /// Boolean namespace.
    #[error(
        "fixed unit premise {premise_index} references variable {variable} outside namespace 0..{num_vars}"
    )]
    UnitPremiseVariableOutOfRange {
        /// Position in the exact ordered premise slice.
        premise_index: usize,
        /// Out-of-range SAT variable index.
        variable: usize,
        /// Solver-stamped Boolean variable count.
        num_vars: usize,
    },
    /// Trace conversion or canonical-DAG replay exceeded its resource envelope
    /// or failed independent bounded RUP validation.
    #[error(transparent)]
    InvalidResolutionDag(#[from] ResolutionValidationError),
}

fn checked_resource_add(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_add(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

fn checked_resource_mul(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_mul(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

fn enforce_resource(
    resource: ResolutionValidationResource,
    actual: usize,
    limit: usize,
) -> Result<(), ResolutionValidationError> {
    if actual > limit {
        return Err(ResolutionValidationError::LimitExceeded {
            resource,
            limit: limit as u128,
            actual: actual as u128,
        });
    }
    Ok(())
}

struct ConversionMeter<'a> {
    limits: &'a ResolutionValidationLimits,
    should_stop: &'a mut dyn FnMut() -> bool,
    work: u64,
}

impl<'a> ConversionMeter<'a> {
    fn new(
        limits: &'a ResolutionValidationLimits,
        should_stop: &'a mut dyn FnMut() -> bool,
    ) -> Result<Self, ResolutionValidationError> {
        let mut meter = Self {
            limits,
            should_stop,
            work: 0,
        };
        meter.check_controls()?;
        Ok(meter)
    }

    fn check_controls(&mut self) -> Result<(), ResolutionValidationError> {
        if self
            .limits
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(ResolutionValidationError::DeadlineExceeded);
        }
        if (self.should_stop)() {
            return Err(ResolutionValidationError::Cancelled);
        }
        Ok(())
    }

    fn charge(&mut self, amount: usize) -> Result<(), ResolutionValidationError> {
        let amount =
            u64::try_from(amount).map_err(|_| ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            })?;
        let previous = self.work;
        self.work =
            self.work
                .checked_add(amount)
                .ok_or(ResolutionValidationError::AccountingOverflow {
                    resource: ResolutionValidationResource::Work,
                })?;
        if self.work > self.limits.max_work {
            return Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Work,
                limit: u128::from(self.limits.max_work),
                actual: u128::from(self.work),
            });
        }
        if previous / CONTROL_POLL_INTERVAL as u64 != self.work / CONTROL_POLL_INTERVAL as u64 {
            self.check_controls()?;
        }
        Ok(())
    }

    fn consumed_work(&self) -> u64 {
        self.work
    }
}

fn add_count(
    current: usize,
    amount: usize,
    resource: ResolutionValidationResource,
    limit: usize,
) -> Result<usize, ResolutionValidationError> {
    let total = checked_resource_add(current, amount, resource)?;
    enforce_resource(resource, total, limit)?;
    Ok(total)
}

fn planned_dag_bytes(shape: TraceShape) -> Result<usize, ResolutionValidationError> {
    let mut bytes = size_of::<ResolutionDag>();
    bytes = checked_resource_add(
        bytes,
        checked_resource_mul(
            shape.original_clauses,
            size_of::<(u64, Vec<Literal>)>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    bytes = checked_resource_add(
        bytes,
        checked_resource_mul(
            shape.derived_steps,
            size_of::<RupStep>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    bytes = checked_resource_add(
        bytes,
        checked_resource_mul(
            checked_resource_add(
                shape.original_literals,
                shape.derived_literals,
                ResolutionValidationResource::Bytes,
            )?,
            size_of::<Literal>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    checked_resource_add(
        bytes,
        checked_resource_mul(
            shape.hints,
            size_of::<u64>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )
}

fn planned_mapping_bytes(shape: TraceShape) -> Result<usize, ResolutionValidationError> {
    let mut bytes = size_of::<Vec<ClauseTraceOriginalMapping>>();
    bytes = checked_resource_add(
        bytes,
        checked_resource_mul(
            shape.original_clauses,
            size_of::<ClauseTraceOriginalMapping>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    checked_resource_add(
        bytes,
        checked_resource_mul(
            shape.original_literals,
            size_of::<Literal>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )
}

/// One fully costed candidate plan: the shape plus both preflighted phase
/// peaks (conversion retains the id map; replay swaps it for the clause
/// database and assignment/trail scratch).
#[derive(Clone, Copy, Debug)]
struct PlannedPeaks {
    shape: TraceShape,
    conversion: usize,
    replay: usize,
}

/// Retained payload a planned shape converts into: the DAG, the exact original
/// mapping, the caller-owned extras, and the borrowed source trace.
fn planned_retained_bytes(
    shape: TraceShape,
    additional_retained_bytes: usize,
) -> Result<usize, ResolutionValidationError> {
    checked_resource_add(
        checked_resource_add(
            checked_resource_add(
                planned_dag_bytes(shape)?,
                planned_mapping_bytes(shape)?,
                ResolutionValidationResource::Bytes,
            )?,
            additional_retained_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        shape.source_trace_bytes,
        ResolutionValidationResource::Bytes,
    )
}

fn planned_synthesis_scratch_bytes(
    num_vars: usize,
    max_row_hints: usize,
) -> Result<usize, ResolutionValidationError> {
    synthesis_scratch_bytes_from_capacities(
        num_vars,
        max_row_hints,
        max_row_hints,
        max_row_hints,
        num_vars,
    )
}

/// Per-variable propagation bookkeeping retained by cone-trimmed chain
/// reconstruction. Covers both the conversion-scoped root-propagation state
/// (assignment, reason id, order slot and position, cone marks, per-row
/// candidate reasons and trails) and the last-resort full-sweep synthesis
/// scratch (reason id, order slot, cone marker, cone-walk stack). 64 bytes
/// per variable is a deliberate over-approximation of both together.
const PROPAGATION_SCRATCH_BYTES_PER_VAR: usize = 64;

fn synthesis_scratch_bytes_from_capacities(
    assignment_capacity: usize,
    candidate_hint_capacity: usize,
    output_hint_capacity: usize,
    recorded_capacity: usize,
    propagation_scratch_vars: usize,
) -> Result<usize, ResolutionValidationError> {
    let assignment = checked_resource_mul(
        assignment_capacity,
        size_of::<Option<bool>>(),
        ResolutionValidationResource::Bytes,
    )?;
    let propagation = checked_resource_mul(
        propagation_scratch_vars,
        PROPAGATION_SCRATCH_BYTES_PER_VAR,
        ResolutionValidationResource::Bytes,
    )?;
    let candidates = checked_resource_mul(
        candidate_hint_capacity,
        size_of::<u64>(),
        ResolutionValidationResource::Bytes,
    )?;
    let output_hints = checked_resource_mul(
        output_hint_capacity,
        size_of::<u64>(),
        ResolutionValidationResource::Bytes,
    )?;
    let recorded = checked_resource_mul(
        recorded_capacity,
        size_of::<u8>(),
        ResolutionValidationResource::Bytes,
    )?;
    checked_resource_add(
        checked_resource_add(
            checked_resource_add(
                checked_resource_add(assignment, candidates, ResolutionValidationResource::Bytes)?,
                checked_resource_add(output_hints, recorded, ResolutionValidationResource::Bytes)?,
                ResolutionValidationResource::Bytes,
            )?,
            propagation,
            ResolutionValidationResource::Bytes,
        )?,
        checked_resource_mul(7, size_of::<Vec<u8>>(), ResolutionValidationResource::Bytes)?,
        ResolutionValidationResource::Bytes,
    )
}

include!("clause_trace_resolution/preflight.rs");

fn reserve_exact<T>(
    values: &mut Vec<T>,
    count: usize,
    resource: ResolutionValidationResource,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    meter.check_controls()?;
    values
        .try_reserve_exact(count)
        .map_err(|_| ResolutionValidationError::AllocationFailed { resource })?;
    meter.check_controls()
}

fn copy_slice_bounded<T: Copy>(
    values: &[T],
    resource: ResolutionValidationResource,
    meter: &mut ConversionMeter<'_>,
) -> Result<Vec<T>, ResolutionValidationError> {
    let mut copy = Vec::new();
    reserve_exact(&mut copy, values.len(), resource, meter)?;
    for chunk in values.chunks(CONTROL_POLL_INTERVAL) {
        meter.check_controls()?;
        meter.charge(chunk.len())?;
        copy.extend_from_slice(chunk);
    }
    meter.check_controls()?;
    Ok(copy)
}

enum TerminalHintScan {
    Satisfied,
    Open,
    Unit(Literal),
    Conflict,
}

fn scan_terminal_hint_clause(
    clause: &[Literal],
    assign: &[Option<bool>],
    meter: &mut ConversionMeter<'_>,
) -> Result<TerminalHintScan, ResolutionValidationError> {
    meter.charge(1)?;
    let mut unit = None;
    for &literal in clause {
        meter.charge(1)?;
        let variable = literal.variable().index();
        let Some(assigned) = assign.get(variable) else {
            return Err(ResolutionDagValidateError::VarOutOfRange {
                clause: 0,
                var: variable,
                num_vars: assign.len(),
            }
            .into());
        };
        match assigned {
            Some(value) if *value == literal.is_positive() => {
                return Ok(TerminalHintScan::Satisfied);
            }
            Some(_) => {}
            None if unit.is_none() => unit = Some(literal),
            None => return Ok(TerminalHintScan::Open),
        }
    }
    Ok(match unit {
        Some(literal) => TerminalHintScan::Unit(literal),
        None => TerminalHintScan::Conflict,
    })
}

/// Independently reconstruct an ordered positive-RUP chain for a missing
/// terminal empty clause.
///
/// This does not consult the solver's UNSAT marker while deciding whether the
/// contradiction exists. It starts only from the exact fixed unit premises and
/// scans the canonical clause database to a deterministic unit-propagation
/// fixpoint. Every returned id is unit (or the final conflict) under the ids
/// before it, so the ordinary independent DAG validator replays the same chain.
fn synthesize_terminal_empty_hints(
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    fixed_unit_premises: &[Literal],
    num_vars: usize,
    admitted_scratch_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Vec<u64>, ClauseTraceResolutionError> {
    synthesize_rup_hints(
        original_clauses,
        derived,
        &[],
        fixed_unit_premises,
        num_vars,
        original_clauses
            .len()
            .checked_add(derived.len())
            .ok_or(ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Hints,
            })?
            .min(
                num_vars
                    .checked_add(1)
                    .ok_or(ResolutionValidationError::AccountingOverflow {
                        resource: ResolutionValidationResource::Hints,
                    })?,
            ),
        0,
        admitted_scratch_bytes,
        meter,
    )?
    .ok_or(ClauseTraceResolutionError::UnitPremisesDoNotRefuteTrace)
}

include!("clause_trace_resolution/root_propagation.rs");

include!("clause_trace_resolution/rooted_repair.rs");

include!("clause_trace_resolution/synthesis.rs");

fn retained_mapping_bytes(
    mappings: &[ClauseTraceOriginalMapping],
    outer_capacity: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<usize, ResolutionValidationError> {
    let mut bytes = checked_resource_add(
        size_of::<Vec<ClauseTraceOriginalMapping>>(),
        checked_resource_mul(
            outer_capacity,
            size_of::<ClauseTraceOriginalMapping>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    for mapping in mappings {
        meter.charge(1)?;
        bytes = checked_resource_add(
            bytes,
            checked_resource_mul(
                mapping.trace_entry.clause.capacity(),
                size_of::<Literal>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        bytes = checked_resource_add(
            bytes,
            checked_resource_mul(
                mapping.trace_entry.resolution_hints.capacity(),
                size_of::<u64>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
    }
    meter.check_controls()?;
    Ok(bytes)
}

fn retained_dag_bytes(
    dag: &ResolutionDag,
    meter: &mut ConversionMeter<'_>,
) -> Result<usize, ResolutionValidationError> {
    let mut bytes = size_of::<ResolutionDag>();
    bytes = checked_resource_add(
        bytes,
        checked_resource_mul(
            dag.original_clauses.capacity(),
            size_of::<(u64, Vec<Literal>)>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    bytes = checked_resource_add(
        bytes,
        checked_resource_mul(
            dag.derived.capacity(),
            size_of::<RupStep>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    for (_, clause) in &dag.original_clauses {
        meter.charge(1)?;
        bytes = checked_resource_add(
            bytes,
            checked_resource_mul(
                clause.capacity(),
                size_of::<Literal>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
    }
    for step in &dag.derived {
        meter.charge(1)?;
        bytes = checked_resource_add(
            bytes,
            checked_resource_mul(
                step.clause.capacity(),
                size_of::<Literal>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        bytes = checked_resource_add(
            bytes,
            checked_resource_mul(
                step.rup_hints.capacity(),
                size_of::<u64>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
    }
    meter.check_controls()?;
    Ok(bytes)
}

/// Convert a clause trace into a canonical, independently replayed RUP DAG.
///
/// `num_vars` is explicit: inferred bounds could silently authorize a literal
/// outside the Boolean namespace of the solve that produced `trace`.
/// `limits` bound the independent [`ResolutionDag::validate_with_limits`]
/// replay.  The conversion rejects incomplete traces, malformed namespaces,
/// unhinted learned clauses, non-prior hints, and marker-only UNSAT outcomes
/// before constructing the DAG. The exact-premise entry point may instead
/// reconstruct a missing terminal step, but only after independently finding a
/// positive-RUP conflict under those premises.
pub fn validate_clause_trace_resolution(
    trace: &ClauseTrace,
    num_vars: usize,
    limits: &ResolutionValidationLimits,
) -> Result<ValidatedClauseTraceResolution, ClauseTraceResolutionError> {
    validate_clause_trace_resolution_interruptible(trace, num_vars, limits, || false)
}

/// Convert and replay a trace while polling caller-owned cancellation state.
///
/// The predicate is called before every potentially large conversion or replay
/// allocation and periodically inside trace, literal-copy, hint, and replay
/// loops. Returning `true` fails closed with
/// [`ResolutionValidationError::Cancelled`]. The ordinary
/// [`validate_clause_trace_resolution`] API delegates here with a predicate
/// that never cancels.
pub fn validate_clause_trace_resolution_interruptible(
    trace: &ClauseTrace,
    num_vars: usize,
    limits: &ResolutionValidationLimits,
    should_stop: impl FnMut() -> bool,
) -> Result<ValidatedClauseTraceResolution, ClauseTraceResolutionError> {
    validate_clause_trace_resolution_interruptible_impl(trace, num_vars, &[], limits, should_stop)
        .map(|(resolution, unit_premises)| {
            debug_assert!(unit_premises.is_empty());
            resolution
        })
}

/// Convert and replay a trace under exact fixed unit premises while polling
/// caller-owned cancellation state.
///
/// The premises are copied into the returned evidence and fixed throughout
/// every RUP replay. They are not granted semantic authority by this function;
/// a downstream caller must authenticate their cross-layer meaning. Unlike the
/// assumption-free API, a derived step may carry no explicit hints when the
/// fixed units alone make its RUP check contradictory.
pub fn validate_clause_trace_resolution_with_unit_premises_interruptible(
    trace: &ClauseTrace,
    num_vars: usize,
    unit_premises: &[Literal],
    limits: &ResolutionValidationLimits,
    should_stop: impl FnMut() -> bool,
) -> Result<ValidatedPremisedClauseTraceResolution, ClauseTraceResolutionError> {
    let (resolution, unit_premises) = validate_clause_trace_resolution_interruptible_impl(
        trace,
        num_vars,
        unit_premises,
        limits,
        should_stop,
    )?;
    Ok(ValidatedPremisedClauseTraceResolution {
        resolution,
        unit_premises,
    })
}

include!("clause_trace_resolution/validation.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};

    fn pos(var: u32) -> Literal {
        Literal::positive(Variable::new(var))
    }

    fn neg(var: u32) -> Literal {
        Literal::negative(Variable::new(var))
    }

    fn valid_trace() -> ClauseTrace {
        let mut trace = ClauseTrace::new();
        trace.add_clause(40, vec![pos(0)], true);
        trace.add_clause(7, vec![neg(0)], true);
        trace.add_clause_with_hints(90, Vec::new(), false, vec![40, 7]);
        trace
    }

    fn convert(
        trace: &ClauseTrace,
        num_vars: usize,
    ) -> Result<ValidatedClauseTraceResolution, ClauseTraceResolutionError> {
        validate_clause_trace_resolution(trace, num_vars, &ResolutionValidationLimits::unbounded())
    }

    #[test]
    fn canonicalizes_ids_and_retains_exact_original_mapping() {
        let trace = valid_trace();
        let converted = convert(&trace, 1).expect("two contrary units are a valid RUP proof");

        assert_eq!(
            converted.dag().original_clauses,
            vec![(1, vec![pos(0)]), (2, vec![neg(0)])]
        );
        assert_eq!(converted.dag().derived.len(), 1);
        assert_eq!(converted.dag().derived[0].id, 3);
        assert_eq!(converted.dag().derived[0].rup_hints, vec![1, 2]);
        assert_eq!(converted.dag().empty_clause_id, 3);

        let first = converted.original_mapping(1).expect("first mapping");
        assert_eq!(first.canonical_id(), 1);
        assert_eq!(first.trace_index(), 0);
        assert_eq!(first.trace_id(), 40);
        assert_eq!(first.trace_entry().clause, vec![pos(0)]);
        assert!(first.trace_entry().is_original);
        assert!(converted.original_mapping(0).is_none());
        assert!(converted.original_mapping(3).is_none());
    }

    #[test]
    fn rejects_proof_work_exhaustion_and_marker_only_empty() {
        let mut exhausted = valid_trace();
        exhausted.mark_proof_work_exhausted();
        assert_eq!(
            convert(&exhausted, 1).unwrap_err(),
            ClauseTraceResolutionError::ProofWorkExhausted
        );

        let mut marker_only = ClauseTrace::new();
        marker_only.add_clause(1, vec![pos(0)], true);
        marker_only.mark_empty();
        assert_eq!(
            convert(&marker_only, 1).unwrap_err(),
            ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty
        );
    }

    #[test]
    fn rejects_zero_and_duplicate_entry_ids() {
        let mut zero = ClauseTrace::new();
        zero.add_clause(0, vec![pos(0)], true);
        assert!(matches!(
            convert(&zero, 1),
            Err(ClauseTraceResolutionError::ZeroClauseId { entry_index: 0 })
        ));

        let mut duplicate = ClauseTrace::new();
        duplicate.add_clause(4, vec![pos(0)], true);
        duplicate.add_clause(4, vec![neg(0)], true);
        assert!(matches!(
            convert(&duplicate, 1),
            Err(ClauseTraceResolutionError::DuplicateClauseId {
                id: 4,
                first_index: 0,
                duplicate_index: 1
            })
        ));
    }

    #[test]
    fn rejects_zero_unknown_and_future_hints() {
        let mut zero = ClauseTrace::new();
        zero.add_clause(1, vec![pos(0)], true);
        zero.add_clause_with_hints(2, Vec::new(), false, vec![0]);
        assert!(matches!(
            convert(&zero, 1),
            Err(ClauseTraceResolutionError::ZeroHint { .. })
        ));

        let mut unknown = ClauseTrace::new();
        unknown.add_clause(1, vec![pos(0)], true);
        unknown.add_clause_with_hints(2, Vec::new(), false, vec![99]);
        assert!(matches!(
            convert(&unknown, 1),
            Err(ClauseTraceResolutionError::UnknownHint { hint_id: 99, .. })
        ));

        let mut future = ClauseTrace::new();
        future.add_clause(1, vec![pos(0)], true);
        future.add_clause_with_hints(2, vec![pos(0)], false, vec![3]);
        future.add_clause_with_hints(3, Vec::new(), false, vec![1, 2]);
        assert!(matches!(
            convert(&future, 1),
            Err(ClauseTraceResolutionError::FutureHint {
                entry_index: 1,
                hint_id: 3,
                hint_entry_index: 2,
                ..
            })
        ));
    }

    #[test]
    fn rejects_unhinted_or_original_empty_and_steps_after_empty() {
        let mut unhinted = ClauseTrace::new();
        unhinted.add_clause(1, vec![pos(0)], true);
        unhinted.add_clause(2, vec![neg(0)], false);
        assert!(matches!(
            convert(&unhinted, 1),
            Err(ClauseTraceResolutionError::UnhintedDerivedClause { id: 2, .. })
        ));

        let mut original_empty = ClauseTrace::new();
        original_empty.add_clause(1, Vec::new(), true);
        assert!(matches!(
            convert(&original_empty, 0),
            Err(ClauseTraceResolutionError::OriginalEmptyClause { id: 1, .. })
        ));

        let mut trailing = valid_trace();
        trailing.add_clause_with_hints(91, Vec::new(), false, vec![90]);
        assert!(matches!(
            convert(&trailing, 1),
            Err(ClauseTraceResolutionError::EntryAfterTerminalEmpty {
                entry_index: 3,
                empty_entry_index: 2,
                ..
            })
        ));
    }

    #[test]
    fn exact_unit_premises_validate_assumption_dependent_empty_clause() {
        let mut trace = ClauseTrace::new();
        trace.add_clause(11, vec![pos(0)], true);
        trace.add_clause_with_hints(12, Vec::new(), false, vec![11]);

        let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            1,
            &[neg(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect("p together with the fixed unit (not p) derives empty");
        assert_eq!(validated.unit_premises(), &[neg(0)]);
        assert_eq!(validated.original_mappings().len(), 1);
        assert_eq!(validated.dag().derived[0].rup_hints, vec![1]);

        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            1,
            &[pos(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("a satisfied base unit plus the same-polarity premise is not UNSAT");
        assert!(matches!(
            error,
            ClauseTraceResolutionError::InvalidResolutionDag(ResolutionValidationError::Invalid(
                ResolutionDagValidateError::NoConflict { .. }
            ))
        ));
    }

    #[test]
    fn fixed_premise_specialization_skips_only_authenticated_satisfied_hints() {
        // The selector guard (s or a) specializes to (a) under the exact
        // scope premise (not s). The first terminal hint is a derived clause
        // satisfied by that same premise; its raw form has another open
        // literal, so strict assumption-free LRAT would reject it as non-unit.
        // Premised replay must instead treat the satisfied clause as absent
        // from the specialized database, then replay the guarded conflict.
        let mut trace = ClauseTrace::new();
        trace.add_clause(11, vec![pos(0), pos(1)], true);
        trace.add_clause(12, vec![neg(1)], true);
        trace.add_clause_with_hints(13, vec![neg(0), pos(2)], false, Vec::new());
        trace.add_clause_with_hints(14, Vec::new(), false, vec![13, 11, 12]);

        let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            3,
            &[neg(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect("authenticated scope specialization has a checked RUP refutation");
        assert_eq!(validated.unit_premises(), &[neg(0)]);

        let dropped = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            3,
            &[],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("dropping scope authority must fail closed");
        assert!(matches!(
            dropped,
            ClauseTraceResolutionError::UnhintedDerivedClause { id: 13, .. }
        ));

        let flipped = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            3,
            &[pos(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("flipping scope authority must fail closed");
        assert!(matches!(
            flipped,
            ClauseTraceResolutionError::InvalidResolutionDag(ResolutionValidationError::Invalid(
                ResolutionDagValidateError::NoConflict { step: 3 }
            ))
        ));
    }

    #[test]
    fn premised_replay_reconstructs_stale_hint_order_but_not_missing_authority() {
        // Under (not s), (s or a) specializes to a and (not a) conflicts.
        // Hint 3 is a stale non-unit prefix. Conversion must replace the
        // untrusted order with the independently reconstructed [1, 2] chain
        // and retain that checked chain in the returned DAG.
        let mut trace = ClauseTrace::new();
        trace.add_clause(11, vec![pos(0), pos(1)], true);
        trace.add_clause(12, vec![neg(1)], true);
        trace.add_clause(13, vec![neg(2), neg(3), neg(4)], true);
        trace.add_clause_with_hints(14, Vec::new(), false, vec![13, 11, 12]);

        let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            5,
            &[neg(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect("exact prior database has an independently replayable chain");
        assert_eq!(validated.dag().derived[0].rup_hints, vec![1, 2]);

        let missing_premise = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            5,
            &[],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("stale stored hints cannot replace missing premise authority");
        assert!(matches!(
            missing_premise,
            ClauseTraceResolutionError::InvalidResolutionDag(ResolutionValidationError::Invalid(
                ResolutionDagValidateError::HintNotUnit { step: 4, hint: 3 }
            ))
        ));

        let mut missing_prior = ClauseTrace::new();
        missing_prior.add_clause(11, vec![pos(0), pos(1)], true);
        missing_prior.add_clause(13, vec![neg(2), neg(3), neg(4)], true);
        missing_prior.add_clause_with_hints(14, Vec::new(), false, vec![13, 11]);
        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &missing_prior,
            5,
            &[neg(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("removing the required conflicting prior row must fail closed");
        assert!(matches!(
            error,
            ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::Invalid(ResolutionDagValidateError::HintNotUnit {
                    step: 3,
                    hint: 2
                }) | ResolutionValidationError::Invalid(ResolutionDagValidateError::NoConflict {
                    step: 3
                })
            )
        ));
    }

    #[test]
    fn candidate_compaction_revisits_prefix_after_later_units() {
        let originals = vec![
            (1, vec![neg(0), pos(1)]),
            (2, vec![pos(0)]),
            (3, vec![neg(1)]),
        ];
        let mut should_stop = || false;
        let limits = ResolutionValidationLimits::unbounded();
        let mut meter = ConversionMeter::new(&limits, &mut should_stop).expect("meter");
        let admitted_scratch = planned_synthesis_scratch_bytes(3, 3).expect("scratch plan");

        let compacted = compact_rup_hint_candidates(
            &originals,
            &[],
            &[],
            &[neg(2)],
            &[1, 2, 3],
            3,
            3,
            admitted_scratch,
            &mut meter,
        )
        .expect("bounded compaction")
        .expect("later units make the skipped prefix conflicting");
        assert_eq!(compacted, vec![2, 3, 1]);

        let mut should_stop = || false;
        let mut meter = ConversionMeter::new(&limits, &mut should_stop).expect("meter");
        assert_eq!(
            compact_rup_hint_candidates(
                &originals,
                &[],
                &[],
                &[neg(2)],
                &[2, 3],
                2,
                3,
                admitted_scratch,
                &mut meter,
            )
            .expect("bounded negative compaction"),
            None,
            "removing the required conflicting candidate must fail closed"
        );
    }

    #[test]
    fn synthesis_scratch_capacity_growth_exceeds_planned_sub_envelope() {
        let planned = planned_synthesis_scratch_bytes(3, 3).expect("scratch plan");
        let actual =
            synthesis_scratch_bytes_from_capacities(4, 4, 4, 4, 4).expect("actual-capacity census");
        assert!(actual > planned);

        let error = enforce_resource(ResolutionValidationResource::Bytes, actual, planned)
            .expect_err("allocator capacity growth must fail closed");
        assert!(matches!(
            error,
            ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                actual: observed,
                limit,
            } if observed == actual as u128 && limit == planned as u128
        ));
    }

    /// A plain `check-sat` trace whose derived row names only its
    /// conflict-analysis antecedents, omitting the root-level reason clauses
    /// those antecedents propagate through.
    ///
    /// Ids 3 and 4 alone are not a RUP chain for the empty clause: neither is
    /// unit under the empty assignment. The row is nonetheless implied by the
    /// full prior database via 1 and 2. Independent reconstruction must supply
    /// the omitted root antecedents, and the reconstructed chain must be
    /// accepted by the ordinary DAG replay — which `convert` runs.
    fn root_antecedents_omitted_trace() -> ClauseTrace {
        let mut trace = ClauseTrace::new();
        trace.add_clause(10, vec![pos(0)], true);
        trace.add_clause(11, vec![neg(0), neg(1)], true);
        trace.add_clause(12, vec![pos(1), pos(2)], true);
        trace.add_clause(13, vec![pos(1), neg(2)], true);
        trace.add_clause_with_hints(14, Vec::new(), false, vec![12, 13]);
        trace
    }

    #[test]
    fn reconstructs_row_chains_that_omit_root_level_antecedents() {
        let trace = root_antecedents_omitted_trace();
        let converted =
            convert(&trace, 3).expect("the row is RUP from the full prior canonical database");

        let step = converted
            .dag()
            .derived
            .iter()
            .find(|step| step.id == 5)
            .expect("the derived empty row");
        assert!(
            step.rup_hints.len() > 2,
            "the recorded two-hint chain must have been widened by reconstruction, got {:?}",
            step.rup_hints
        );
        assert_eq!(
            step.rup_hints,
            vec![1, 2, 3, 4],
            "reconstruction must emit the propagation-ordered chain including the root antecedents"
        );
        assert_eq!(converted.dag().empty_clause_id, 5);
    }

    /// Narrowness pin: reconstruction repairs an incomplete chain for a row the
    /// database really implies. A row the database does NOT imply must still be
    /// rejected — reconstruction may never invent a derivation.
    #[test]
    fn reconstruction_still_rejects_a_row_the_database_does_not_imply() {
        let mut unimplied = ClauseTrace::new();
        unimplied.add_clause(10, vec![pos(0)], true);
        unimplied.add_clause(11, vec![neg(0), neg(1)], true);
        // `p1` is false in the model {p0 = true, p1 = false}, so no chain exists.
        unimplied.add_clause_with_hints(12, vec![pos(1)], false, vec![10, 11]);
        unimplied.add_clause_with_hints(13, Vec::new(), false, vec![12, 11]);
        assert!(matches!(
            convert(&unimplied, 2),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::Invalid(ResolutionDagValidateError::NoConflict {
                    step: 3
                })
            ))
        ));
    }

    /// The widened plan is admitted before any conversion allocation. When it
    /// does not fit the configured hint envelope it must be declined outright,
    /// leaving the narrower recorded-width posture, never silently exceeded.
    #[test]
    fn declines_the_widened_plan_that_does_not_fit_the_hint_envelope() {
        let trace = root_antecedents_omitted_trace();
        let mut limits = ResolutionValidationLimits::unbounded();
        // Room for the two recorded hints, but not for a reconstructed chain.
        limits.max_hints = 2;
        let error = validate_clause_trace_resolution(&trace, 3, &limits)
            .expect_err("without a widened budget the omitted antecedents stay omitted");
        assert!(
            matches!(
                error,
                ClauseTraceResolutionError::InvalidResolutionDag(
                    ResolutionValidationError::Invalid(
                        ResolutionDagValidateError::NoConflict { step: 5 }
                            | ResolutionDagValidateError::HintNotUnit { step: 5, .. }
                    )
                )
            ),
            "expected a fail-closed replay rejection of the unrepaired row, got {error:?}"
        );
    }

    /// Slack-funded widening under the narrow plan: the widened plan's
    /// worst case (every derived row at full reconstruction width) does not
    /// fit the hint envelope, but the envelope still has unclaimed room past
    /// the recorded total. One under-recorded row must widen into that slack
    /// and the conversion must succeed, with the other row untouched.
    #[test]
    fn widens_one_row_into_unclaimed_hint_slack_under_the_narrow_plan() {
        let mut trace = ClauseTrace::new();
        trace.add_clause(10, vec![pos(0)], true);
        trace.add_clause(11, vec![neg(0), pos(1)], true);
        trace.add_clause(12, vec![neg(1), pos(2)], true);
        trace.add_clause(13, vec![neg(2)], true);
        // Records only its conflicting antecedent; the root chain via 10/11
        // is omitted and must be reconstructed (canonical chain [1, 2, 3]).
        trace.add_clause_with_hints(20, vec![pos(2)], false, vec![12]);
        trace.add_clause_with_hints(21, Vec::new(), false, vec![20, 13]);

        let mut limits = ResolutionValidationLimits::unbounded();
        // Recorded total 3; widened worst case max(1,4) + max(2,4) = 8. Six
        // declines the widened plan and leaves a slack of exactly 3, of which
        // the reconstructed row consumes 2.
        limits.max_hints = 6;
        let converted = validate_clause_trace_resolution(&trace, 3, &limits)
            .expect("the under-recorded row widens into the unclaimed hint slack");
        assert_eq!(converted.dag().derived[0].rup_hints, vec![1, 2, 3]);
        assert_eq!(converted.dag().derived[1].rup_hints, vec![5, 4]);
        assert_eq!(converted.dag().empty_clause_id, 6);
    }

    /// Reconstructed chains are trimmed to the conflict cone: a root unit the
    /// sweep happens to propagate, but that does not support the conflict,
    /// must not appear in the retained chain.
    #[test]
    fn reconstructed_chain_is_trimmed_to_the_conflict_cone() {
        let mut trace = ClauseTrace::new();
        // An unrelated propagating unit, deliberately first in canonical
        // order so the sweep assigns it before the relevant chain.
        trace.add_clause(9, vec![pos(3)], true);
        trace.add_clause(10, vec![pos(0)], true);
        trace.add_clause(11, vec![neg(0), pos(1)], true);
        trace.add_clause(12, vec![neg(1), pos(2)], true);
        trace.add_clause(13, vec![neg(2)], true);
        trace.add_clause_with_hints(20, vec![pos(2)], false, vec![12]);
        trace.add_clause_with_hints(21, Vec::new(), false, vec![20, 13]);

        let converted =
            convert(&trace, 4).expect("the row is RUP from the full prior canonical database");
        assert_eq!(
            converted.dag().derived[0].rup_hints,
            vec![2, 3, 4],
            "the unrelated unit (canonical id 1) must be trimmed from the chain"
        );
    }

    #[test]
    fn premised_reconstruction_bounds_malformed_literals_and_work() {
        let mut malformed = ClauseTrace::new();
        malformed.add_clause(11, vec![pos(0)], true);
        malformed.add_clause_with_hints(12, vec![pos(1)], false, vec![11]);
        malformed.add_clause_with_hints(13, Vec::new(), false, vec![12]);
        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &malformed,
            1,
            &[neg(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("out-of-namespace target must reject instead of indexing scratch");
        assert!(matches!(
            error,
            ClauseTraceResolutionError::InvalidResolutionDag(ResolutionValidationError::Invalid(
                ResolutionDagValidateError::VarOutOfRange {
                    var: 1,
                    num_vars: 1,
                    ..
                }
            ))
        ));

        let mut valid = ClauseTrace::new();
        valid.add_clause(11, vec![pos(0), pos(1)], true);
        valid.add_clause(12, vec![neg(1)], true);
        valid.add_clause(13, vec![neg(2), neg(3), neg(4)], true);
        valid.add_clause_with_hints(14, Vec::new(), false, vec![13, 11, 12]);
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_work = 1;
        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &valid,
            5,
            &[neg(0)],
            &limits,
            || false,
        )
        .expect_err("reconstruction work must remain inside the shared envelope");
        assert!(matches!(
            error,
            ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Work,
                    limit: 1,
                    ..
                }
            )
        ));

        let mut byte_limits = ResolutionValidationLimits::unbounded();
        byte_limits.max_bytes = 1;
        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &valid,
            5,
            &[neg(0)],
            &byte_limits,
            || false,
        )
        .expect_err("row-compaction scratch must be admitted before allocation");
        assert!(matches!(
            error,
            ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Bytes,
                    limit: 1,
                    ..
                }
            )
        ));
    }

    #[test]
    fn marker_only_assumption_conflict_gets_independently_reconstructed_terminal_rup() {
        let mut trace = ClauseTrace::new();
        trace.add_clause(11, vec![pos(0), pos(1)], true);
        trace.add_clause(12, vec![neg(1)], true);
        trace.mark_empty();

        let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            2,
            &[neg(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect("(not p), (p or q), and (not q) have an exact unit refutation");
        assert_eq!(validated.unit_premises(), &[neg(0)]);
        assert_eq!(validated.dag().derived.len(), 1);
        assert!(validated.dag().derived[0].clause.is_empty());
        assert_eq!(validated.dag().derived[0].rup_hints, vec![1, 2]);

        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            2,
            &[pos(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("the marker must not authorize a satisfiable premise set");
        assert_eq!(
            error,
            ClauseTraceResolutionError::UnitPremisesDoNotRefuteTrace
        );

        assert_eq!(
            convert(&trace, 2).unwrap_err(),
            ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty,
            "assumption-free conversion must never borrow synthesized premises"
        );
    }

    #[test]
    fn contradictory_unit_premises_are_a_checked_refutation() {
        let mut trace = ClauseTrace::new();
        trace.add_clause(11, vec![pos(1)], true);
        trace.add_clause_with_hints(12, Vec::new(), false, Vec::new());

        let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            2,
            &[pos(0), neg(0)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect("opposite authenticated units entail the terminal empty clause");
        assert_eq!(validated.unit_premises(), &[pos(0), neg(0)]);
    }

    #[test]
    fn unit_premises_obey_namespace_and_original_limits() {
        let trace = valid_trace();
        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            1,
            &[pos(1)],
            &ResolutionValidationLimits::unbounded(),
            || false,
        )
        .expect_err("a premise outside the stamped namespace must fail closed");
        assert_eq!(
            error,
            ClauseTraceResolutionError::UnitPremiseVariableOutOfRange {
                premise_index: 0,
                variable: 1,
                num_vars: 1,
            }
        );

        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_original_clauses = 2;
        let error = validate_clause_trace_resolution_with_unit_premises_interruptible(
            &trace,
            1,
            &[pos(0)],
            &limits,
            || false,
        )
        .expect_err("fixed units count as authenticated original premises");
        assert!(matches!(
            error,
            ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::OriginalClauses,
                    limit: 2,
                    actual: 3,
                }
            )
        ));
    }

    #[test]
    fn explicit_variable_bound_and_rup_replay_fail_closed() {
        let trace = valid_trace();
        assert!(matches!(
            convert(&trace, 0),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::Invalid(_)
            ))
        ));

        let mut not_rup = ClauseTrace::new();
        not_rup.add_clause(1, vec![pos(0)], true);
        not_rup.add_clause_with_hints(2, Vec::new(), false, vec![1]);
        assert!(matches!(
            convert(&not_rup, 1),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::Invalid(_)
            ))
        ));
    }

    #[test]
    fn expired_deadline_rejects_before_trace_materialization() {
        let trace = valid_trace();
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.deadline = Some(Instant::now());

        assert!(matches!(
            validate_clause_trace_resolution(&trace, 1, &limits),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::DeadlineExceeded
            ))
        ));
    }

    #[test]
    fn count_and_byte_preflight_reject_before_conversion_allocations() {
        let trace = valid_trace();

        let mut count_limits = ResolutionValidationLimits::unbounded();
        count_limits.max_original_clauses = 1;
        assert!(matches!(
            validate_clause_trace_resolution(&trace, 1, &count_limits),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::OriginalClauses,
                    limit: 1,
                    actual: 2,
                }
            ))
        ));

        let mut byte_limits = ResolutionValidationLimits::unbounded();
        byte_limits.max_bytes = 1;
        assert!(matches!(
            validate_clause_trace_resolution(&trace, 1, &byte_limits),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Bytes,
                    limit: 1,
                    ..
                }
            ))
        ));
    }

    #[test]
    fn conversion_and_replay_share_one_work_allowance() {
        let trace = valid_trace();
        let mut limits = ResolutionValidationLimits::unbounded();
        // This exact trace consumes 37 conversion visits, including namespace
        // initialization, both filtered-entry scans, and the retained-capacity
        // census, followed by 12 replay preflight/allocation/initialization
        // visits. If replay received a fresh allowance it would succeed;
        // carrying conversion forward makes the replay's first original-clause
        // visit exceed the envelope.
        limits.max_work = 49;

        assert!(matches!(
            validate_clause_trace_resolution(&trace, 1, &limits),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Work,
                    limit: 49,
                    actual: 50,
                }
            ))
        ));
    }

    #[test]
    fn source_trace_capacity_is_part_of_byte_envelope() {
        let mut trace = ClauseTrace::with_capacity(4096);
        trace.add_clause(40, vec![pos(0)], true);
        trace.add_clause(7, vec![neg(0)], true);
        trace.add_clause_with_hints(90, Vec::new(), false, vec![40, 7]);
        let mut limits = ResolutionValidationLimits::unbounded();
        limits.max_bytes = 1024;

        assert!(matches!(
            validate_clause_trace_resolution(&trace, 1, &limits),
            Err(ClauseTraceResolutionError::InvalidResolutionDag(
                ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Bytes,
                    limit: 1024,
                    ..
                }
            ))
        ));
    }

    #[test]
    fn cooperative_cancellation_rejects_before_conversion_allocations() {
        let trace = valid_trace();
        let mut polls = 0usize;
        let error = validate_clause_trace_resolution_interruptible(
            &trace,
            1,
            &ResolutionValidationLimits::unbounded(),
            || {
                polls += 1;
                polls >= 2
            },
        )
        .expect_err("the caller cancellation predicate must fail closed");

        assert_eq!(
            error,
            ClauseTraceResolutionError::InvalidResolutionDag(ResolutionValidationError::Cancelled)
        );
        assert_eq!(polls, 2);
    }
}
