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

use std::collections::HashMap;
use std::mem::size_of;

use ay_core::time::Instant;

use crate::clause_trace::{ClauseTrace, ClauseTraceEntry};
use crate::literal::Literal;
use crate::resolution_dag::{ResolutionDag, RupStep};
use crate::resolution_validate::{
    ResolutionValidationError, ResolutionValidationLimits, ResolutionValidationResource,
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

fn preflight_trace_shape(
    trace: &ClauseTrace,
    entries: &[ClauseTraceEntry],
    num_vars: usize,
    additional_retained_bytes: usize,
    allow_synthesized_terminal: bool,
    meter: &mut ConversionMeter<'_>,
) -> Result<TraceShape, ResolutionValidationError> {
    meter.check_controls()?;
    let mut shape = TraceShape {
        source_trace_bytes: checked_resource_add(
            size_of::<ClauseTrace>(),
            checked_resource_mul(
                trace.entries_capacity(),
                size_of::<ClauseTraceEntry>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?,
        ..TraceShape::default()
    };
    let mut has_derived_empty = false;
    for (entry_index, entry) in entries.iter().enumerate() {
        if entry_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        if entry.is_original {
            shape.original_clauses = add_count(
                shape.original_clauses,
                1,
                ResolutionValidationResource::OriginalClauses,
                meter.limits.max_original_clauses,
            )?;
            shape.original_literals = add_count(
                shape.original_literals,
                entry.clause.len(),
                ResolutionValidationResource::OriginalLiterals,
                meter.limits.max_original_literals,
            )?;
        } else {
            has_derived_empty |= entry.clause.is_empty();
            shape.derived_steps = add_count(
                shape.derived_steps,
                1,
                ResolutionValidationResource::DerivedSteps,
                meter.limits.max_derived_steps,
            )?;
            shape.derived_literals = add_count(
                shape.derived_literals,
                entry.clause.len(),
                ResolutionValidationResource::DerivedLiterals,
                meter.limits.max_derived_literals,
            )?;
            shape.hints = add_count(
                shape.hints,
                entry.resolution_hints.len(),
                ResolutionValidationResource::Hints,
                meter.limits.max_hints,
            )?;
        }
        shape.source_trace_bytes = checked_resource_add(
            shape.source_trace_bytes,
            checked_resource_mul(
                entry.clause.capacity(),
                size_of::<Literal>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        shape.source_trace_bytes = checked_resource_add(
            shape.source_trace_bytes,
            checked_resource_mul(
                entry.resolution_hints.capacity(),
                size_of::<u64>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        if entry.clause.len() >= CONTROL_POLL_INTERVAL
            || entry.resolution_hints.len() >= CONTROL_POLL_INTERVAL
        {
            meter.check_controls()?;
        }
    }

    // An assumption solve can finish from a conflict against a temporary
    // decision without adding a permanent empty clause to ClauseTrace. The
    // marker alone is never authority. Under exact fixed unit premises the
    // converter may reconstruct one terminal positive-RUP step, but its full
    // worst-case retained shape must be admitted before any conversion
    // allocation. A deterministic unit-propagation chain uses at most one hint
    // per newly assigned variable plus one final conflicting clause, and never
    // more hints than there are preceding clauses.
    if allow_synthesized_terminal && trace.has_empty_clause() && !has_derived_empty {
        shape.synthesize_terminal_empty = true;
        shape.derived_steps = add_count(
            shape.derived_steps,
            1,
            ResolutionValidationResource::DerivedSteps,
            meter.limits.max_derived_steps,
        )?;
        let propagation_and_conflict_bound =
            checked_resource_add(num_vars, 1, ResolutionValidationResource::Hints)?;
        let synthesized_hint_bound = entries.len().min(propagation_and_conflict_bound);
        shape.hints = add_count(
            shape.hints,
            synthesized_hint_bound,
            ResolutionValidationResource::Hints,
            meter.limits.max_hints,
        )?;
    }

    // Reject count/byte envelopes before allocating the namespace map or any
    // duplicate DAG/mapping payload. The two phase peaks are both preflighted:
    // conversion retains the id map, while replay replaces that map with its
    // clause database and assignment/trail scratch.
    let dag_bytes = planned_dag_bytes(shape)?;
    let mapping_bytes = planned_mapping_bytes(shape)?;
    // Hash tables reserve spare buckets to preserve their load factor. Budget
    // a checked 2x bucket envelope before allocation; the actual capacity is
    // measured again after `try_reserve`.
    let namespace_bucket_bound =
        checked_resource_mul(entries.len(), 2, ResolutionValidationResource::Bytes)?;
    let namespace_bytes = checked_resource_mul(
        namespace_bucket_bound,
        HASH_ENTRY_BYTES,
        ResolutionValidationResource::Bytes,
    )?;
    let conversion_peak = checked_resource_add(
        checked_resource_add(
            checked_resource_add(
                checked_resource_add(
                    dag_bytes,
                    mapping_bytes,
                    ResolutionValidationResource::Bytes,
                )?,
                additional_retained_bytes,
                ResolutionValidationResource::Bytes,
            )?,
            shape.source_trace_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        namespace_bytes,
        ResolutionValidationResource::Bytes,
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        conversion_peak,
        meter.limits.max_bytes,
    )?;

    let replay_database_bytes = namespace_bytes;
    let assignment_bytes = checked_resource_mul(
        num_vars,
        checked_resource_add(
            size_of::<Option<bool>>(),
            size_of::<usize>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    let replay_peak = checked_resource_add(
        checked_resource_add(
            checked_resource_add(
                checked_resource_add(
                    checked_resource_add(
                        dag_bytes,
                        mapping_bytes,
                        ResolutionValidationResource::Bytes,
                    )?,
                    additional_retained_bytes,
                    ResolutionValidationResource::Bytes,
                )?,
                shape.source_trace_bytes,
                ResolutionValidationResource::Bytes,
            )?,
            replay_database_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        assignment_bytes,
        ResolutionValidationResource::Bytes,
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        replay_peak,
        meter.limits.max_bytes,
    )?;
    meter.check_controls()?;
    Ok(shape)
}

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
        match assign[literal.variable().index()] {
            Some(value) if value == literal.is_positive() => {
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
    meter: &mut ConversionMeter<'_>,
) -> Result<Vec<u64>, ClauseTraceResolutionError> {
    let mut assign = Vec::new();
    reserve_exact(
        &mut assign,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    while assign.len() < num_vars {
        let chunk = (num_vars - assign.len()).min(CONTROL_POLL_INTERVAL);
        meter.charge(chunk)?;
        assign.resize(assign.len() + chunk, None);
        meter.check_controls()?;
    }

    let clause_count = checked_resource_add(
        original_clauses.len(),
        derived.len(),
        ResolutionValidationResource::Hints,
    )?;
    let propagation_and_conflict_bound =
        checked_resource_add(num_vars, 1, ResolutionValidationResource::Hints)?;
    let hint_capacity = clause_count.min(propagation_and_conflict_bound);
    let mut hints = Vec::new();
    reserve_exact(
        &mut hints,
        hint_capacity,
        ResolutionValidationResource::Hints,
        meter,
    )?;

    for &literal in fixed_unit_premises {
        meter.charge(1)?;
        let variable = literal.variable().index();
        let value = literal.is_positive();
        match assign[variable] {
            None => assign[variable] = Some(value),
            Some(existing) if existing == value => {}
            // The exact premise set refutes itself. The downstream replay has
            // the same fixed-premise conflict rule, so an empty hint chain is
            // a complete independently checked terminal derivation.
            Some(_) => return Ok(hints),
        }
    }

    loop {
        meter.check_controls()?;
        let mut propagated = false;
        let clauses = original_clauses
            .iter()
            .map(|(id, clause)| (*id, clause.as_slice()))
            .chain(derived.iter().map(|step| (step.id, step.clause.as_slice())));
        for (id, clause) in clauses {
            match scan_terminal_hint_clause(clause, &assign, meter)? {
                TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    // Unit scans only return an unassigned literal. Recording
                    // the id before installing it produces the exact ordered
                    // hint sequence consumed by positive-RUP replay.
                    hints.push(id);
                    assign[literal.variable().index()] = Some(literal.is_positive());
                    propagated = true;
                }
                TerminalHintScan::Conflict => {
                    hints.push(id);
                    return Ok(hints);
                }
            }
        }
        if !propagated {
            return Err(ClauseTraceResolutionError::UnitPremisesDoNotRefuteTrace);
        }
    }
}

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

fn validate_clause_trace_resolution_interruptible_impl(
    trace: &ClauseTrace,
    num_vars: usize,
    fixed_unit_premises: &[Literal],
    limits: &ResolutionValidationLimits,
    mut should_stop: impl FnMut() -> bool,
) -> Result<(ValidatedClauseTraceResolution, Vec<Literal>), ClauseTraceResolutionError> {
    let mut meter = ConversionMeter::new(limits, &mut should_stop)?;
    if trace.is_truncated() {
        return Err(ClauseTraceResolutionError::Truncated);
    }
    if trace.proof_work_exhausted() {
        return Err(ClauseTraceResolutionError::ProofWorkExhausted);
    }

    let entries = trace.entries();
    let premise_payload_bytes = checked_resource_mul(
        fixed_unit_premises.len(),
        size_of::<Literal>(),
        ResolutionValidationResource::Bytes,
    )?;
    // The caller-owned premise payload and the returned owned copy coexist
    // throughout conversion and replay.
    let planned_premise_bytes = checked_resource_add(
        size_of::<Vec<Literal>>(),
        checked_resource_mul(
            premise_payload_bytes,
            2,
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    let shape = preflight_trace_shape(
        trace,
        entries,
        num_vars,
        planned_premise_bytes,
        !fixed_unit_premises.is_empty(),
        &mut meter,
    )?;
    enforce_resource(
        ResolutionValidationResource::OriginalClauses,
        checked_resource_add(
            shape.original_clauses,
            fixed_unit_premises.len(),
            ResolutionValidationResource::OriginalClauses,
        )?,
        limits.max_original_clauses,
    )?;
    enforce_resource(
        ResolutionValidationResource::OriginalLiterals,
        checked_resource_add(
            shape.original_literals,
            fixed_unit_premises.len(),
            ResolutionValidationResource::OriginalLiterals,
        )?,
        limits.max_original_literals,
    )?;
    for (premise_index, &premise) in fixed_unit_premises.iter().enumerate() {
        if premise_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        let variable = premise.variable().index();
        if variable >= num_vars {
            return Err(ClauseTraceResolutionError::UnitPremiseVariableOutOfRange {
                premise_index,
                variable,
                num_vars,
            });
        }
    }
    let unit_premises = copy_slice_bounded(
        fixed_unit_premises,
        ResolutionValidationResource::OriginalLiterals,
        &mut meter,
    )?;
    let retained_premise_bytes = checked_resource_add(
        size_of::<Vec<Literal>>(),
        checked_resource_add(
            premise_payload_bytes,
            checked_resource_mul(
                unit_premises.capacity(),
                size_of::<Literal>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        retained_premise_bytes,
        limits.max_bytes,
    )?;

    // The complete count/byte preflight above precedes every conversion
    // allocation. All reserves are fallible and surrounded by cooperative
    // control checks.
    let mut entry_states = HashMap::new();
    meter.check_controls()?;
    // Hash-table reserve initializes its bucket/control-byte namespace before
    // any entry insertion. Charge the same conservative 2x capacity bound used
    // by the byte preflight before entering that allocation.
    meter.charge(checked_resource_mul(
        entries.len(),
        2,
        ResolutionValidationResource::Work,
    )?)?;
    entry_states.try_reserve(entries.len()).map_err(|_| {
        ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::ClauseDatabase,
        }
    })?;
    meter.check_controls()?;
    for (entry_index, entry) in entries.iter().enumerate() {
        if entry_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        if entry.id == 0 {
            return Err(ClauseTraceResolutionError::ZeroClauseId { entry_index });
        }
        if let Some(first) = entry_states.insert(
            entry.id,
            TraceIdState {
                trace_index: entry_index,
                canonical_id: None,
            },
        ) {
            return Err(ClauseTraceResolutionError::DuplicateClauseId {
                id: entry.id,
                first_index: first.trace_index,
                duplicate_index: entry_index,
            });
        }
    }

    let mut terminal_empty_index = None;
    for (entry_index, entry) in entries.iter().enumerate() {
        if entry_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        if let Some(empty_entry_index) = terminal_empty_index {
            return Err(ClauseTraceResolutionError::EntryAfterTerminalEmpty {
                entry_index,
                id: entry.id,
                empty_entry_index,
            });
        }

        if entry.is_original {
            if entry.clause.is_empty() {
                return Err(ClauseTraceResolutionError::OriginalEmptyClause {
                    entry_index,
                    id: entry.id,
                });
            }
            if !entry.resolution_hints.is_empty() {
                return Err(ClauseTraceResolutionError::OriginalHasHints {
                    entry_index,
                    id: entry.id,
                });
            }
            continue;
        }

        if entry.resolution_hints.is_empty() && unit_premises.is_empty() {
            return Err(ClauseTraceResolutionError::UnhintedDerivedClause {
                entry_index,
                id: entry.id,
            });
        }
        for (hint_index, &hint_id) in entry.resolution_hints.iter().enumerate() {
            if hint_index % CONTROL_POLL_INTERVAL == 0 {
                meter.check_controls()?;
            }
            meter.charge(1)?;
            if hint_id == 0 {
                return Err(ClauseTraceResolutionError::ZeroHint {
                    entry_index,
                    entry_id: entry.id,
                });
            }
            let Some(hint_state) = entry_states.get(&hint_id) else {
                return Err(ClauseTraceResolutionError::UnknownHint {
                    entry_index,
                    entry_id: entry.id,
                    hint_id,
                });
            };
            let hint_entry_index = hint_state.trace_index;
            if hint_entry_index >= entry_index {
                return Err(ClauseTraceResolutionError::FutureHint {
                    entry_index,
                    entry_id: entry.id,
                    hint_id,
                    hint_entry_index,
                });
            }
        }

        if entry.clause.is_empty() {
            terminal_empty_index = Some(entry_index);
        }
    }

    if terminal_empty_index.is_none() && !shape.synthesize_terminal_empty {
        return if trace.has_empty_clause() {
            Err(ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty)
        } else {
            Err(ClauseTraceResolutionError::NoDerivedEmptyClause)
        };
    }
    if !trace.has_empty_clause() {
        // Public ClauseTrace mutation keeps this state unreachable, but require
        // both signals so future constructors cannot weaken the contract.
        return Err(ClauseTraceResolutionError::NoDerivedEmptyClause);
    }

    let original_count_u64 = u64::try_from(shape.original_clauses)
        .map_err(|_| ClauseTraceResolutionError::CanonicalIdOverflow)?;
    let mut original_clauses = Vec::new();
    reserve_exact(
        &mut original_clauses,
        shape.original_clauses,
        ResolutionValidationResource::OriginalClauses,
        &mut meter,
    )?;
    let mut original_mappings = Vec::new();
    reserve_exact(
        &mut original_mappings,
        shape.original_clauses,
        ResolutionValidationResource::OriginalClauses,
        &mut meter,
    )?;

    let mut next_canonical_id = 1_u64;
    for (trace_index, entry) in entries.iter().enumerate() {
        // Iterator filtering still visits every trace entry. Charge that scan
        // independently from the selected-entry conversion work below.
        meter.charge(1)?;
        if !entry.is_original {
            continue;
        }
        meter.charge(1)?;
        let canonical_id = next_canonical_id;
        next_canonical_id = next_canonical_id
            .checked_add(1)
            .ok_or(ClauseTraceResolutionError::CanonicalIdOverflow)?;
        let Some(state) = entry_states.get_mut(&entry.id) else {
            return Err(ClauseTraceResolutionError::MissingCheckedIdentity {
                entry_index: trace_index,
                id: entry.id,
            });
        };
        state.canonical_id = Some(canonical_id);
        let dag_clause = copy_slice_bounded(
            &entry.clause,
            ResolutionValidationResource::OriginalLiterals,
            &mut meter,
        )?;
        let mapped_clause = copy_slice_bounded(
            &entry.clause,
            ResolutionValidationResource::OriginalLiterals,
            &mut meter,
        )?;
        original_clauses.push((canonical_id, dag_clause));
        original_mappings.push(ClauseTraceOriginalMapping {
            canonical_id,
            trace_index,
            trace_entry: ClauseTraceEntry::new(entry.id, mapped_clause, true, Vec::new()),
        });
    }

    let expected_first_derived = original_count_u64
        .checked_add(1)
        .ok_or(ClauseTraceResolutionError::CanonicalIdOverflow)?;
    debug_assert_eq!(next_canonical_id, expected_first_derived);
    let mut derived = Vec::new();
    reserve_exact(
        &mut derived,
        shape.derived_steps,
        ResolutionValidationResource::DerivedSteps,
        &mut meter,
    )?;
    let mut empty_clause_id = None;
    for (entry_index, entry) in entries.iter().enumerate() {
        // As above, every predicate visit belongs to the shared allowance.
        meter.charge(1)?;
        if entry.is_original {
            continue;
        }
        meter.charge(1)?;
        let canonical_id = next_canonical_id;
        next_canonical_id = next_canonical_id
            .checked_add(1)
            .ok_or(ClauseTraceResolutionError::CanonicalIdOverflow)?;

        let mut rup_hints = Vec::new();
        reserve_exact(
            &mut rup_hints,
            entry.resolution_hints.len(),
            ResolutionValidationResource::Hints,
            &mut meter,
        )?;
        for (hint_index, &hint_id) in entry.resolution_hints.iter().enumerate() {
            if hint_index % CONTROL_POLL_INTERVAL == 0 {
                meter.check_controls()?;
            }
            meter.charge(1)?;
            let canonical_hint = entry_states
                .get(&hint_id)
                .and_then(|state| state.canonical_id)
                .ok_or(ClauseTraceResolutionError::UnknownHint {
                    entry_index,
                    entry_id: entry.id,
                    hint_id,
                })?;
            rup_hints.push(canonical_hint);
        }
        let Some(state) = entry_states.get_mut(&entry.id) else {
            return Err(ClauseTraceResolutionError::MissingCheckedIdentity {
                entry_index,
                id: entry.id,
            });
        };
        state.canonical_id = Some(canonical_id);
        if Some(entry_index) == terminal_empty_index {
            empty_clause_id = Some(canonical_id);
        }
        let clause = copy_slice_bounded(
            &entry.clause,
            ResolutionValidationResource::DerivedLiterals,
            &mut meter,
        )?;
        derived.push(RupStep {
            id: canonical_id,
            clause,
            rup_hints,
        });
    }

    if shape.synthesize_terminal_empty {
        let rup_hints = synthesize_terminal_empty_hints(
            &original_clauses,
            &derived,
            &unit_premises,
            num_vars,
            &mut meter,
        )?;
        let canonical_id = next_canonical_id;
        derived.push(RupStep {
            id: canonical_id,
            clause: Vec::new(),
            rup_hints,
        });
        empty_clause_id = Some(canonical_id);
    }

    let empty_clause_id =
        empty_clause_id.ok_or(ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty)?;
    let dag = ResolutionDag {
        num_vars,
        original_clauses,
        derived,
        empty_clause_id,
    };
    let mapping_bytes =
        retained_mapping_bytes(&original_mappings, original_mappings.capacity(), &mut meter)?;
    let dag_bytes = retained_dag_bytes(&dag, &mut meter)?;
    let retained_bytes = checked_resource_add(
        checked_resource_add(
            checked_resource_add(
                dag_bytes,
                mapping_bytes,
                ResolutionValidationResource::Bytes,
            )?,
            retained_premise_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        shape.source_trace_bytes,
        ResolutionValidationResource::Bytes,
    )?;
    let conversion_bytes = checked_resource_add(
        retained_bytes,
        checked_resource_mul(
            entry_states.capacity(),
            HASH_ENTRY_BYTES,
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        conversion_bytes,
        limits.max_bytes,
    )?;
    meter.check_controls()?;
    drop(entry_states);

    let conversion_work = meter.consumed_work();
    let validation_work = dag.validate_with_limits_interruptible(
        limits,
        unit_premises.as_slice(),
        checked_resource_add(
            checked_resource_add(
                mapping_bytes,
                shape.source_trace_bytes,
                ResolutionValidationResource::Bytes,
            )?,
            retained_premise_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        conversion_work,
        &mut should_stop,
    )?;

    Ok((
        ValidatedClauseTraceResolution {
            dag,
            original_mappings,
            validation_work,
            retained_bytes,
        },
        unit_premises,
    ))
}

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
                crate::ResolutionDagValidateError::NoConflict { .. }
            ))
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
