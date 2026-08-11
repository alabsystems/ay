// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent, resource-bounded replay for in-memory resolution DAGs.

use crate::literal::Literal;
use crate::resolution_dag::{ResolutionDag, RupStep};
use ay_core::time::Instant;
use std::collections::HashMap;
use std::mem::size_of;

/// Certificate or scratch resource guarded by [`ResolutionValidationLimits`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolutionValidationResource {
    /// Original clause count.
    OriginalClauses,
    /// Literals in original clauses.
    OriginalLiterals,
    /// Derived proof-step count.
    DerivedSteps,
    /// Literals in derived clauses.
    DerivedLiterals,
    /// RUP hint count.
    Hints,
    /// Deterministic replay work (literal and hint visits).
    Work,
    /// Certificate plus replay scratch memory.
    Bytes,
    /// Clause database entry count.
    ClauseDatabase,
    /// Assignment/trail scratch.
    AssignmentScratch,
}

/// Hard limits for independent [`ResolutionDag`] replay.
///
/// `max_bytes` accounts for the DAG's retained payload plus conservative
/// validator scratch (the clause-id map, assignment, and undo trail). Allocator
/// reallocation transients are outside this counter and require a caller-owned
/// process/RSS envelope. The
/// deadline is absolute, so callers cannot accidentally refresh a relative
/// timeout between parsing and replay.
#[derive(Clone, Debug)]
pub struct ResolutionValidationLimits {
    /// Absolute replay deadline. `None` disables the wall-clock guard.
    pub deadline: Option<Instant>,
    /// Maximum original clauses.
    pub max_original_clauses: usize,
    /// Maximum literals across original clauses.
    pub max_original_literals: usize,
    /// Maximum derived RUP steps.
    pub max_derived_steps: usize,
    /// Maximum literals across derived clauses.
    pub max_derived_literals: usize,
    /// Maximum RUP hints across all derived steps.
    pub max_hints: usize,
    /// Maximum deterministic replay work units.
    pub max_work: u64,
    /// Maximum logical certificate plus conservative replay-scratch bytes.
    pub max_bytes: usize,
}

impl Default for ResolutionValidationLimits {
    fn default() -> Self {
        Self {
            deadline: None,
            max_original_clauses: 2_000_000,
            max_original_literals: 16_000_000,
            max_derived_steps: 2_000_000,
            max_derived_literals: 16_000_000,
            max_hints: 32_000_000,
            max_work: 250_000_000,
            max_bytes: 512 * 1024 * 1024,
        }
    }
}

impl ResolutionValidationLimits {
    /// Limits matching the historical [`ResolutionDag::validate`] posture.
    /// New production call sites should pass explicit finite limits instead.
    #[must_use]
    pub fn unbounded() -> Self {
        Self {
            deadline: None,
            max_original_clauses: usize::MAX,
            max_original_literals: usize::MAX,
            max_derived_steps: usize::MAX,
            max_derived_literals: usize::MAX,
            max_hints: usize::MAX,
            max_work: u64::MAX,
            max_bytes: usize::MAX,
        }
    }
}

/// Errors from the compatibility-preserving [`ResolutionDag::validate`]
/// replay.  This enum intentionally retains the exact historical variants so
/// downstream exhaustive matches remain source-compatible.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ResolutionDagValidateError {
    /// An original clause's LRAT id is not its 1-based input position.
    #[error("original clause at index {index} has id {id}, expected {expected}")]
    NonCanonicalOriginalId {
        /// Position in `original_clauses`.
        index: usize,
        /// Recorded LRAT id.
        id: u64,
        /// Expected id (`index + 1`).
        expected: u64,
    },
    /// A literal references a variable outside `0..num_vars`.
    #[error("clause id {clause}: variable index {var} out of range (num_vars {num_vars})")]
    VarOutOfRange {
        /// LRAT id of the offending clause.
        clause: u64,
        /// Variable index seen.
        var: usize,
        /// Declared variable count.
        num_vars: usize,
    },
    /// A derived step's id does not strictly increase.
    #[error("derived step id {id} not strictly greater than previous id {prev}")]
    NonMonotoneStepId {
        /// Offending step id.
        id: u64,
        /// Highest id seen before it.
        prev: u64,
    },
    /// A hint names no clause known at that point.
    #[error("step {step}: hint {hint} names no known clause")]
    UnknownHint {
        /// Derived step id.
        step: u64,
        /// Offending hint id.
        hint: u64,
    },
    /// A hint was not unit under the current assignment.
    #[error("step {step}: hint {hint} is not unit under the current assignment")]
    HintNotUnit {
        /// Derived step id.
        step: u64,
        /// Offending hint id.
        hint: u64,
    },
    /// The hint chain ended without conflict.
    #[error("step {step}: hint chain exhausted without conflict (clause not RUP from its hints)")]
    NoConflict {
        /// Derived step id.
        step: u64,
    },
    /// The refutation carries no derived steps.
    #[error("refutation has no derived steps")]
    NoSteps,
    /// The final derived clause is not empty.
    #[error("final derived clause is not empty (has {len} literals)")]
    FinalClauseNotEmpty {
        /// Literal count of the final clause.
        len: usize,
    },
    /// The recorded empty-clause id does not name the final step.
    #[error("recorded empty_clause_id {recorded} does not match final step id {actual}")]
    EmptyClauseIdMismatch {
        /// Recorded id.
        recorded: u64,
        /// Actual final step id.
        actual: u64,
    },
}

/// Errors from resource-bounded [`ResolutionDag::validate_with_limits`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ResolutionValidationError {
    /// The certificate is not a valid resolution DAG.
    #[error(transparent)]
    Invalid(#[from] ResolutionDagValidateError),
    /// A finite validation limit was exceeded.
    #[error("resolution replay {resource:?} limit exceeded: limit {limit}, actual {actual}")]
    LimitExceeded {
        /// Exhausted resource.
        resource: ResolutionValidationResource,
        /// Configured limit.
        limit: u128,
        /// Observed or attempted amount.
        actual: u128,
    },
    /// The absolute validation deadline expired.
    #[error("resolution replay deadline exceeded")]
    DeadlineExceeded,
    /// Overflow occurred while accounting proof or scratch size.
    #[error("resolution replay accounting overflow for {resource:?}")]
    AccountingOverflow {
        /// Resource being accounted.
        resource: ResolutionValidationResource,
    },
    /// A fallible replay-scratch allocation failed.
    #[error("resolution replay allocation failed for {resource:?}")]
    AllocationFailed {
        /// Scratch resource being allocated.
        resource: ResolutionValidationResource,
    },
}

struct WorkMeter<'a> {
    limits: &'a ResolutionValidationLimits,
    work: u64,
}

impl<'a> WorkMeter<'a> {
    fn new(limits: &'a ResolutionValidationLimits) -> Result<Self, ResolutionValidationError> {
        let meter = Self { limits, work: 0 };
        meter.check_deadline()?;
        Ok(meter)
    }

    fn check_deadline(&self) -> Result<(), ResolutionValidationError> {
        if self
            .limits
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(ResolutionValidationError::DeadlineExceeded);
        }
        Ok(())
    }

    fn charge(&mut self, amount: u64) -> Result<(), ResolutionValidationError> {
        let old = self.work;
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
        // Clock reads are amortized across deterministic replay work.
        if old / 1024 != self.work / 1024 {
            self.check_deadline()?;
        }
        Ok(())
    }
}

fn checked_add(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_add(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

fn checked_mul(
    lhs: usize,
    rhs: usize,
    resource: ResolutionValidationResource,
) -> Result<usize, ResolutionValidationError> {
    lhs.checked_mul(rhs)
        .ok_or(ResolutionValidationError::AccountingOverflow { resource })
}

fn enforce(
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

impl ResolutionDag {
    /// Replay with the historical, compatibility-preserving unbounded posture.
    /// Production paths should use [`Self::validate_with_limits`].
    pub fn validate(&self) -> Result<(), ResolutionDagValidateError> {
        let check_lits =
            |clause_id: u64, lits: &[Literal]| -> Result<(), ResolutionDagValidateError> {
                for lit in lits {
                    let var = lit.variable().index();
                    if var >= self.num_vars {
                        return Err(ResolutionDagValidateError::VarOutOfRange {
                            clause: clause_id,
                            var,
                            num_vars: self.num_vars,
                        });
                    }
                }
                Ok(())
            };

        let mut db: HashMap<u64, &[Literal]> =
            HashMap::with_capacity(self.original_clauses.len() + self.derived.len());
        for (index, (id, lits)) in self.original_clauses.iter().enumerate() {
            let expected = index as u64 + 1;
            if *id != expected {
                return Err(ResolutionDagValidateError::NonCanonicalOriginalId {
                    index,
                    id: *id,
                    expected,
                });
            }
            check_lits(*id, lits)?;
            db.insert(*id, lits.as_slice());
        }

        let mut last_id = self.original_clauses.len() as u64;
        let mut assign: Vec<Option<bool>> = vec![None; self.num_vars];
        let mut trail: Vec<usize> = Vec::new();
        for step in &self.derived {
            if step.id <= last_id {
                return Err(ResolutionDagValidateError::NonMonotoneStepId {
                    id: step.id,
                    prev: last_id,
                });
            }
            check_lits(step.id, &step.clause)?;

            let result = replay_rup_legacy(step, &db, &mut assign, &mut trail);
            for &var in &trail {
                assign[var] = None;
            }
            trail.clear();
            result?;

            db.insert(step.id, step.clause.as_slice());
            last_id = step.id;
        }

        let Some(last) = self.derived.last() else {
            return Err(ResolutionDagValidateError::NoSteps);
        };
        if !last.clause.is_empty() {
            return Err(ResolutionDagValidateError::FinalClauseNotEmpty {
                len: last.clause.len(),
            });
        }
        if self.empty_clause_id != last.id {
            return Err(ResolutionDagValidateError::EmptyClauseIdMismatch {
                recorded: self.empty_clause_id,
                actual: last.id,
            });
        }
        Ok(())
    }

    /// Independently replay this LRAT/RUP DAG under explicit count, deadline,
    /// and retained-byte limits.
    ///
    /// The replay checks canonical originals, variable ranges, monotone ids,
    /// each hinted RUP derivation, and the final empty clause. All allocations
    /// are preceded by bounded accounting and use fallible reserve operations.
    pub fn validate_with_limits(
        &self,
        limits: &ResolutionValidationLimits,
    ) -> Result<(), ResolutionValidationError> {
        let mut meter = WorkMeter::new(limits)?;
        enforce(
            ResolutionValidationResource::OriginalClauses,
            self.original_clauses.len(),
            limits.max_original_clauses,
        )?;
        enforce(
            ResolutionValidationResource::DerivedSteps,
            self.derived.len(),
            limits.max_derived_steps,
        )?;

        let mut certificate_bytes = size_of::<ResolutionDag>();
        certificate_bytes = checked_add(
            certificate_bytes,
            checked_mul(
                self.original_clauses.capacity(),
                size_of::<(u64, Vec<Literal>)>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        certificate_bytes = checked_add(
            certificate_bytes,
            checked_mul(
                self.derived.capacity(),
                size_of::<RupStep>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;

        let mut original_literals = 0usize;
        for (index, (_, clause)) in self.original_clauses.iter().enumerate() {
            meter.charge(1)?;
            if index % 1024 == 0 {
                meter.check_deadline()?;
            }
            original_literals = checked_add(
                original_literals,
                clause.len(),
                ResolutionValidationResource::OriginalLiterals,
            )?;
            certificate_bytes = checked_add(
                certificate_bytes,
                checked_mul(
                    clause.capacity(),
                    size_of::<Literal>(),
                    ResolutionValidationResource::Bytes,
                )?,
                ResolutionValidationResource::Bytes,
            )?;
        }
        enforce(
            ResolutionValidationResource::OriginalLiterals,
            original_literals,
            limits.max_original_literals,
        )?;

        let mut derived_literals = 0usize;
        let mut hints = 0usize;
        for (index, step) in self.derived.iter().enumerate() {
            meter.charge(1)?;
            if index % 1024 == 0 {
                meter.check_deadline()?;
            }
            derived_literals = checked_add(
                derived_literals,
                step.clause.len(),
                ResolutionValidationResource::DerivedLiterals,
            )?;
            hints = checked_add(
                hints,
                step.rup_hints.len(),
                ResolutionValidationResource::Hints,
            )?;
            certificate_bytes = checked_add(
                certificate_bytes,
                checked_mul(
                    step.clause.capacity(),
                    size_of::<Literal>(),
                    ResolutionValidationResource::Bytes,
                )?,
                ResolutionValidationResource::Bytes,
            )?;
            certificate_bytes = checked_add(
                certificate_bytes,
                checked_mul(
                    step.rup_hints.capacity(),
                    size_of::<u64>(),
                    ResolutionValidationResource::Bytes,
                )?,
                ResolutionValidationResource::Bytes,
            )?;
        }
        enforce(
            ResolutionValidationResource::DerivedLiterals,
            derived_literals,
            limits.max_derived_literals,
        )?;
        enforce(ResolutionValidationResource::Hints, hints, limits.max_hints)?;

        let db_entries = checked_add(
            self.original_clauses.len(),
            self.derived.len(),
            ResolutionValidationResource::ClauseDatabase,
        )?;
        // Conservatively preflight scratch before allocating it. HashMap's
        // implementation controls its actual bucket count, so it is checked
        // again from the resulting capacity below.
        let mut estimated_bytes = checked_add(
            certificate_bytes,
            checked_mul(db_entries, 64, ResolutionValidationResource::Bytes)?,
            ResolutionValidationResource::Bytes,
        )?;
        estimated_bytes = checked_add(
            estimated_bytes,
            checked_mul(
                self.num_vars,
                checked_add(
                    size_of::<Option<bool>>(),
                    size_of::<usize>(),
                    ResolutionValidationResource::Bytes,
                )?,
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        enforce(
            ResolutionValidationResource::Bytes,
            estimated_bytes,
            limits.max_bytes,
        )?;
        meter.check_deadline()?;

        let mut db: HashMap<u64, &[Literal]> = HashMap::new();
        db.try_reserve(db_entries)
            .map_err(|_| ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::ClauseDatabase,
            })?;
        meter.check_deadline()?;
        let mut assign: Vec<Option<bool>> = Vec::new();
        assign.try_reserve_exact(self.num_vars).map_err(|_| {
            ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::AssignmentScratch,
            }
        })?;
        assign.resize(self.num_vars, None);
        meter.check_deadline()?;
        let mut trail: Vec<usize> = Vec::new();
        trail.try_reserve_exact(self.num_vars).map_err(|_| {
            ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::AssignmentScratch,
            }
        })?;
        meter.check_deadline()?;

        let actual_scratch_bytes = checked_add(
            checked_mul(db.capacity(), 64, ResolutionValidationResource::Bytes)?,
            checked_add(
                checked_mul(
                    assign.capacity(),
                    size_of::<Option<bool>>(),
                    ResolutionValidationResource::Bytes,
                )?,
                checked_mul(
                    trail.capacity(),
                    size_of::<usize>(),
                    ResolutionValidationResource::Bytes,
                )?,
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        let actual_bytes = checked_add(
            certificate_bytes,
            actual_scratch_bytes,
            ResolutionValidationResource::Bytes,
        )?;
        enforce(
            ResolutionValidationResource::Bytes,
            actual_bytes,
            limits.max_bytes,
        )?;

        for (index, (id, lits)) in self.original_clauses.iter().enumerate() {
            meter.charge(1)?;
            let expected = u64::try_from(index)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or(ResolutionValidationError::AccountingOverflow {
                    resource: ResolutionValidationResource::OriginalClauses,
                })?;
            if *id != expected {
                return Err(ResolutionDagValidateError::NonCanonicalOriginalId {
                    index,
                    id: *id,
                    expected,
                }
                .into());
            }
            check_lits(self.num_vars, *id, lits, &mut meter)?;
            db.insert(*id, lits.as_slice());
        }

        let mut last_id = u64::try_from(self.original_clauses.len()).map_err(|_| {
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::OriginalClauses,
            }
        })?;
        for step in &self.derived {
            meter.charge(1)?;
            if step.id <= last_id {
                return Err(ResolutionDagValidateError::NonMonotoneStepId {
                    id: step.id,
                    prev: last_id,
                }
                .into());
            }
            check_lits(self.num_vars, step.id, &step.clause, &mut meter)?;

            let result = replay_rup(step, &db, &mut assign, &mut trail, &mut meter);
            for &var in &trail {
                meter.charge(1)?;
                assign[var] = None;
            }
            trail.clear();
            result?;

            db.insert(step.id, step.clause.as_slice());
            last_id = step.id;
        }

        let Some(last) = self.derived.last() else {
            return Err(ResolutionDagValidateError::NoSteps.into());
        };
        if !last.clause.is_empty() {
            return Err(ResolutionDagValidateError::FinalClauseNotEmpty {
                len: last.clause.len(),
            }
            .into());
        }
        if self.empty_clause_id != last.id {
            return Err(ResolutionDagValidateError::EmptyClauseIdMismatch {
                recorded: self.empty_clause_id,
                actual: last.id,
            }
            .into());
        }
        meter.check_deadline()
    }
}

enum LegacyHintScan {
    Conflict,
    Propagate(Literal),
    SatisfiedUnit,
    NonUnit,
}

fn replay_rup_legacy(
    step: &RupStep,
    db: &HashMap<u64, &[Literal]>,
    assign: &mut [Option<bool>],
    trail: &mut Vec<usize>,
) -> Result<(), ResolutionDagValidateError> {
    for lit in &step.clause {
        let var = lit.variable().index();
        let forced = !lit.is_positive();
        match assign[var] {
            None => {
                assign[var] = Some(forced);
                trail.push(var);
            }
            Some(value) if value == forced => {}
            Some(_) => return Ok(()),
        }
    }

    for &hint in &step.rup_hints {
        let Some(hint_clause) = db.get(&hint) else {
            return Err(ResolutionDagValidateError::UnknownHint {
                step: step.id,
                hint,
            });
        };
        match scan_hint_legacy(hint_clause, assign) {
            LegacyHintScan::Conflict => return Ok(()),
            LegacyHintScan::Propagate(lit) => {
                let var = lit.variable().index();
                assign[var] = Some(lit.is_positive());
                trail.push(var);
            }
            LegacyHintScan::SatisfiedUnit => {}
            LegacyHintScan::NonUnit => {
                return Err(ResolutionDagValidateError::HintNotUnit {
                    step: step.id,
                    hint,
                });
            }
        }
    }
    Err(ResolutionDagValidateError::NoConflict { step: step.id })
}

fn scan_hint_legacy(clause: &[Literal], assign: &[Option<bool>]) -> LegacyHintScan {
    let mut non_falsified: Option<(Literal, bool)> = None;
    for &lit in clause {
        let truth = assign[lit.variable().index()].map(|value| value == lit.is_positive());
        match truth {
            Some(false) => {}
            Some(true) | None => {
                if non_falsified.is_some() {
                    return LegacyHintScan::NonUnit;
                }
                non_falsified = Some((lit, truth == Some(true)));
            }
        }
    }
    match non_falsified {
        None => LegacyHintScan::Conflict,
        Some((_, true)) => LegacyHintScan::SatisfiedUnit,
        Some((lit, false)) => LegacyHintScan::Propagate(lit),
    }
}

fn check_lits(
    num_vars: usize,
    clause_id: u64,
    lits: &[Literal],
    meter: &mut WorkMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    for lit in lits {
        meter.charge(1)?;
        let var = lit.variable().index();
        if var >= num_vars {
            return Err(ResolutionDagValidateError::VarOutOfRange {
                clause: clause_id,
                var,
                num_vars,
            }
            .into());
        }
    }
    Ok(())
}

enum HintScan {
    Conflict,
    Propagate(Literal),
    SatisfiedUnit,
    NonUnit,
}

fn replay_rup(
    step: &RupStep,
    db: &HashMap<u64, &[Literal]>,
    assign: &mut [Option<bool>],
    trail: &mut Vec<usize>,
    meter: &mut WorkMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    for lit in &step.clause {
        meter.charge(1)?;
        let var = lit.variable().index();
        let forced = !lit.is_positive();
        match assign[var] {
            None => {
                assign[var] = Some(forced);
                trail.push(var);
            }
            Some(value) if value == forced => {}
            Some(_) => return Ok(()), // tautology
        }
    }

    for &hint in &step.rup_hints {
        meter.charge(1)?;
        let Some(hint_clause) = db.get(&hint) else {
            return Err(ResolutionDagValidateError::UnknownHint {
                step: step.id,
                hint,
            }
            .into());
        };
        match scan_hint(hint_clause, assign, meter)? {
            HintScan::Conflict => return Ok(()),
            HintScan::Propagate(lit) => {
                let var = lit.variable().index();
                assign[var] = Some(lit.is_positive());
                trail.push(var);
            }
            HintScan::SatisfiedUnit => {}
            HintScan::NonUnit => {
                return Err(ResolutionDagValidateError::HintNotUnit {
                    step: step.id,
                    hint,
                }
                .into());
            }
        }
    }
    Err(ResolutionDagValidateError::NoConflict { step: step.id }.into())
}

fn scan_hint(
    clause: &[Literal],
    assign: &[Option<bool>],
    meter: &mut WorkMeter<'_>,
) -> Result<HintScan, ResolutionValidationError> {
    let mut non_falsified: Option<(Literal, bool)> = None;
    for &lit in clause {
        meter.charge(1)?;
        let truth = assign[lit.variable().index()].map(|value| value == lit.is_positive());
        match truth {
            Some(false) => {}
            Some(true) | None => {
                if non_falsified.is_some() {
                    return Ok(HintScan::NonUnit);
                }
                non_falsified = Some((lit, truth == Some(true)));
            }
        }
    }
    Ok(match non_falsified {
        None => HintScan::Conflict,
        Some((_, true)) => HintScan::SatisfiedUnit,
        Some((lit, false)) => HintScan::Propagate(lit),
    })
}

#[cfg(test)]
mod compatibility_tests {
    use super::*;

    // Deliberately exhaustive: adding a bounded-resource variant to the
    // historical error enum must fail this compile guard.
    fn exhaust_legacy_error(error: ResolutionDagValidateError) {
        match error {
            ResolutionDagValidateError::NonCanonicalOriginalId { .. }
            | ResolutionDagValidateError::VarOutOfRange { .. }
            | ResolutionDagValidateError::NonMonotoneStepId { .. }
            | ResolutionDagValidateError::UnknownHint { .. }
            | ResolutionDagValidateError::HintNotUnit { .. }
            | ResolutionDagValidateError::NoConflict { .. }
            | ResolutionDagValidateError::NoSteps
            | ResolutionDagValidateError::FinalClauseNotEmpty { .. }
            | ResolutionDagValidateError::EmptyClauseIdMismatch { .. } => {}
        }
    }

    #[test]
    fn legacy_error_remains_exhaustive() {
        exhaust_legacy_error(ResolutionDagValidateError::NoSteps);
    }

    #[cfg(feature = "unsat-cert")]
    #[test]
    fn legacy_unsat_cert_module_path_remains_public() {
        let error: crate::unsat_cert::ResolutionDagValidateError =
            ResolutionDagValidateError::NoSteps;
        let _: crate::ResolutionDagValidateError = error;
    }
}
