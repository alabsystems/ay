// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Aggregate resource metering for checked SAT refutations.

use super::*;

/// Hard resource envelope for the independent positive-RUP replay.
///
/// These are deliberately written at the production call site rather than
/// inherited implicitly from `Default`: changing a library default cannot
/// silently widen the mandatory verdict gate.
pub(super) fn validation_limits(executor: &Executor) -> ResolutionValidationLimits {
    ResolutionValidationLimits {
        // Use the command deadline, not a possibly lane-halved solve deadline:
        // replay may begin at the inner boundary while command time remains.
        deadline: executor
            .certification_deadline
            .get()
            .or_else(|| executor.solve_deadline.get()),
        max_original_clauses: 2_000_000,
        max_original_literals: 16_000_000,
        max_derived_steps: 2_000_000,
        max_derived_literals: 16_000_000,
        max_hints: 32_000_000,
        max_work: 250_000_000,
        max_bytes: 512 * 1024 * 1024,
    }
}

/// One aggregate resource/control meter for every accepting phase after SAT
/// search. It resumes from conversion/replay usage rather than granting proof
/// reconstruction, strict authentication, and composition fresh allowances.
pub(super) struct CheckedRefutationMeter {
    pub(super) limits: ResolutionValidationLimits,
    interrupt: Option<Arc<AtomicBool>>,
    memory_limit: Option<usize>,
    work: u64,
    bytes: usize,
}

/// Read-only projection shared by ordinary test evidence and production's
/// premise-carrying evidence. Crucially, this trait is private: it cannot be
/// used to erase the unit premises from a checked result outside this module.
pub(super) trait CheckedResolutionEvidence {
    fn dag(&self) -> &ResolutionDag;
    fn original_mappings(&self) -> &[ClauseTraceOriginalMapping];
    fn validation_work(&self) -> u64;
    fn retained_bytes(&self) -> usize;
}

impl CheckedResolutionEvidence for ValidatedClauseTraceResolution {
    fn dag(&self) -> &ResolutionDag {
        self.dag()
    }

    fn original_mappings(&self) -> &[ClauseTraceOriginalMapping] {
        self.original_mappings()
    }

    fn validation_work(&self) -> u64 {
        self.validation_work()
    }

    fn retained_bytes(&self) -> usize {
        self.retained_bytes()
    }
}

impl CheckedResolutionEvidence for ValidatedPremisedClauseTraceResolution {
    fn dag(&self) -> &ResolutionDag {
        self.dag()
    }

    fn original_mappings(&self) -> &[ClauseTraceOriginalMapping] {
        self.original_mappings()
    }

    fn validation_work(&self) -> u64 {
        self.validation_work()
    }

    fn retained_bytes(&self) -> usize {
        self.retained_bytes()
    }
}

impl CheckedRefutationMeter {
    pub(super) fn new(
        limits: ResolutionValidationLimits,
        interrupt: Option<Arc<AtomicBool>>,
        memory_limit: Option<usize>,
    ) -> Result<Self, ResolutionValidationError> {
        let mut meter = Self {
            limits,
            interrupt,
            memory_limit,
            work: 0,
            bytes: 0,
        };
        meter.charge(0, 0)?;
        Ok(meter)
    }

    #[cfg(test)]
    pub(super) fn resume<E: CheckedResolutionEvidence>(
        limits: ResolutionValidationLimits,
        interrupt: Option<Arc<AtomicBool>>,
        memory_limit: Option<usize>,
        validated: &E,
    ) -> Result<Self, ResolutionValidationError> {
        let mut meter = Self::new(limits, interrupt, memory_limit)?;
        meter.absorb_validation(validated)?;
        Ok(meter)
    }

    pub(super) fn remaining_validation_limits(
        &self,
    ) -> Result<ResolutionValidationLimits, ResolutionValidationError> {
        self.check_controls()?;
        let mut remaining = self.limits.clone();
        remaining.max_work = remaining.max_work.checked_sub(self.work).ok_or(
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            },
        )?;
        remaining.max_bytes = remaining.max_bytes.checked_sub(self.bytes).ok_or(
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Bytes,
            },
        )?;
        Ok(remaining)
    }

    pub(super) fn absorb_validation<E: CheckedResolutionEvidence>(
        &mut self,
        validated: &E,
    ) -> Result<(), ResolutionValidationError> {
        let work = usize::try_from(validated.validation_work()).map_err(|_| {
            ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            }
        })?;
        self.charge(work, validated.retained_bytes())
    }

    #[cfg(test)]
    pub(super) fn unbounded() -> Self {
        Self {
            limits: ResolutionValidationLimits::unbounded(),
            interrupt: None,
            memory_limit: None,
            work: 0,
            bytes: 0,
        }
    }

    pub(super) fn charge(
        &mut self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ResolutionValidationError> {
        self.check_controls()?;
        let work =
            u64::try_from(work).map_err(|_| ResolutionValidationError::AccountingOverflow {
                resource: ResolutionValidationResource::Work,
            })?;
        self.work =
            self.work
                .checked_add(work)
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
        self.bytes =
            self.bytes
                .checked_add(bytes)
                .ok_or(ResolutionValidationError::AccountingOverflow {
                    resource: ResolutionValidationResource::Bytes,
                })?;
        if self.bytes > self.limits.max_bytes {
            return Err(ResolutionValidationError::LimitExceeded {
                resource: ResolutionValidationResource::Bytes,
                limit: self.limits.max_bytes as u128,
                actual: self.bytes as u128,
            });
        }
        self.check_controls()
    }

    fn check_controls(&self) -> Result<(), ResolutionValidationError> {
        if self
            .limits
            .deadline
            .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
        {
            return Err(ResolutionValidationError::DeadlineExceeded);
        }
        if self
            .interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || crate::memory::memory_exceeded(self.memory_limit)
            || ay_sys::process_memory_exceeded()
        {
            return Err(ResolutionValidationError::Cancelled);
        }
        Ok(())
    }
}
