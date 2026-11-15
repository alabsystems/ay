// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Existing RUP allocation/work accounting, with cancellation-only polls.

use super::{BvSolvedExportError, Lit, ResolutionStep, RupExpansionLimits};
use ay_core::time::Instant;
use std::{hash::Hash, mem::size_of};

/// Mutable output and accounting shared by each RUP expansion.
pub(super) struct RupExpansionState<'a> {
    pub(super) steps: Vec<ResolutionStep>,
    pub(super) next_step_id: u32,
    meter: Option<RupExpansionMeter>,
    resolution_scratch: Vec<Lit>,
    keep_going: &'a mut dyn FnMut() -> bool,
}

impl<'a> RupExpansionState<'a> {
    pub(super) fn new(
        next_step_id: u32,
        limits: Option<RupExpansionLimits>,
        keep_going: &'a mut dyn FnMut() -> bool,
    ) -> Self {
        Self {
            steps: Vec::new(),
            next_step_id,
            meter: limits.map(RupExpansionMeter::new),
            resolution_scratch: Vec::new(),
            keep_going,
        }
    }

    // The allocation-volume budget charges actual fresh buffers. Reusing a
    // previously charged temporary preserves that bound and retained evidence.
    pub(super) fn resolution_buffer(
        &mut self,
        capacity: usize,
    ) -> Result<Vec<Lit>, BvSolvedExportError> {
        self.check_deadline()?;
        let mut buffer = std::mem::take(&mut self.resolution_scratch);
        if buffer.capacity() < capacity {
            return reserve_rup_vec(capacity, self, capacity);
        }
        buffer.clear();
        Ok(buffer)
    }

    pub(super) fn recycle_resolution_buffer(&mut self, mut buffer: Vec<Lit>) {
        if buffer.capacity() > self.resolution_scratch.capacity() {
            buffer.clear();
            self.resolution_scratch = buffer;
        }
    }

    pub(super) fn is_bounded(&self) -> bool {
        self.meter.is_some()
    }

    pub(super) fn check_deadline(&mut self) -> Result<(), BvSolvedExportError> {
        if self
            .meter
            .as_ref()
            .is_some_and(|meter| Instant::now() >= meter.limits.deadline)
        {
            Err(BvSolvedExportError::ResourceLimit {
                resource: "RUP expansion deadline",
                limit: 0,
                actual: 1,
            })
        } else {
            self.poll()
        }
    }

    fn poll(&mut self) -> Result<(), BvSolvedExportError> {
        if (self.keep_going)() {
            Ok(())
        } else {
            Err(BvSolvedExportError::Cancelled)
        }
    }

    pub(super) fn accounting_overflow(&self, resource: &'static str) -> BvSolvedExportError {
        BvSolvedExportError::ResourceLimit {
            resource,
            limit: self.meter.as_ref().map_or(usize::MAX, |meter| {
                if resource == "expanded literals" {
                    meter.limits.max_literals
                } else if resource == "RUP expansion work" {
                    meter.limits.max_work
                } else {
                    meter.limits.max_bytes
                }
            }),
            actual: usize::MAX,
        }
    }

    pub(super) fn charge_work(&mut self, amount: usize) -> Result<(), BvSolvedExportError> {
        let Some(meter) = self.meter.as_mut() else {
            return self.poll();
        };
        meter.work = meter
            .work
            .checked_add(amount)
            .ok_or(BvSolvedExportError::ResourceLimit {
                resource: "RUP expansion work",
                limit: meter.limits.max_work,
                actual: usize::MAX,
            })?;
        if meter.work > meter.limits.max_work {
            return Err(BvSolvedExportError::ResourceLimit {
                resource: "RUP expansion work",
                limit: meter.limits.max_work,
                actual: meter.work,
            });
        }
        if meter.work >= meter.next_deadline_check {
            if Instant::now() >= meter.limits.deadline {
                return Err(BvSolvedExportError::ResourceLimit {
                    resource: "RUP expansion deadline",
                    limit: 0,
                    actual: 1,
                });
            }
            meter.next_deadline_check = meter.work.saturating_add(1_024);
        }
        self.poll()
    }

    fn charge_literals(&mut self, amount: usize) -> Result<(), BvSolvedExportError> {
        let Some(meter) = self.meter.as_mut() else {
            return self.poll();
        };
        meter.literals =
            meter
                .literals
                .checked_add(amount)
                .ok_or(BvSolvedExportError::ResourceLimit {
                    resource: "expanded literals",
                    limit: meter.limits.max_literals,
                    actual: usize::MAX,
                })?;
        if meter.literals > meter.limits.max_literals {
            return Err(BvSolvedExportError::ResourceLimit {
                resource: "expanded literals",
                limit: meter.limits.max_literals,
                actual: meter.literals,
            });
        }
        self.poll()
    }

    fn charge_bytes(&mut self, amount: usize) -> Result<(), BvSolvedExportError> {
        let Some(meter) = self.meter.as_mut() else {
            return self.poll();
        };
        meter.bytes =
            meter
                .bytes
                .checked_add(amount)
                .ok_or(BvSolvedExportError::ResourceLimit {
                    resource: "RUP expansion bytes",
                    limit: meter.limits.max_bytes,
                    actual: usize::MAX,
                })?;
        if meter.bytes > meter.limits.max_bytes {
            return Err(BvSolvedExportError::ResourceLimit {
                resource: "RUP expansion bytes",
                limit: meter.limits.max_bytes,
                actual: meter.bytes,
            });
        }
        self.poll()
    }

    pub(super) fn reserve_steps(&mut self, capacity: usize) -> Result<(), BvSolvedExportError> {
        if self.meter.is_none() {
            return Ok(());
        }
        let bytes = capacity
            .checked_mul(size_of::<ResolutionStep>())
            .ok_or_else(|| self.accounting_overflow("RUP expansion bytes"))?;
        self.charge_bytes(bytes)?;
        self.steps
            .try_reserve_exact(capacity)
            .map_err(|_| BvSolvedExportError::ResourceLimit {
                resource: "RUP expansion bytes",
                limit: self
                    .meter
                    .as_ref()
                    .map_or(usize::MAX, |meter| meter.limits.max_bytes),
                actual: self
                    .meter
                    .as_ref()
                    .map_or(usize::MAX, |meter| meter.limits.max_bytes.saturating_add(1)),
            })
    }

    pub(super) fn push_step(&mut self, step: ResolutionStep) -> Result<(), BvSolvedExportError> {
        if let Some(limits) = self.meter.as_ref().map(|meter| meter.limits) {
            if self.steps.len() >= limits.max_steps {
                return Err(BvSolvedExportError::ResourceLimit {
                    resource: "expanded resolution steps",
                    limit: limits.max_steps,
                    actual: self.steps.len().saturating_add(1),
                });
            }
        }
        self.poll()?;
        self.steps.push(step);
        Ok(())
    }
}

struct RupExpansionMeter {
    limits: RupExpansionLimits,
    literals: usize,
    work: usize,
    bytes: usize,
    next_deadline_check: usize,
}

impl RupExpansionMeter {
    fn new(limits: RupExpansionLimits) -> Self {
        Self {
            limits,
            literals: 0,
            work: 0,
            bytes: 0,
            next_deadline_check: 0,
        }
    }
}

pub(super) fn reserve_rup_map<K, V>(
    state: &mut RupExpansionState,
    entries: usize,
) -> Result<(), BvSolvedExportError> {
    // Hash tables need control bytes and spare capacity in addition to their
    // key/value payload. A 2x record charge is a conservative pre-allocation
    // envelope for the standard library's <= 7/8 load factor.
    let bytes = entries
        .checked_mul(size_of::<(K, V)>())
        .and_then(|bytes| bytes.checked_mul(2))
        .ok_or_else(|| state.accounting_overflow("RUP expansion bytes"))?;
    state.charge_bytes(bytes)
}

pub(super) fn try_reserve_rup_map<K, V>(
    map: &mut std::collections::HashMap<K, V>,
    entries: usize,
    state: &RupExpansionState,
) -> Result<(), BvSolvedExportError>
where
    K: Eq + Hash,
{
    if state.meter.is_none() {
        return Ok(());
    }
    map.try_reserve(entries)
        .map_err(|_| BvSolvedExportError::ResourceLimit {
            resource: "RUP expansion bytes",
            limit: state
                .meter
                .as_ref()
                .map_or(usize::MAX, |meter| meter.limits.max_bytes),
            actual: state
                .meter
                .as_ref()
                .map_or(usize::MAX, |meter| meter.limits.max_bytes.saturating_add(1)),
        })
}

pub(super) fn reserve_rup_vec<T>(
    len: usize,
    state: &mut RupExpansionState,
    literal_slots: usize,
) -> Result<Vec<T>, BvSolvedExportError> {
    if state.meter.is_none() {
        return Ok(Vec::with_capacity(len));
    }
    state.charge_literals(literal_slots)?;
    let bytes = len
        .checked_mul(size_of::<T>())
        .ok_or_else(|| state.accounting_overflow("RUP expansion bytes"))?;
    state.charge_bytes(bytes)?;
    let mut out = Vec::new();
    out.try_reserve_exact(len)
        .map_err(|_| BvSolvedExportError::ResourceLimit {
            resource: "RUP expansion bytes",
            limit: state
                .meter
                .as_ref()
                .map_or(usize::MAX, |meter| meter.limits.max_bytes),
            actual: state
                .meter
                .as_ref()
                .map_or(usize::MAX, |meter| meter.limits.max_bytes.saturating_add(1)),
        })?;
    Ok(out)
}
