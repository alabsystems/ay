// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Row-local occurrence notifications with the legacy ascending-position rounds.
//! Unlike ordinary FIFO watched propagation (see kitten/search.rs), readiness
//! never chooses a reason: the unchanged clause scanner does, in legacy order.

use super::*;

#[path = "rooted_scheduler/index.rs"]
mod index;
#[path = "rooted_scheduler/queue.rs"]
mod queue;
#[path = "rooted_scheduler/selection.rs"]
mod selection;
pub(super) use selection::CandidateSchedule;

pub(super) struct Scheduler {
    heads: Vec<usize>,
    items: Vec<usize>,
    current: Vec<usize>,
    next: Vec<usize>,
    membership: Vec<u8>,
    current_bit: u8,
    next_bit: u8,
    trail_cursor: usize,
}

impl Scheduler {
    pub(super) fn planned_bytes(
        num_vars: usize,
        count: usize,
        literals: usize,
    ) -> Result<usize, ResolutionValidationError> {
        if count == 0 {
            return Ok(0);
        }
        let codes = checked_resource_add(
            checked_resource_mul(num_vars, 2, ResolutionValidationResource::Bytes)?,
            1,
            ResolutionValidationResource::Bytes,
        )?;
        Self::bytes([codes, literals, count, count, count, codes])
    }

    // heads, items, current, next, membership, temporary CSR cursor. Include
    // pending heaps even while building: deliberately conservative peak.
    fn bytes(capacities: [usize; 6]) -> Result<usize, ResolutionValidationError> {
        let mut bytes = checked_resource_add(
            size_of::<Self>(),
            size_of::<Vec<usize>>(),
            ResolutionValidationResource::Bytes,
        )?;
        for (index, capacity) in capacities.into_iter().enumerate() {
            bytes = checked_resource_add(
                bytes,
                checked_resource_mul(
                    capacity,
                    if index == 4 { 1 } else { size_of::<usize>() },
                    ResolutionValidationResource::Bytes,
                )?,
                ResolutionValidationResource::Bytes,
            )?;
        }
        Ok(bytes)
    }

    fn check_capacities(
        capacities: [usize; 6],
        admitted: usize,
    ) -> Result<(), ResolutionValidationError> {
        enforce_resource(
            ResolutionValidationResource::Bytes,
            Self::bytes(capacities)?,
            admitted,
        )
    }

    pub(super) fn new(
        root: &RootPropagation,
        originals: &[(u64, Vec<Literal>)],
        derived: &[RupStep],
        candidates: &[u64],
        retired: &rooted_retirement::RetiredCandidates,
        admitted: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Option<Self>, ResolutionValidationError> {
        let mut scheduler = Self::for_candidates(
            root.assign.len(),
            originals,
            derived,
            candidates,
            |position| retired.contains(position),
            admitted,
            meter,
        )?;
        if let Some(ready) = scheduler.as_mut() {
            // All live positions are initially ready, covering assignments
            // made before this index was built.
            ready.trail_cursor = root.row_trail.len();
        }
        Ok(scheduler)
    }

    /// Shared candidate scheduling, without assuming any root-propagated facts.
    pub(super) fn for_candidates(
        num_vars: usize,
        originals: &[(u64, Vec<Literal>)],
        derived: &[RupStep],
        candidates: &[u64],
        retired: impl Fn(usize) -> bool,
        admitted: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Option<Self>, ResolutionValidationError> {
        meter.check_controls()?;
        let Some((heads, items, cursor_capacity)) =
            index::build(num_vars, originals, derived, candidates, admitted, meter)?
        else {
            return Ok(None);
        };
        let count = candidates.len();
        let mut capacities = [
            heads.capacity(),
            items.capacity(),
            count,
            count,
            count,
            cursor_capacity,
        ];
        let mut current = Vec::new();
        reserve_exact(
            &mut current,
            count,
            ResolutionValidationResource::AssignmentScratch,
            meter,
        )?;
        capacities[2] = current.capacity();
        Self::check_capacities(capacities, admitted)?;
        let mut next = Vec::new();
        reserve_exact(
            &mut next,
            count,
            ResolutionValidationResource::AssignmentScratch,
            meter,
        )?;
        capacities[3] = next.capacity();
        Self::check_capacities(capacities, admitted)?;
        let mut membership = Vec::new();
        reserve_exact(
            &mut membership,
            count,
            ResolutionValidationResource::AssignmentScratch,
            meter,
        )?;
        capacities[4] = membership.capacity();
        Self::check_capacities(capacities, admitted)?;
        for position in 0..count {
            meter.charge(2)?;
            let ready = !retired(position);
            membership.push(u8::from(ready));
            if ready {
                meter.charge(1)?;
                // Ascending positions already form a min-heap.
                current.push(position);
            }
        }
        meter.check_controls()?;
        Ok(Some(Self {
            heads,
            items,
            current,
            next,
            membership,
            current_bit: 1,
            next_bit: 2,
            trail_cursor: 0,
        }))
    }

    pub(super) fn pop(
        &mut self,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Option<usize>, ResolutionValidationError> {
        let result = queue::pop(&mut self.current, meter)?;
        if let Some(position) = result {
            meter.charge(1)?;
            self.membership[position] &= !self.current_bit;
        }
        Ok(result)
    }

    pub(super) fn notify(
        &mut self,
        root: &RootPropagation,
        after: Option<usize>,
        retired: &rooted_retirement::RetiredCandidates,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        while self.trail_cursor < root.row_trail.len() {
            meter.charge(1)?;
            let variable = root.row_trail[self.trail_cursor] as usize;
            self.trail_cursor += 1;
            let Some(value) = root.assign[variable] else {
                continue;
            };
            self.notify_assignment(
                variable,
                value,
                after,
                |position| retired.contains(position),
                meter,
            )?;
        }
        Ok(())
    }

    /// Wake only candidates whose literals were falsified. Satisfying a
    /// literal cannot turn an open clause into a unit or conflict.
    pub(super) fn notify_assignment(
        &mut self,
        variable: usize,
        value: bool,
        after: Option<usize>,
        retired: impl Fn(usize) -> bool,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        let code = literal_code(variable, !value);
        for offset in self.heads[code]..self.heads[code + 1] {
            meter.charge(1)?;
            let position = self.items[offset];
            if retired(position) {
                continue;
            }
            let in_current = after.is_none_or(|cursor| position > cursor);
            let bit = if in_current {
                self.current_bit
            } else {
                self.next_bit
            };
            if self.membership[position] & bit != 0 {
                continue;
            }
            meter.charge(1)?;
            self.membership[position] |= bit;
            let heap = if in_current {
                &mut self.current
            } else {
                &mut self.next
            };
            // A position occurs at most once in each round's heap.
            queue::push(heap, position, self.membership.len(), meter)?;
        }
        Ok(())
    }

    pub(super) fn next_round(
        &mut self,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        meter.charge(1)?;
        debug_assert_eq!(self.current.len(), 0);
        std::mem::swap(&mut self.current, &mut self.next);
        std::mem::swap(&mut self.current_bit, &mut self.next_bit);
        Ok(())
    }
}

#[cfg(test)]
#[path = "rooted_scheduler/tests.rs"]
mod tests;
