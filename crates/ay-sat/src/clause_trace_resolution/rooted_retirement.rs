// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Monotone satisfied-clause retirement, local to one rooted repair sweep.

use super::*;

/// Original-clause bitmap and sparse reset trail, held in the CSR builder's
/// already admitted cursor allocation. No additional buffer or namespace.
#[derive(Default)]
pub(super) struct RetiredOriginals(Vec<u32>);

impl RetiredOriginals {
    fn layout(clauses: usize, available: usize) -> Option<usize> {
        let words = clauses.checked_add(31)?.checked_div(32)?;
        u32::try_from(words).ok()?;
        let slots = words.checked_mul(2)?.checked_add(1)?;
        (clauses != 0 && slots <= available).then_some(slots)
    }

    pub(super) fn from_cursor(
        mut cursor: Vec<u32>,
        clauses: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Self, ResolutionValidationError> {
        meter.check_controls()?;
        meter.charge(1)?;
        let Some(slots) = Self::layout(clauses, cursor.len()) else {
            return Ok(Self::default());
        };
        cursor.truncate(slots);
        // [touched count, bitmap words, touched-word indices]. The trail is
        // overwritten before reading; only the count and bitmap need clearing.
        let zeroed = 1 + (slots - 1) / 2;
        for chunk in cursor[..zeroed].chunks_mut(CONTROL_POLL_INTERVAL) {
            meter.charge(chunk.len())?;
            chunk.fill(0);
            meter.check_controls()?;
        }
        meter.check_controls()?;
        Ok(Self(cursor))
    }

    fn location(&self, position: usize) -> Option<(usize, u32)> {
        let words = self.0.len().checked_sub(1)? / 2;
        let word = position / 32;
        (word < words).then_some((word, 1u32 << (position % 32)))
    }

    pub(super) fn contains(
        &self,
        position: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<bool, ResolutionValidationError> {
        let Some((word, mask)) = self.location(position) else {
            return Ok(false);
        };
        meter.charge(1)?;
        Ok(self.0[1 + word] & mask != 0)
    }

    pub(super) fn mark(
        &mut self,
        position: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        let Some((word, mask)) = self.location(position) else {
            return Ok(());
        };
        meter.charge(1)?;
        let previous = self.0[1 + word];
        if previous & mask != 0 {
            return Ok(());
        }
        if previous == 0 {
            let words = (self.0.len() - 1) / 2;
            let touched = self.0[0] as usize;
            // Charge flag/trail/count writes AND the eventual trail read/reset
            // before mutation. The first touched word also funds count reset.
            meter.charge(5 + usize::from(touched == 0))?;
            self.0[1 + words + touched] = word as u32;
            self.0[0] += 1;
        } else {
            meter.charge(1)?;
        }
        self.0[1 + word] = previous | mask;
        Ok(())
    }

    /// Reset work was prepaid at first touch, so even cancellation/work refusal
    /// must finish this bounded cleanup without polling or another debit.
    pub(super) fn clear(&mut self) {
        let Some(&touched) = self.0.first() else {
            return;
        };
        if touched == 0 {
            return;
        }
        let words = (self.0.len() - 1) / 2;
        for index in 0..touched as usize {
            let word = self.0[1 + words + index] as usize;
            self.0[1 + word] = 0;
        }
        self.0[0] = 0;
    }

    #[cfg(test)]
    pub(super) fn is_clear(&self) -> bool {
        self.0.is_empty() || self.0[..=self.0.len() / 2].iter().all(|&word| word == 0)
    }
}

pub(super) struct RetiredCandidates(Vec<u8>);

impl RetiredCandidates {
    fn bytes(capacity: usize) -> Result<usize, ResolutionValidationError> {
        checked_resource_add(
            size_of::<Self>(),
            capacity,
            ResolutionValidationResource::Bytes,
        )
    }

    fn check_capacity(
        capacity: usize,
        admitted_capacity: usize,
    ) -> Result<(), ResolutionValidationError> {
        enforce_resource(
            ResolutionValidationResource::Bytes,
            Self::bytes(capacity)?,
            Self::bytes(admitted_capacity)?,
        )
    }

    pub(super) fn new(
        count: usize,
        admitted_capacity: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Self, ResolutionValidationError> {
        meter.check_controls()?;
        // The caller supplies the recorded-byte slot admitted by
        // planned_trace_peaks, not the entire synthesis scratch allowance.
        Self::check_capacity(count, admitted_capacity)?;
        let mut flags = Vec::new();
        reserve_exact(
            &mut flags,
            count,
            ResolutionValidationResource::AssignmentScratch,
            meter,
        )?;
        Self::check_capacity(flags.capacity(), admitted_capacity)?;
        while flags.len() < count {
            let chunk = (count - flags.len()).min(CONTROL_POLL_INTERVAL);
            meter.charge(chunk)?;
            flags.resize(flags.len() + chunk, 0);
            meter.check_controls()?;
        }
        Ok(Self(flags))
    }

    pub(super) fn contains(&self, position: usize) -> bool {
        self.0[position] != 0
    }

    /// Within a sweep assignments only extend. A satisfied clause, including
    /// a just-propagated unit, cannot become open or conflicting in this row.
    pub(super) fn mark(
        &mut self,
        position: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        meter.charge(1)?;
        self.0[position] = 1;
        Ok(())
    }
}

#[cfg(test)]
mod tests;
