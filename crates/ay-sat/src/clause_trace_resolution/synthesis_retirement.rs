// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

/// A temporary bitmap over canonical database positions, not clause ids.
/// Reuses only the already admitted, zero-initialized cone-marker buffer.
/// Satisfied clauses and propagated units stay satisfied as assignments grow;
/// open clauses remain live. No proof, reason or clause storage changes.
struct SynthesisRetirement<'a>(&'a mut [u8]);

impl<'a> SynthesisRetirement<'a> {
    fn layout(originals: usize, derived: usize, available: usize) -> Option<usize> {
        let clauses = originals.checked_add(derived)?;
        let bytes = clauses.checked_add(7)?.checked_div(8)?;
        (bytes <= available).then_some(bytes)
    }

    fn new(
        in_cone: &'a mut [u8],
        originals: usize,
        derived: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Self, ResolutionValidationError> {
        meter.check_controls()?;
        meter.charge(1)?;
        let bytes = Self::layout(originals, derived, in_cone.len()).unwrap_or(0);
        // prepare_synthesis_state initialized these bytes. Unsupported layouts
        // leave the full buffer untouched and retain the original sweep.
        Ok(Self(&mut in_cone[..bytes]))
    }

    fn contains(
        &self,
        position: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<bool, ResolutionValidationError> {
        let Some(byte) = self.0.get(position / 8) else {
            return Ok(false);
        };
        meter.charge(1)?;
        Ok(byte & (1 << (position % 8)) != 0)
    }

    fn mark(
        &mut self,
        position: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<(), ResolutionValidationError> {
        let Some(byte) = self.0.get_mut(position / 8) else {
            return Ok(());
        };
        // Account for both the read and write before mutating the borrowed byte.
        meter.charge(2)?;
        *byte |= 1 << (position % 8);
        Ok(())
    }

    fn clear(self, meter: &mut ConversionMeter<'_>) -> Result<(), ResolutionValidationError> {
        meter.check_controls()?;
        for chunk in self.0.chunks_mut(CONTROL_POLL_INTERVAL) {
            meter.charge(chunk.len())?;
            chunk.fill(0);
            meter.check_controls()?;
        }
        meter.check_controls()
    }
}

#[cfg(test)]
mod synthesis_retirement_tests {
    use super::*;
    include!("synthesis_retirement/tests.rs");
}
