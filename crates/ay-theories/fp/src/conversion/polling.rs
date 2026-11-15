// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conversion-only row/phase polling; legacy circuit helpers are unchanged.

mod finish;
mod normalize;
mod prepare;
mod round;
mod rows;

#[cfg(test)]
mod tests;

use crate::construction::control::BuildControl;
use crate::construction::FpBuildStage;
use crate::FpSolver;

impl FpSolver<'_> {
    pub(crate) fn conversion_poll<C: BuildControl>(&self, control: &mut C) -> Result<(), C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))
    }
}
