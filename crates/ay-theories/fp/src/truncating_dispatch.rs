// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reserved typed-only truncating remainder dispatch.
//! Frontend/native declarations refuse the __ay_ namespace. The Expr bridge
//! additionally rejects FuncApp forgeries before it mints this in-process DATA.

use crate::construction::control::BuildControl;
use crate::{FpBuildStage, FpDecomposed, FpPrecision, FpSolver};
use ay_core::term::{Symbol, TermId};
use ay_core::Sort;

impl FpSolver<'_> {
    pub(crate) fn decompose_truncating_rem_with_control<C: BuildControl>(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        precision: FpPrecision,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let format = Sort::FloatingPoint(precision.exponent_bits(), precision.significand_bits());
        if !matches!(precision, FpPrecision::Float32 | FpPrecision::Float64)
            || !matches!(symbol, Symbol::Named(_))
            || args.len() != 2
            || args
                .iter()
                .any(|&id| self.terms.entry_stamp(id).is_none() || self.terms.sort(id) != &format)
        {
            self.has_encoding_gap = true;
            let result = self.fresh_decomposed(precision);
            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            return Ok(result);
        }
        let x = self.get_fp_with_control(args[0], control)?;
        let y = self.get_fp_with_control(args[1], control)?;
        let result = self.make_truncating_rem_with_control(&x, &y, control)?;
        drop(y);
        drop(x);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests;
