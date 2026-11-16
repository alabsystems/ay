// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::solver::conflict_analysis_minimize::admitted::Policy as Minimize;

impl Minimize for Counted<'_> {
    type Error = CountedAdmissionError;
    fn work(&self, units: usize) -> AdmissionResult<()> {
        self.0.admit(units, 0)
    }
    fn copy(&self, s: &mut Solver) -> AdmissionResult<()> {
        s.conflict.prepare_counted_minimize_copy(self.0)
    }
    fn sort(&self, values: &mut [Literal], data: &[VarData]) -> AdmissionResult<()> {
        sort::prepay_unstable(values.len(), self.0)?;
        <Ordinary as Minimize>::sort(&Ordinary, values, data).map_err(|never| match never {})
    }
    fn frame(&self, s: &Solver, lit: Literal, _: u32) -> AdmissionResult<()> {
        self.0
            .admit(1, size_of::<(Literal, u32, VarData, usize, usize)>())?;
        bounded_literal(s, lit, self.0)
    }
    fn antecedent(&self, s: &Solver, lit: Literal, _: Literal) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        // Do not demand a false trail assignment before ordinary ghost handling.
        // The shared kernel conservatively keeps unassigned chrono literals.
        bounded_literal(s, lit, self.0)
    }
    fn mark(&self, s: &mut Solver) -> AdmissionResult<()> {
        self.0.admit(2, 0)?;
        try_reserve(self.0, &mut s.min.minimize_to_clear, 1)
    }
    fn level(&self, s: &mut Solver, level: usize) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        let Some(entry) = s.min.minimize_level_seen.get(level) else {
            return Err(invalid(self.0, "ordinary minimize level out of bounds"));
        };
        if entry.count == u32::MAX {
            return Err(invalid(self.0, "ordinary minimize level counter overflow"));
        }
        if entry.count == 0 {
            self.0.admit(2, 0)?;
            try_reserve(self.0, &mut s.min.minimize_levels_to_clear, 1)?;
        }
        Ok(())
    }
    fn clause(&self, _: &Solver, _: Literal, _: usize) -> AdmissionResult<()> {
        // Trusted internal arena offsets, exactly as ordinary analysis.
        // Any internal panic remains inside the original-owner guard.
        self.0.admit(1, 0)
    }
    fn counter(&self, value: u64, amount: u64) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        value
            .checked_add(amount)
            .ok_or_else(|| invalid(self.0, "ordinary finalization counter overflow"))?;
        Ok(())
    }
    fn glue_growth(&self, s: &mut Solver, required: usize) -> AdmissionResult<()> {
        let growth = required.saturating_sub(s.glue_stamp.len());
        self.0.admit(growth, 0)?;
        try_reserve(self.0, &mut s.glue_stamp, growth)
    }
}

pub(super) fn bounded_literal(
    s: &Solver,
    lit: Literal,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    if lit.variable().index() >= s.var_data.len() || lit.index() >= s.vals.len() {
        return Err(invalid(
            owner,
            "ordinary finalization literal out of bounds",
        ));
    }
    Ok(())
}
