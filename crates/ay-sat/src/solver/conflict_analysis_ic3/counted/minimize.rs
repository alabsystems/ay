// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual selected minimization, including the shared repeated-block shrink
//! engine. Activity, learned insertion, reset and proof remain separate work.

use super::*;
use crate::counted_storage::try_reserve;
use crate::solver::conflict_analysis_minimize::admitted::{Policy, ShrinkRoute};

mod shrink;
mod sort;

pub(in crate::solver) struct CountedIc3Minimized<'a> {
    resolution: CountedIc3Resolution<'a>,
}

impl CountedIc3Minimized<'_> {
    pub(in crate::solver) fn asserting_literal(&self) -> Literal {
        self.resolution.uip
    }
    pub(in crate::solver) fn lower_literals(&self) -> &[Literal] {
        self.resolution.lower_literals()
    }
    /// Ordinary IC3 uses the LBD computed BEFORE minimization.
    pub(in crate::solver) fn lbd(&self) -> u32 {
        self.resolution.lbd
    }
    pub(in crate::solver) fn finish(self) -> Result<(), SatUnknownReason> {
        self.resolution.finish()
    }
}

impl<'a> CountedIc3Resolution<'a> {
    /// Consume once through the configured real minimization route. The
    /// same owner's shared block-shrink engine retains the ordinary selected
    /// algorithm; no shrinking default or recursive fallback is substituted.
    pub(in crate::solver) fn minimize_selected(
        mut self,
    ) -> Result<CountedIc3Minimized<'a>, SatUnknownReason> {
        let owner = self.retirement.owner.clone();
        prepare(self.retirement.solver, &owner).map_err(counted_admission::reason)?;
        self.retirement.minimization_active = true;
        let p = Counted(&owner);
        let s = &mut *self.retirement.solver;
        match s
            .shrink_route_admitted(&p)
            .map_err(counted_admission::reason)?
        {
            ShrinkRoute::Plain => s
                .minimize_clause_admitted(None, &p)
                .map_err(counted_admission::reason)?,
            ShrinkRoute::DistinctLevels => (),
            ShrinkRoute::RepeatedLevels(count) => {
                crate::solver::shrink::admitted::run(s, count, None, &p)
                    .map_err(counted_admission::reason)?
            }
        }
        owner.check().map_err(counted_admission::reason)?;
        Ok(CountedIc3Minimized { resolution: self })
    }
}

fn prepare(s: &mut Solver, owner: &CountedAdmission) -> AdmissionResult<()> {
    owner.admit(16, 0)?;
    if s.min.minimize_flags.len() < s.num_vars
        || s.min.minimize_level_seen.len() <= s.decision_level as usize
        || !s.min.minimize_to_clear.is_empty()
        || !s.min.minimize_levels_to_clear.is_empty()
        || !s.conflict.clause_buf_mut().is_empty()
    {
        return Err(invalid(
            owner,
            "counted minimization requires retired bounded scratch",
        ));
    }
    owner.admit(s.min.minimize_flags.len(), 0)?;
    if s.min.minimize_flags.iter().any(|flags| *flags != 0) {
        return Err(invalid(owner, "counted minimization has untracked flags"));
    }
    owner.admit(s.min.minimize_level_seen.len(), 0)?;
    if s.min
        .minimize_level_seen
        .iter()
        .any(|level| *level != minimization_state::LevelSeen::EMPTY)
    {
        return Err(invalid(owner, "counted minimization has untracked levels"));
    }
    Ok(())
}

/// Quiet, prepaid retirement is safe even during opaque-payload/internal unwind.
/// Preserve unrelated scratch if preflight never transferred its ownership.
pub(super) fn retire(s: &mut Solver) {
    for &var in &s.min.minimize_to_clear {
        if let Some(flags) = s.min.minimize_flags.get_mut(var) {
            *flags = 0;
        }
    }
    s.min.minimize_to_clear.clear();
    for &level in &s.min.minimize_levels_to_clear {
        if let Some(entry) = s.min.minimize_level_seen.get_mut(level as usize) {
            *entry = minimization_state::LevelSeen::EMPTY;
        }
    }
    s.min.minimize_levels_to_clear.clear();
    s.conflict.clause_buf_mut().clear();
}

struct Counted<'a>(&'a CountedAdmission);

impl Policy for Counted<'_> {
    type Error = CountedAdmissionError;
    fn work(&self, units: usize) -> AdmissionResult<()> {
        self.0.admit(units, 0)
    }
    fn copy(&self, s: &mut Solver) -> AdmissionResult<()> {
        s.conflict.prepare_counted_minimize_copy(self.0)
    }
    fn sort(&self, values: &mut [Literal], data: &[VarData]) -> AdmissionResult<()> {
        sort::by_trail(values, data, self.0)
    }
    fn frame(&self, s: &Solver, lit: Literal, _depth: u32) -> AdmissionResult<()> {
        // Logical resident recursion data, not a claim about compiler stack
        // layout or CPU instructions. Storage is cumulative, never refunded.
        self.0.admit(
            1,
            std::mem::size_of::<(Literal, u32, VarData, usize, usize)>(),
        )?;
        validate_literal(s, lit, self.0)
    }
    fn antecedent(&self, s: &Solver, lit: Literal, parent: Literal) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        validate_literal(s, lit, self.0)?;
        if s.var_data[lit.variable().index()].trail_pos
            >= s.var_data[parent.variable().index()].trail_pos
        {
            return Err(invalid(
                self.0,
                "counted minimize antecedent is not earlier than its pivot",
            ));
        }
        Ok(())
    }
    fn mark(&self, s: &mut Solver) -> AdmissionResult<()> {
        self.0.admit(2, 0)?; // registration and actual later cleanup
        try_reserve(self.0, &mut s.min.minimize_to_clear, 1)
    }
    fn level(&self, s: &mut Solver, level: usize) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        let Some(entry) = s.min.minimize_level_seen.get(level) else {
            return Err(invalid(
                self.0,
                "counted minimization level is out of bounds",
            ));
        };
        if entry.count == u32::MAX {
            return Err(invalid(
                self.0,
                "counted minimization level counter overflow",
            ));
        }
        if entry.count == 0 {
            self.0.admit(2, 0)?;
            try_reserve(self.0, &mut s.min.minimize_levels_to_clear, 1)?;
        }
        Ok(())
    }
    fn clause(&self, s: &Solver, lit: Literal, offset: usize) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        if s.arena.len_of(offset) < 2 {
            return Err(invalid(
                self.0,
                "counted minimization reason is deleted or unit",
            ));
        }
        // Ordinary minimize deliberately accepts garbage_keep_data reasons.
        // Require the real positive pivot exactly once; other occurrences of
        // its variable would be skipped by the ordinary recursion and are invalid.
        let mut pivots = 0;
        for &reason in s.arena.literals(offset) {
            self.0.admit(1, 0)?;
            if reason.variable() == lit.variable() {
                if reason != lit.negated() {
                    return Err(invalid(
                        self.0,
                        "counted minimize reason has the wrong pivot sign",
                    ));
                }
                pivots += 1;
            }
        }
        if pivots != 1 {
            return Err(invalid(
                self.0,
                "counted minimize reason lacks its unique pivot",
            ));
        }
        Ok(())
    }
    fn counter(&self, value: u64, amount: u64) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        value
            .checked_add(amount)
            .ok_or_else(|| invalid(self.0, "counted minimization counter overflow"))?;
        Ok(())
    }
    fn glue_growth(&self, s: &mut Solver, required: usize) -> AdmissionResult<()> {
        let growth = required.saturating_sub(s.glue_stamp.len());
        self.0.admit(growth, 0)?;
        try_reserve(self.0, &mut s.glue_stamp, growth)
    }
}

fn validate_literal(s: &Solver, lit: Literal, owner: &CountedAdmission) -> AdmissionResult<()> {
    let Some(data) = s.var_data.get(lit.variable().index()) else {
        return Err(invalid(
            owner,
            "counted minimization literal is out of bounds",
        ));
    };
    if data.level > s.decision_level
        || s.lit_val(lit) >= 0
        || s.trail.get(data.trail_pos as usize) != Some(&lit.negated())
    {
        return Err(invalid(
            owner,
            "counted minimization literal has no false trail assignment",
        ));
    }
    Ok(())
}
