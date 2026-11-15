// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::try_reserve;

pub(super) struct Counted<'a>(pub(super) &'a CountedAdmission);

impl resolution::Policy for Counted<'_> {
    type Error = CountedAdmissionError;

    fn step(&self) -> AdmissionResult<()> {
        self.0.admit(1, 0)
    }

    fn clause(&self, s: &Solver, offset: usize, pivot: Option<Literal>) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        if s.arena.is_dead(offset) || s.arena.len_of(offset) < 2 {
            return Err(invalid(
                self.0,
                "counted first-UIP received a nonlive reason clause",
            ));
        }
        let mut pivots = 0usize;
        for &lit in s.arena.literals(offset) {
            self.0.admit(1, 0)?;
            if Some(lit) == pivot {
                pivots += 1;
            }
        }
        if pivot.is_some() && pivots != 1 {
            return Err(invalid(
                self.0,
                "counted first-UIP reason does not contain its pivot once",
            ));
        }
        Ok(())
    }

    fn literal(&self, s: &Solver, lit: Literal, pivot: Option<Literal>) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        let var = lit.variable().index();
        let Some(data) = s.var_data.get(var) else {
            return Err(invalid(
                self.0,
                "counted first-UIP literal is out of bounds",
            ));
        };
        let position = data.trail_pos as usize;
        if data.level > s.decision_level
            || s.lit_val(lit) >= 0
            || s.trail.get(position) != Some(&lit.negated())
        {
            return Err(invalid(
                self.0,
                "counted first-UIP literal lacks its false trail assignment",
            ));
        }
        if let Some(pivot) = pivot {
            let before = s.var_data[pivot.variable().index()].trail_pos as usize;
            if position >= before {
                return Err(invalid(
                    self.0,
                    "counted first-UIP reason is not earlier than its pivot",
                ));
            }
        }
        Ok(())
    }

    fn mark(&self, s: &mut Solver, lit: Literal) -> AdmissionResult<()> {
        let level = s.var_data[lit.variable().index()].level;
        s.conflict.prepare_counted_ic3_seen(self.0)?;
        if level > 0 {
            prepare_level(s, level, self.0)?;
        }
        if level > 0 && level < s.decision_level {
            s.conflict.prepare_counted_ic3_learned(self.0)?;
        }
        Ok(())
    }

    fn trail(&self, s: &Solver, index: usize) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        let lit = s.trail[index];
        let Some(data) = s.var_data.get(lit.variable().index()) else {
            return Err(invalid(
                self.0,
                "counted first-UIP trail variable is out of bounds",
            ));
        };
        if data.trail_pos as usize != index || s.lit_val(lit) <= 0 || data.level > s.decision_level
        {
            return Err(invalid(
                self.0,
                "counted first-UIP trail assignment is stale",
            ));
        }
        Ok(())
    }

    fn reason(&self, kind: &ReasonKind) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        match kind {
            ReasonKind::Decision | ReasonKind::LazyTheory(_) => Err(invalid(
                self.0,
                "counted first-UIP cannot resolve a non-UIP decision or lazy theory reason",
            )),
            ReasonKind::BinaryLiteral(_) | ReasonKind::Clause(_) => Ok(()),
        }
    }

    fn bailout(&self, s: &mut Solver) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        s.stats.trail_exhaustion_bailouts = s
            .stats
            .trail_exhaustion_bailouts
            .checked_add(1)
            .ok_or_else(|| invalid(self.0, "counted first-UIP bailout counter overflow"))?;
        // The scope retires all prepaid scratch; no ordinary diagnostic is
        // dropped and no unmetered clear/debug scan runs after a refusal.
        Ok(())
    }
}

fn prepare_level(s: &mut Solver, level: u32, owner: &CountedAdmission) -> AdmissionResult<()> {
    owner.admit(2, 0)?;
    let index = level as usize;
    let required = index
        .checked_add(1)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let growth = required.saturating_sub(s.min.level_seen.len());
    if growth > 0 {
        owner.admit(growth, 0)?;
        try_reserve(owner, &mut s.min.level_seen, growth)?;
    }
    let count = s.min.level_seen.get(index).map_or(0, |entry| entry.count);
    if count == u32::MAX {
        return Err(invalid(owner, "counted first-UIP level counter overflow"));
    }
    if count == 0 {
        owner.admit(2, 0)?; // dirty-list append and actual later level reset
        try_reserve(owner, &mut s.min.level_seen_to_clear, 1)?;
    }
    Ok(())
}
