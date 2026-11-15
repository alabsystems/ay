// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission around the actual ordinary learned-clause insertion kernel.

use super::*;
use crate::counted_storage::{try_reserve, try_reserved_exact, Result as AdmissionResult};
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use std::convert::Infallible;

mod reserve;

pub(super) trait Policy {
    type Error;
    fn begin(&self, s: &Solver, lits: &[Literal], hints: &[u64]) -> Result<(), Self::Error>;
    #[cfg(debug_assertions)]
    fn no_duplicates(&self, lits: &[Literal]) -> Result<bool, Self::Error>;
    fn watch_order(&self, s: &Solver, count: usize) -> Result<(), Self::Error>;
    fn reserve_tail(
        &self,
        s: &mut Solver,
        lits: &[Literal],
        watches: Option<(Literal, Literal)>,
    ) -> Result<(), Self::Error>;
    fn reverse_hints(&self, hints: &[u64]) -> Result<Vec<u64>, Self::Error>;
    fn insert(&self, s: &mut Solver, lits: &[Literal], hints: &[u64])
        -> Result<usize, Self::Error>;
    fn learn_event(&self, s: &mut Solver, id: u64) -> Result<(), Self::Error>;
}

pub(super) struct Ordinary;
impl Policy for Ordinary {
    type Error = Infallible;
    fn begin(&self, _: &Solver, _: &[Literal], _: &[u64]) -> Result<(), Infallible> {
        Ok(())
    }
    #[cfg(debug_assertions)]
    fn no_duplicates(&self, lits: &[Literal]) -> Result<bool, Infallible> {
        let mut sorted = lits.iter().map(|l| l.0).collect::<Vec<_>>();
        sorted.sort_unstable();
        Ok(sorted.windows(2).all(|w| w[0] != w[1]))
    }
    fn watch_order(&self, _: &Solver, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn reserve_tail(
        &self,
        _: &mut Solver,
        _: &[Literal],
        _: Option<(Literal, Literal)>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn reverse_hints(&self, hints: &[u64]) -> Result<Vec<u64>, Infallible> {
        Ok(Solver::lrat_reverse_hints(hints))
    }
    fn insert(&self, s: &mut Solver, lits: &[Literal], hints: &[u64]) -> Result<usize, Infallible> {
        Ok(s.add_clause_db_checked(lits, true, true, hints))
    }
    fn learn_event(&self, s: &mut Solver, id: u64) -> Result<(), Infallible> {
        s.trace_learn(id);
        Ok(())
    }
}

struct Counted<'a>(&'a CountedAdmission);
impl Policy for Counted<'_> {
    type Error = CountedAdmissionError;
    fn begin(&self, s: &Solver, lits: &[Literal], hints: &[u64]) -> AdmissionResult<()> {
        reserve::entry(s, lits, hints, self.0)
    }
    #[cfg(debug_assertions)]
    fn no_duplicates(&self, lits: &[Literal]) -> AdmissionResult<bool> {
        let mut sorted = try_reserved_exact(self.0, lits.len())?;
        self.0.admit(lits.len().saturating_mul(2), 0)?;
        sorted.extend(lits.iter().map(|lit| lit.0));
        reserve::sort(lits.len(), self.0)?;
        sorted.sort_unstable();
        Ok(sorted.windows(2).all(|w| w[0] != w[1]))
    }
    fn watch_order(&self, s: &Solver, count: usize) -> AdmissionResult<()> {
        reserve::watch_order(s, count, self.0)
    }
    fn reserve_tail(
        &self,
        s: &mut Solver,
        lits: &[Literal],
        watches: Option<(Literal, Literal)>,
    ) -> AdmissionResult<()> {
        reserve::tail(s, lits, watches, self.0)
    }
    fn reverse_hints(&self, hints: &[u64]) -> AdmissionResult<Vec<u64>> {
        let mut reversed = Vec::new();
        for &id in hints.iter().rev() {
            self.0.admit(2, 0)?; // visit and eventual private-element retirement
            if id != 0 {
                try_reserve(self.0, &mut reversed, 1)?;
                reversed.push(id);
            }
        }
        Ok(reversed)
    }
    fn insert(&self, s: &mut Solver, lits: &[Literal], hints: &[u64]) -> AdmissionResult<usize> {
        s.add_derived_clause_db_counted(lits, hints, self.0)
    }
    fn learn_event(&self, s: &mut Solver, id: u64) -> AdmissionResult<()> {
        s.learn_event_counted(TraceEvent::Learn { clause_id: id }, self.0)
    }
}

impl Solver {
    pub(in crate::solver) fn add_conflict_learned_counted(
        &mut self,
        result: &mut ConflictResult,
        owner: &CountedAdmission,
    ) -> AdmissionResult<ClauseRef> {
        let reference = self.add_learned_clause_inner_with_proof_hints(
            &mut result.learned_clause,
            result.lbd,
            &result.resolution_chain,
            None,
            &mut Counted(owner),
        )?;
        owner.admit(
            result
                .learned_clause
                .len()
                .saturating_add(result.resolution_chain.len()),
            0,
        )?;
        self.conflict
            .return_learned_buf(std::mem::take(&mut result.learned_clause));
        self.conflict
            .return_chain_buf(std::mem::take(&mut result.resolution_chain));
        owner.check()?;
        Ok(reference)
    }
}
