// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission around the actual CaDiCaL conflict-level/watch repair algorithm.

use super::*;
use crate::counted_storage::Result as AdmissionResult;
use crate::decision_trace::counted_decision::invalid;
use ay_core::original_query::CountedAdmission;
use std::convert::Infallible;

pub(in crate::solver) trait Policy {
    type Error;
    fn enter(&self, s: &Solver, reference: ClauseRef) -> Result<(), Self::Error>;
    fn work(&self, count: usize) -> Result<(), Self::Error>;
    fn relocation(
        &self,
        s: &mut Solver,
        reference: ClauseRef,
        slot: usize,
        best: usize,
    ) -> Result<(), Self::Error>;
    fn finish_move(&self) -> Result<(), Self::Error>;
}

pub(in crate::solver) struct Ordinary;
impl Policy for Ordinary {
    type Error = Infallible;
    fn enter(&self, _: &Solver, _: ClauseRef) -> Result<(), Infallible> {
        Ok(())
    }
    fn work(&self, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn relocation(
        &self,
        _: &mut Solver,
        _: ClauseRef,
        _: usize,
        _: usize,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn finish_move(&self) -> Result<(), Infallible> {
        Ok(())
    }
}

pub(in crate::solver) struct Counted<'a>(pub(in crate::solver) &'a CountedAdmission);
impl Policy for Counted<'_> {
    type Error = ay_core::original_query::CountedAdmissionError;
    fn enter(&self, s: &Solver, reference: ClauseRef) -> AdmissionResult<()> {
        self.0.admit(8, 0)?;
        let start = reference
            .index()
            .checked_add(crate::clause_arena::HEADER_WORDS);
        if start.is_none_or(|start| start > s.arena.len())
            || s.num_vars != s.var_data.len()
            || s.vals.len() < s.num_vars.saturating_mul(2)
        {
            return Err(invalid(self.0, "invalid counted conflict-level source"));
        }
        if s.arena.len_of(reference.index()) > s.arena.len() - start.unwrap_or(s.arena.len()) {
            return Err(invalid(self.0, "invalid counted conflict literal range"));
        }
        for &lit in s.arena.literals(reference.index()) {
            self.0.admit(1, 0)?;
            if lit.variable().index() >= s.num_vars || lit.index() >= s.watches.num_lists() {
                return Err(invalid(
                    self.0,
                    "conflict-level literal outside actual state",
                ));
            }
        }
        Ok(())
    }
    fn work(&self, count: usize) -> AdmissionResult<()> {
        self.0.admit(count, 0)
    }
    fn relocation(
        &self,
        s: &mut Solver,
        reference: ClauseRef,
        slot: usize,
        best: usize,
    ) -> AdmissionResult<()> {
        self.0.admit(8, 0)?;
        if best <= 1 {
            return self.0.check();
        }
        let old = s.arena.literal(reference.index(), slot);
        let new = s.arena.literal(reference.index(), best);
        let watches = s.watches.get_watches(old);
        let mut present = false;
        for index in 0..watches.len() {
            self.0.admit(2, 0)?; // actual inspection plus the matching destructive walk
            present |= watches.clause_ref(index) == reference;
        }
        if present {
            // Do not move regions early: leave ordinary append/relocation and
            // dead-slot accounting unchanged, including detached JIT watches.
            s.watches.reserve_counted_conflict_move(new, self.0)?;
        }
        self.0.check()
    }
    fn finish_move(&self) -> AdmissionResult<()> {
        self.0.check()
    }
}
