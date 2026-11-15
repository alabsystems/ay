// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The existing IC3 first-UIP walk, shared without changing its ordering.
//! GRASP (Marques-Silva/Sakallah, 1996), Chaff (DAC 2001), MiniSat (SAT 2003).
//! Final minimization, activity updates and learning remain separate phases.

use super::*;
use std::convert::Infallible;

pub(super) trait Policy {
    type Error;
    fn step(&self) -> Result<(), Self::Error>;
    fn clause(&self, s: &Solver, offset: usize, pivot: Option<Literal>) -> Result<(), Self::Error>;
    fn literal(&self, s: &Solver, lit: Literal, pivot: Option<Literal>) -> Result<(), Self::Error>;
    fn mark(&self, s: &mut Solver, lit: Literal) -> Result<(), Self::Error>;
    fn trail(&self, s: &Solver, index: usize) -> Result<(), Self::Error>;
    fn reason(&self, kind: &ReasonKind) -> Result<(), Self::Error>;
    fn bailout(&self, s: &mut Solver) -> Result<(), Self::Error>;
}

pub(super) struct Ordinary;

impl Policy for Ordinary {
    type Error = Infallible;
    fn step(&self) -> Result<(), Infallible> {
        Ok(())
    }
    fn clause(&self, _: &Solver, _: usize, _: Option<Literal>) -> Result<(), Infallible> {
        Ok(())
    }
    fn literal(&self, _: &Solver, _: Literal, _: Option<Literal>) -> Result<(), Infallible> {
        Ok(())
    }
    fn mark(&self, _: &mut Solver, _: Literal) -> Result<(), Infallible> {
        Ok(())
    }
    fn trail(&self, _: &Solver, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn reason(&self, _: &ReasonKind) -> Result<(), Infallible> {
        Ok(())
    }
    fn bailout(&self, s: &mut Solver) -> Result<(), Infallible> {
        s.stats.trail_exhaustion_bailouts += 1;
        s.conflict.clear(&mut s.var_data);
        s.clear_level_seen();
        Ok(())
    }
}

enum Origin {
    Clause,
    Binary,
}

impl Solver {
    pub(super) fn resolve_ic3_first_uip<P: Policy>(
        &mut self,
        conflict_ref: ClauseRef,
        policy: &P,
    ) -> Result<Option<Literal>, P::Error> {
        debug_assert!(
            self.decision_level > 0,
            "BUG: IC3 conflict analysis called at decision level 0"
        );
        let mut counter = 0u32;
        let mut pivot = None;
        let mut index = self.trail.len();
        let mut offset = conflict_ref.0 as usize;
        policy.clause(self, offset, pivot)?;
        let mut clause_len = self.arena.len_of(offset);
        loop {
            policy.step()?;
            for i in 0..clause_len {
                policy.step()?;
                let lit = self.arena.literal_at(offset, i);
                if Some(lit) != pivot {
                    self.visit_ic3_literal(lit, pivot, &mut counter, Origin::Clause, policy)?;
                }
            }
            let Some(trail_lit) = self.next_ic3_seen_literal(&mut index, policy)? else {
                policy.bailout(self)?;
                return Ok(None);
            };
            pivot = Some(trail_lit);
            debug_assert!(
                counter > 0,
                "BUG: IC3 analysis counter underflow before resolving {pivot:?} \
                 (counter={counter}, decision_level={})",
                self.decision_level,
            );
            if counter == 0 {
                policy.bailout(self)?;
                return Ok(None);
            }
            counter -= 1;
            if counter == 0 {
                return Ok(Some(trail_lit.negated()));
            }
            policy.step()?;
            let kind = self.var_reason_kind(trail_lit.variable().index());
            policy.reason(&kind)?;
            match kind {
                ReasonKind::Decision => {
                    self.conflict.add_to_learned(trail_lit.negated());
                    clause_len = 0;
                }
                ReasonKind::BinaryLiteral(reason_lit) => {
                    self.visit_ic3_literal(
                        reason_lit,
                        pivot,
                        &mut counter,
                        Origin::Binary,
                        policy,
                    )?;
                    clause_len = 0;
                }
                ReasonKind::LazyTheory(lazy_idx) => {
                    // Preserve the ordinary debug assertion and release fallback.
                    // Counted policy rejects this kind before reaching the arm.
                    debug_assert!(
                        false,
                        "BUG: LazyTheory reason in IC3 conflict analysis (var={}, lazy_idx={})",
                        trail_lit.variable().index(),
                        lazy_idx
                    );
                    self.conflict.add_to_learned(trail_lit.negated());
                    clause_len = 0;
                }
                ReasonKind::Clause(reason_ref) => {
                    offset = reason_ref.0 as usize;
                    policy.clause(self, offset, pivot)?;
                    clause_len = self.arena.len_of(offset);
                }
            }
        }
    }

    fn visit_ic3_literal<P: Policy>(
        &mut self,
        lit: Literal,
        pivot: Option<Literal>,
        counter: &mut u32,
        origin: Origin,
        policy: &P,
    ) -> Result<(), P::Error> {
        policy.literal(self, lit, pivot)?;
        let var = lit.variable().index();
        let level = self.var_data[var].level;
        if !self.conflict.is_seen(var, &self.var_data) {
            policy.mark(self, lit)?;
            self.conflict.mark_seen(var, &mut self.var_data);
            if matches!(origin, Origin::Clause) {
                debug_assert!(
                    level <= self.decision_level,
                    "BUG: IC3 analyzed literal var={} at level {} exceeds decision level {}",
                    var,
                    level,
                    self.decision_level
                );
            }
            if level > 0 {
                self.track_level_seen(level, var);
            }
            if level == self.decision_level {
                *counter += 1;
            } else if level > 0 {
                self.conflict.add_to_learned(lit);
            }
        }
        Ok(())
    }

    fn next_ic3_seen_literal<P: Policy>(
        &self,
        index: &mut usize,
        policy: &P,
    ) -> Result<Option<Literal>, P::Error> {
        *index = (*index).min(self.trail.len());
        while *index > 0 {
            *index -= 1;
            policy.trail(self, *index)?;
            let lit = self.trail[*index];
            let var = lit.variable().index();
            if self.conflict.is_seen(var, &self.var_data)
                && self.var_data[var].level == self.decision_level
            {
                return Ok(Some(lit));
            }
        }
        Ok(None)
    }
}
