// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual ordinary conflict dispatch before first-UIP analysis. Both policies
//! execute the same unit/chrono branches; no alternate search mode is selected.

use super::*;
use std::convert::Infallible;

mod counted;
mod ordinary;
#[cfg(test)]
mod tests;
mod unit;

use ordinary::Ordinary;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Prelude {
    Analyze,
    Forced,
    Terminal,
}

#[derive(Clone, Copy)]
enum ForcedKind {
    GlobalUnit,
    Chronological,
}

trait Policy {
    type Error;
    fn backtrack(&mut self, s: &mut Solver, level: u32) -> Result<(), Self::Error>;
    fn level(
        &mut self,
        s: &mut Solver,
        reference: ClauseRef,
    ) -> Result<(u32, Option<Literal>), Self::Error>;
    fn unit(&mut self, s: &mut Solver, reference: ClauseRef) -> Result<bool, Self::Error>;
    fn force(
        &mut self,
        s: &mut Solver,
        reference: ClauseRef,
        lit: Literal,
        level: u32,
    ) -> Result<(), Self::Error>;
    fn note_forced(&mut self, s: &mut Solver, kind: ForcedKind) -> Result<(), Self::Error>;
    fn terminal(&mut self, s: &mut Solver, reference: ClauseRef) -> Result<(), Self::Error>;
    fn decay(&mut self, s: &mut Solver) -> Result<(), Self::Error>;
}

impl Solver {
    fn conflict_dispatch_prelude<P: Policy>(
        &mut self,
        reference: ClauseRef,
        policy: &mut P,
    ) -> Result<Prelude, P::Error> {
        // Global units precede the chrono/non-chrono split (#1696). Preserve
        // theory proof-ID retention and the ordinary callback-before-BT order.
        if self.arena.len_of(reference.index()) == 1 {
            policy.backtrack(self, 0)?;
            if !policy.unit(self, reference)? {
                policy.terminal(self, reference)?;
                return Ok(Prelude::Terminal);
            }
            policy.note_forced(self, ForcedKind::GlobalUnit)?;
            return Ok(Prelude::Forced);
        }
        // CaDiCaL analyze.cpp:962-1028; SAT'18 chronological BT, Algorithm 1.
        if self.chrono_enabled {
            let (level, forced) = policy.level(self, reference)?;
            if let Some(lit) = forced {
                if level > 0 {
                    policy.backtrack(self, level - 1)?;
                    policy.force(self, reference, lit, level - 1)?;
                    policy.note_forced(self, ForcedKind::Chronological)?;
                    return Ok(Prelude::Forced);
                }
            }
            if level < self.decision_level {
                policy.backtrack(self, level)?;
            }
            if self.decision_level == 0 {
                policy.terminal(self, reference)?;
                return Ok(Prelude::Terminal);
            }
        }
        Ok(Prelude::Analyze)
    }

    // Trail-exhaustion bailout learns nothing (#8479); retain the actual
    // selected decay and theory callback rather than manufacturing a clause.
    fn conflict_dispatch_bailout<P: Policy>(&mut self, policy: &mut P) -> Result<(), P::Error> {
        policy.backtrack(self, 0)?;
        policy.decay(self)
    }

    fn conflict_dispatch_force(&mut self, reference: ClauseRef, lit: Literal, level: u32) {
        self.fix_learned_uip_at_root(lit, level);
        self.enqueue(lit, Some(reference));
    }

    fn conflict_dispatch_note_forced(&mut self, kind: ForcedKind) {
        self.stats.forced_backtracks += 1;
        if matches!(kind, ForcedKind::Chronological) && self.cold.bump_reasons_kissat {
            self.update_bumpreason_decision_rate();
        }
    }

    fn conflict_dispatch_decay(&mut self) {
        match self.active_branch_heuristic {
            BranchHeuristic::Evsids => self.vsids.decay(),
            BranchHeuristic::Chb => self.vsids.decay_evsids_dormant(),
            BranchHeuristic::Vmtf => {}
        }
    }

    pub(super) fn conflict_dispatch_ordinary<F>(
        &mut self,
        reference: ClauseRef,
        callback: &mut F,
    ) -> bool
    where
        F: FnMut(&mut Solver, u32),
    {
        match self.conflict_dispatch_prelude(reference, &mut Ordinary(callback)) {
            Ok(Prelude::Analyze) => true,
            Ok(Prelude::Forced | Prelude::Terminal) => false,
            Err(never) => match never {},
        }
    }

    pub(super) fn conflict_bailout_ordinary<F>(&mut self, callback: &mut F)
    where
        F: FnMut(&mut Solver, u32),
    {
        match self.conflict_dispatch_bailout(&mut Ordinary(callback)) {
            Ok(()) => {}
            Err(never) => match never {},
        }
    }
}
