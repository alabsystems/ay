// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Ordinary<'a, F>(pub(super) &'a mut F);

impl<F: FnMut(&mut Solver, u32)> Policy for Ordinary<'_, F> {
    type Error = Infallible;

    fn backtrack(&mut self, s: &mut Solver, level: u32) -> Result<(), Infallible> {
        (self.0)(s, level);
        s.backtrack(level);
        Ok(())
    }
    fn level(
        &mut self,
        s: &mut Solver,
        reference: ClauseRef,
    ) -> Result<(u32, Option<Literal>), Infallible> {
        Ok(s.find_conflict_level(reference))
    }
    fn unit(&mut self, s: &mut Solver, reference: ClauseRef) -> Result<bool, Infallible> {
        Ok(s.install_theory_unit_at_root(reference))
    }
    fn force(
        &mut self,
        s: &mut Solver,
        reference: ClauseRef,
        lit: Literal,
        level: u32,
    ) -> Result<(), Infallible> {
        s.conflict_dispatch_force(reference, lit, level);
        Ok(())
    }
    fn note_forced(&mut self, s: &mut Solver, kind: ForcedKind) -> Result<(), Infallible> {
        s.conflict_dispatch_note_forced(kind);
        Ok(())
    }
    fn terminal(&mut self, s: &mut Solver, reference: ClauseRef) -> Result<(), Infallible> {
        s.record_level0_conflict_chain(reference);
        Ok(())
    }
    fn decay(&mut self, s: &mut Solver) -> Result<(), Infallible> {
        s.conflict_dispatch_decay();
        Ok(())
    }
}
