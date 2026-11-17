// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The ordinary CaDiCaL minimize.cpp pass, with admission at its real work.
//! Recursive flag/abort/reason ordering lives in redundancy.rs. Ordinary
//! callers retain std sorting; counted sorting explicitly pays comparisons.

use super::*;
use std::convert::Infallible;

mod redundancy;

pub(in crate::solver) trait Policy {
    type Error;
    fn work(&self, units: usize) -> Result<(), Self::Error>;
    fn copy(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn sort(&self, values: &mut [Literal], data: &[VarData]) -> Result<(), Self::Error>;
    fn frame(&self, s: &Solver, lit: Literal, depth: u32) -> Result<(), Self::Error>;
    fn antecedent(&self, s: &Solver, lit: Literal, parent: Literal) -> Result<(), Self::Error>;
    fn mark(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn level(&self, s: &mut Solver, level: usize) -> Result<(), Self::Error>;
    fn clause(&self, s: &Solver, lit: Literal, offset: usize) -> Result<(), Self::Error>;
    fn counter(&self, value: u64, amount: u64) -> Result<(), Self::Error>;
    fn glue_growth(&self, s: &mut Solver, required: usize) -> Result<(), Self::Error>;
}

pub(in crate::solver) struct Ordinary;

impl Policy for Ordinary {
    type Error = Infallible;
    fn work(&self, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn copy(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn sort(&self, values: &mut [Literal], data: &[VarData]) -> Result<(), Infallible> {
        values.sort_unstable_by_key(|lit| data[lit.variable().index()].trail_pos);
        Ok(())
    }
    fn frame(&self, _: &Solver, _: Literal, _: u32) -> Result<(), Infallible> {
        Ok(())
    }
    fn antecedent(&self, _: &Solver, _: Literal, _: Literal) -> Result<(), Infallible> {
        Ok(())
    }
    fn mark(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn level(&self, _: &mut Solver, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn clause(&self, _: &Solver, _: Literal, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn counter(&self, _: u64, _: u64) -> Result<(), Infallible> {
        Ok(())
    }
    fn glue_growth(&self, _: &mut Solver, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
}

pub(in crate::solver) enum ShrinkRoute {
    Plain,
    DistinctLevels,
    RepeatedLevels(usize),
}

impl Solver {
    pub(in crate::solver) fn minimize_clause_admitted<P: Policy>(
        &mut self,
        mut removed: Option<&mut Vec<Literal>>,
        p: &P,
    ) -> Result<(), P::Error> {
        p.copy(self)?;
        self.conflict.copy_learned_to_clause_buf();
        p.sort(self.conflict.clause_buf_mut(), &self.var_data)?;
        let len = self.conflict.clause_buf_mut().len();
        for index in 0..len {
            p.work(1)?;
            let var = self.conflict.clause_buf_mut()[index].variable().index();
            p.mark(self)?;
            self.min.minimize_flags[var] |= MIN_VISITED;
            self.min.minimize_to_clear.push(var);
            let vd = self.var_data[var];
            let level = vd.level as usize;
            p.level(self, level)?;
            let entry = &mut self.min.minimize_level_seen[level];
            if entry.count == 0 {
                self.min.minimize_levels_to_clear.push(level as u32);
            }
            entry.count += 1;
            if vd.trail_pos < entry.trail {
                entry.trail = vd.trail_pos;
            }
        }
        for index in 0..len {
            p.work(1)?;
            let lit = self.conflict.clause_buf_mut()[index];
            if !self.redundant_admitted(lit, 0, p)? {
                self.min.minimize_flags[lit.variable().index()] |= MIN_KEEP;
            }
        }
        // retain is infallible for the counted caller (removed=None). Pay the
        // real complete scan/compaction before entering its nonfallible closure.
        p.work(len)?;
        let var_data = &self.var_data;
        let flags = &self.min.minimize_flags;
        self.conflict.retain_learned(|lit| {
            let var = lit.variable().index();
            let keep = var_data[var].level != 0 && flags[var] & MIN_REMOVABLE == 0;
            if !keep {
                if let Some(removed) = removed.as_deref_mut() {
                    removed.push(lit);
                }
            }
            keep
        });
        self.clear_minimize_scratch();
        debug_assert!(
            self.min.minimize_to_clear.is_empty(),
            "BUG: minimize_to_clear not empty after clear"
        );
        Ok(())
    }

    /// Same ordinary successful-pass cleanup; the unwind guard also bounds
    /// indexes defensively while retiring these same prepaid dirty lists.
    /// Each dirty element's reset is prepaid when that element is registered.
    pub(in crate::solver) fn clear_minimize_scratch(&mut self) {
        for &var in &self.min.minimize_to_clear {
            self.min.minimize_flags[var] = 0;
        }
        self.min.minimize_to_clear.clear();
        for &level in &self.min.minimize_levels_to_clear {
            self.min.minimize_level_seen[level as usize] = minimization_state::LevelSeen::EMPTY;
        }
        self.min.minimize_levels_to_clear.clear();
    }

    pub(in crate::solver) fn shrink_route_admitted<P: Policy>(
        &mut self,
        p: &P,
    ) -> Result<ShrinkRoute, P::Error> {
        p.work(1)?;
        if !self.shrink_enabled {
            return Ok(ShrinkRoute::Plain);
        }
        let count = self.conflict.learned_count();
        p.counter(self.stats.shrink_lits_deduced, count as u64 + 1)?;
        self.stats.shrink_lits_deduced += count as u64 + 1;
        if count <= 1 {
            return Ok(ShrinkRoute::Plain);
        }
        debug_assert!(
            self.shrink_enabled,
            "BUG: shrink_and_minimize called but shrink_enabled is false"
        );
        if self.repeated_level_admitted(count, p)? {
            return Ok(ShrinkRoute::RepeatedLevels(count));
        }
        p.counter(self.stats.shrink_singleton_fast_path_skips, 1)?;
        self.stats.shrink_singleton_fast_path_skips += 1;
        Ok(ShrinkRoute::DistinctLevels)
    }

    /// Return true if block-level shrinking has an actual same-level block to
    /// inspect among the non-UIP learned literals.
    ///
    /// If every non-UIP learned literal is at a distinct decision level, the
    /// shrink path cannot find a block UIP. The existing singleton-block path
    /// keeps each literal without recursive minimization, so the scratch setup,
    /// entry sort, and cleanup are avoidable in that case.
    pub(in crate::solver) fn repeated_level_admitted<P: Policy>(
        &mut self,
        count: usize,
        p: &P,
    ) -> Result<bool, P::Error> {
        p.work(1)?;
        if self.glue_stamp_counter == u32::MAX {
            p.work(self.glue_stamp.len())?;
            self.glue_stamp.fill(0);
            self.glue_stamp_counter = 0;
        }
        self.glue_stamp_counter += 1;
        let stamp = self.glue_stamp_counter;
        for index in 0..count {
            p.work(1)?;
            let lit = self.conflict.learned_at(index);
            let var = lit.variable().index();
            if self.lit_val(lit) >= 0 {
                return Ok(true);
            }
            let vd = self.var_data[var];
            if vd.level == 0 || vd.trail_pos as usize >= self.trail.len() {
                return Ok(true);
            }
            let level = vd.level as usize;
            if level >= self.glue_stamp.len() {
                p.glue_growth(self, level + 1)?;
                self.glue_stamp.resize(level + 1, 0);
            }
            if self.glue_stamp[level] == stamp {
                return Ok(true);
            }
            self.glue_stamp[level] = stamp;
        }
        Ok(false)
    }
}
