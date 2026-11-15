// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared CaDiCaL/Kissat block-shrink pass. Refusal is distinct from the
//! algorithm's ordinary failed-block fallback. No second minimization pass.

use super::*;
use crate::solver::conflict_analysis_minimize::admitted as minimize;
use crate::solver::reap::Reap;
use std::convert::Infallible;

pub(super) mod blocks;
mod prepare;
pub(super) mod walk;

pub(in crate::solver) trait Policy: minimize::Policy {
    const COUNTED: bool;
    fn prepare(&self, s: &Solver) -> Result<(), Self::Error>;
    fn reserve<T>(&self, values: &mut Vec<T>, additional: usize) -> Result<(), Self::Error>;
    fn sort_entries(&self, entries: &mut [(u32, usize, usize)]) -> Result<(), Self::Error>;
    fn push(&self, reap: &mut Reap, value: u32) -> Result<(), Self::Error>;
    fn pop(&self, reap: &mut Reap) -> Result<u32, Self::Error>;
    fn literal(&self, s: &Solver, lit: Literal) -> Result<(), Self::Error>;
    fn seen(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn open(&self, count: u32) -> Result<(), Self::Error>;
    fn chain(&self, s: &mut Solver, id: u64) -> Result<(), Self::Error>;
}

impl Policy for minimize::Ordinary {
    const COUNTED: bool = false;
    fn prepare(&self, _: &Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn reserve<T>(&self, _: &mut Vec<T>, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn sort_entries(&self, entries: &mut [(u32, usize, usize)]) -> Result<(), Infallible> {
        sort_shrink_entries(entries);
        Ok(())
    }
    fn push(&self, reap: &mut Reap, value: u32) -> Result<(), Infallible> {
        reap.push(value);
        Ok(())
    }
    fn pop(&self, reap: &mut Reap) -> Result<u32, Infallible> {
        Ok(reap.pop())
    }
    fn literal(&self, _: &Solver, _: Literal) -> Result<(), Infallible> {
        Ok(())
    }
    fn seen(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn open(&self, _: u32) -> Result<(), Infallible> {
        Ok(())
    }
    fn chain(&self, s: &mut Solver, id: u64) -> Result<(), Infallible> {
        s.conflict.add_to_chain(id);
        Ok(())
    }
}

/// Owns every taken workspace through ordinary completion, refusal and unwind.
/// Counted cleanup is prepaid before taking ownership and at dirty registration.
struct Scratch<'a> {
    s: &'a mut Solver,
    entries: Vec<(u32, usize, usize)>,
    result: Vec<Literal>,
    block: Vec<Literal>,
    counted: bool,
}

impl Drop for Scratch<'_> {
    fn drop(&mut self) {
        if self.counted {
            retire_minimize(self.s);
            self.s.ws_shrink_chain.clear();
            self.s.min.shrink_walked.clear();
            self.s.reap.clear();
            self.entries.clear();
            self.result.clear();
            self.block.clear();
        }
        self.s.ws_shrink_entries = std::mem::take(&mut self.entries);
        self.s.ws_shrink_result = std::mem::take(&mut self.result);
        self.s.ws_shrink_block_lits = std::mem::take(&mut self.block);
    }
}

fn retire_minimize(s: &mut Solver) {
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
}

pub(in crate::solver) fn run<P: Policy>(
    s: &mut Solver,
    count: usize,
    mut removed: Option<&mut Vec<Literal>>,
    p: &P,
) -> Result<(), P::Error> {
    p.prepare(s)?;
    p.work(80)?; // entry, fixed-size scratch retirement, all 33 Reap buckets
    debug_assert!(s.shrink_enabled && count > 1);
    let entries = std::mem::take(&mut s.ws_shrink_entries);
    let result = std::mem::take(&mut s.ws_shrink_result);
    let block = std::mem::take(&mut s.ws_shrink_block_lits);
    let mut scratch = Scratch {
        s,
        entries,
        result,
        block,
        counted: P::COUNTED,
    };
    if !prepare::entries(&mut scratch, count, p)? {
        // Ordinary chrono stale-position fallback: clear the exact dirty lists
        // before running the same recursive minimizer, not a counted shortcut.
        scratch.s.clear_minimize_scratch();
        scratch.s.minimize_clause_admitted(removed, p)?;
        return Ok(());
    }
    p.sort_entries(&mut scratch.entries)?;
    scratch.result.clear();
    let mut end = scratch.entries.len();
    while end > 0 {
        p.work(1)?;
        let level = scratch.entries[end - 1].0;
        let mut start = end - 1;
        while start > 0 {
            p.work(1)?;
            if scratch.entries[start - 1].0 != level {
                break;
            }
            start -= 1;
        }
        blocks::apply(&mut scratch, start, end, level, &mut removed, p)?;
        end = start;
    }
    p.work(scratch.result.len())?;
    debug_assert!(scratch.result.len() <= count);
    scratch.s.conflict.replace_learned(&scratch.result);
    scratch.s.clear_minimize_scratch();
    Ok(())
}

fn mark<P: Policy>(s: &mut Solver, var: usize, flags: u8, p: &P) -> Result<(), P::Error> {
    p.work(1)?;
    if s.min.minimize_flags[var] & MIN_VISITED == 0 {
        p.mark(s)?;
        s.min.minimize_to_clear.push(var);
    }
    s.min.minimize_flags[var] |= flags | MIN_VISITED;
    Ok(())
}

fn push<T, P: Policy>(values: &mut Vec<T>, value: T, p: &P) -> Result<(), P::Error> {
    p.work(2)?; // append and eventual retirement
    p.reserve(values, 1)?;
    values.push(value);
    Ok(())
}

fn removed<P: Policy>(
    removed: &mut Option<&mut Vec<Literal>>,
    lit: Literal,
    p: &P,
) -> Result<(), P::Error> {
    if let Some(values) = removed.as_deref_mut() {
        push(values, lit, p)?;
    }
    Ok(())
}
