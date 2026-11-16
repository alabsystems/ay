// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Block-level clause shrinking (CaDiCaL shrink.cpp, Kissat shrink.c).
//!
//! After 1UIP conflict analysis, the learned clause may contain multiple
//! literals at the same decision level. Block-level shrinking attempts to
//! replace an entire "block" of same-level literals with a single "block UIP"
//! — a literal that implies all others at that level. This produces shorter
//! learned clauses than recursive minimization alone.
//!
//! Algorithm (`shrink=3` single-pass pipeline, matching Kissat/CaDiCaL):
//! 1. Sort learned clause by (decision level desc, trail position desc)
//!    — Kissat analyze.c:227-302
//! 2. Process blocks from the TAIL of the sorted clause (lowest levels first)
//!    so lower-level removability proofs warm the cache for higher blocks
//!    — Kissat shrink.c:371-377
//! 3. For each block of 2+ literals at the same level:
//!    a. Walk backward along the trail within that level, resolving reasons
//!    b. If block literals converge to a single literal, replace the block with it
//!    c. If resolution fails, fall back to per-literal minimization
//! 4. No flag reset. No second minimize pass. Removable/poison/keep caches
//!    persist across all blocks — Kissat minimize.c:175-178
//!
//! Reference: `reference/cadical/src/shrink.cpp` (507 lines)
//! Design: the development design notes
//! Design: the development design notes

use super::*;
use std::cmp::Ordering;

pub(in crate::solver) mod admitted;

const SMALL_SHRINK_SORT_LIMIT: usize = 32;

#[inline]
fn compare_shrink_entries(a: &(u32, usize, usize), b: &(u32, usize, usize)) -> Ordering {
    b.0.cmp(&a.0).then_with(|| b.1.cmp(&a.1))
}

#[inline]
fn sort_shrink_entries(entries: &mut [(u32, usize, usize)]) {
    if entries.len() <= SMALL_SHRINK_SORT_LIMIT {
        for i in 1..entries.len() {
            let mut j = i;
            while j > 0 && compare_shrink_entries(&entries[j], &entries[j - 1]).is_lt() {
                entries.swap(j, j - 1);
                j -= 1;
            }
        }
    } else {
        entries.sort_unstable_by(compare_shrink_entries);
    }
}

impl Solver {
    /// Shrink and minimize the learned clause in a single pass (`shrink=3`).
    ///
    /// Matches the Kissat/CaDiCaL `shrink=3` architecture:
    /// - Block-level shrinking with per-literal minimization fallback
    /// - Removable/poison/keep caches persist across all blocks
    /// - No flag reset between blocks, no second standalone minimize pass
    /// - Low-level blocks processed first to warm cache for higher blocks
    ///
    /// On block-UIP success, replaced literals are promoted to MIN_REMOVABLE
    /// (Kissat's `mark_shrinkable_as_removable` promotes every walked literal;
    /// `--sat-shrink-removable-kissat` does too) while MIN_VISITED is cleared,
    /// so MIN_VISITED still means "literal is currently in the learned clause."
    pub(super) fn shrink_and_minimize_learned_clause(&mut self) {
        use conflict_analysis_minimize::admitted::{Ordinary, ShrinkRoute};
        let route = match self.shrink_route_admitted(&Ordinary) {
            Ok(route) => route,
            Err(never) => match never {},
        };
        match route {
            ShrinkRoute::Plain => self.minimize_learned_clause(),
            ShrinkRoute::DistinctLevels => (),
            ShrinkRoute::RepeatedLevels(count) => {
                self.shrink_and_minimize_repeated_level_learned_clause(count)
            }
        }
    }

    pub(super) fn shrink_and_minimize_repeated_level_learned_clause(
        &mut self,
        learned_count: usize,
    ) {
        self.shrink_and_minimize_repeated_level_learned_clause_collect_removed(learned_count, None);
    }

    pub(super) fn shrink_and_minimize_repeated_level_learned_clause_collect_removed(
        &mut self,
        learned_count: usize,
        removed_lits: Option<&mut Vec<Literal>>,
    ) {
        match admitted::run(
            self,
            learned_count,
            removed_lits,
            &conflict_analysis_minimize::admitted::Ordinary,
        ) {
            Ok(()) => (),
            Err(never) => match never {},
        }
    }
}

#[cfg(test)]
#[path = "shrink_tests.rs"]
mod tests;

// Keep existing ordinary kernel controls on the shared implementation.
#[cfg(test)]
impl Solver {
    fn find_block_uip(&mut self, block: &[Literal], level: u32) -> Option<Literal> {
        match admitted::walk::find(
            self,
            block,
            level,
            &conflict_analysis_minimize::admitted::Ordinary,
        ) {
            Ok(value) => value,
            Err(never) => match never {},
        }
    }

    fn is_literal_removable_for_shrink(&mut self, lit: Literal) -> bool {
        match admitted::walk::removable(self, lit, &conflict_analysis_minimize::admitted::Ordinary)
        {
            Ok(value) => value,
            Err(never) => match never {},
        }
    }

    fn mark_shrink_walked_removable(&mut self, var: usize, level: u32) {
        match admitted::blocks::promote(
            self,
            var,
            level,
            &conflict_analysis_minimize::admitted::Ordinary,
        ) {
            Ok(()) => (),
            Err(never) => match never {},
        }
    }
}
