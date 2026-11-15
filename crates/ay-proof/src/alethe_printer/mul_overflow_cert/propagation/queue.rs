// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An ordered cyclic set with a hierarchy of nonempty-word summaries.
//!
//! A full initial sweep is the implicit suffix `[cursor, clauses)`; its
//! already-pending clauses need no bitmap lookup, insertion or removal. The
//! sparse initial mode instead starts empty and only visits explicit seeds;
//! its first round has no implicit suffix. In both modes the
//! lowest level has one bit per other queued clause; each higher level has
//! one bit per nonempty word below it. A successor lookup skips empty ranges
//! by consulting their summaries, rather than scanning empty words. Each word
//! examination/update and every scratch growth uses the original allowance
//! and owner. No heap comparisons or entry relocation are needed.

use super::{charge, exhausted, reserve, EmissionProgress};

type Entry = (usize, usize);
const WORD_BITS: usize = u64::BITS as usize;

enum Initial {
    Full,
    Sparse,
}

pub(super) struct Queue {
    levels: Vec<Vec<u64>>,
    clauses: usize,
    initial: Initial,
    round: usize,
    /// The first index not yet visited in this round. Pending lower indices
    /// belong to the next round; assignment never schedules a later round.
    cursor: usize,
}

impl Queue {
    pub(super) fn all(
        clauses: usize,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Self> {
        Self::new(clauses, Initial::Full, budget, progress)
    }

    pub(super) fn sparse(
        clauses: usize,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Self> {
        Self::new(clauses, Initial::Sparse, budget, progress)
    }

    fn new(
        clauses: usize,
        initial: Initial,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Self> {
        charge(budget, 1, progress)?;
        let mut levels = Vec::new();
        let mut bits = clauses;
        while bits != 0 {
            let len = bits.div_ceil(WORD_BITS);
            let mut words = Vec::new();
            reserve(&mut words, len, budget, progress)?;
            for _ in 0..len {
                charge(budget, 1, progress)?;
                #[cfg(test)]
                tests::bitmap_access();
                words.push(0);
            }
            reserve(&mut levels, 1, budget, progress)?;
            levels.push(words);
            if len == 1 {
                break;
            }
            bits = len;
        }
        progress.poll().then_some(())?;
        Some(Self {
            levels,
            clauses,
            initial,
            round: 0,
            cursor: 0,
        })
    }

    pub(super) fn implicitly_pending(&self, clause: usize) -> bool {
        matches!(self.initial, Initial::Full)
            && self.round == 0
            && clause >= self.cursor
            && clause < self.clauses
    }

    pub(super) fn insert(
        &mut self,
        entry: Entry,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<()> {
        charge(budget, 1, progress)?;
        if entry.1 >= self.clauses {
            return exhausted(budget);
        }
        let round = if entry.1 < self.cursor {
            let Some(next) = self.round.checked_add(1) else {
                return exhausted(budget);
            };
            next
        } else {
            self.round
        };
        if entry.0 != round {
            return exhausted(budget);
        }
        if self.implicitly_pending(entry.1) {
            // This clause is already in the implicit initial suffix.
            return progress.poll().then_some(());
        }
        let mut bit = entry.1;
        for words in &mut self.levels {
            charge(budget, 1, progress)?;
            #[cfg(test)]
            tests::bitmap_access();
            let word = words.get_mut(bit / WORD_BITS)?;
            let mask = 1u64 << (bit % WORD_BITS);
            if *word & mask != 0 {
                break;
            }
            let was_empty = *word == 0;
            charge(budget, 1, progress)?;
            *word |= mask;
            if !was_empty {
                break;
            }
            bit /= WORD_BITS;
        }
        progress.poll().then_some(())
    }

    /// First set bit at/after `first` in one level, with no linear empty-word
    /// scan. The recursion climbs/descends at most the fixed word hierarchy.
    fn successor(
        &self,
        level: usize,
        first: usize,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Option<usize>> {
        charge(budget, 1, progress)?;
        let Some(words) = self.levels.get(level) else {
            return Some(None);
        };
        let word = first / WORD_BITS;
        #[cfg(test)]
        tests::bitmap_access();
        let Some(&value) = words.get(word) else {
            return Some(None);
        };
        let masked = value & (u64::MAX << (first % WORD_BITS));
        if masked != 0 {
            return Some(Some(word * WORD_BITS + masked.trailing_zeros() as usize));
        }
        let Some(next) = self.successor(level + 1, word + 1, budget, progress)? else {
            return Some(None);
        };
        charge(budget, 1, progress)?;
        #[cfg(test)]
        tests::bitmap_access();
        let value = *words.get(next)?;
        if value == 0 {
            return exhausted(budget);
        }
        Some(Some(next * WORD_BITS + value.trailing_zeros() as usize))
    }

    fn remove(
        &mut self,
        mut bit: usize,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<()> {
        for words in &mut self.levels {
            charge(budget, 1, progress)?;
            #[cfg(test)]
            tests::bitmap_access();
            let word = words.get_mut(bit / WORD_BITS)?;
            let mask = 1u64 << (bit % WORD_BITS);
            charge(budget, 1, progress)?;
            *word &= !mask;
            if *word != 0 {
                break;
            }
            bit /= WORD_BITS;
        }
        progress.poll().then_some(())
    }

    pub(super) fn pop(
        &mut self,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Option<Entry>> {
        charge(budget, 1, progress)?;
        if self.implicitly_pending(self.cursor) {
            // The first round visits every clause in order. Only notices for
            // its visited prefix are stored, for the following round.
            let clause = self.cursor;
            let Some(next) = clause.checked_add(1) else {
                return exhausted(budget);
            };
            self.cursor = next;
            progress.poll().then_some(())?;
            return Some(Some((0, clause)));
        }
        #[cfg(test)]
        tests::bitmap_access();
        if self
            .levels
            .last()
            .and_then(|words| words.first())
            .copied()
            .unwrap_or(0)
            == 0
        {
            return Some(None);
        }
        let clause = match self.successor(0, self.cursor, budget, progress)? {
            Some(clause) => clause,
            None => {
                let Some(next) = self.round.checked_add(1) else {
                    return exhausted(budget);
                };
                self.round = next;
                self.successor(0, 0, budget, progress)??
            }
        };
        self.remove(clause, budget, progress)?;
        let Some(next) = clause.checked_add(1) else {
            return exhausted(budget);
        };
        self.cursor = next;
        progress.poll().then_some(())?;
        Some(Some((self.round, clause)))
    }
}

#[cfg(test)]
mod tests;
