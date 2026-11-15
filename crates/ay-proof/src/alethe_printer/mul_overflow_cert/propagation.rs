// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Occurrence-list worklist propagation, preserving the old ordered sweeps.
//!
//! This is the usual dependency worklist optimization of fixed-point iteration
//! (Kildall, "A Unified Approach to Global Program Optimization", POPL 1973).
//! A clause whose atoms did not change cannot change its propagation result.
//! Unlike a different watched-literal visitation order, ordering work by
//! `(sweep, clause index)` preserves the original reasons and conflict choice.
//! The index is advice only: callers still evaluate the complete original clause.

use super::super::emission_progress::EmissionProgress;
use super::localsat::{ChildSeed, Clause};
use super::term::T;
use ay_core::kani_compat::DetHashMap as HashMap;

mod queue;
use queue::Queue;

/// One shared remaining local allowance; no index or queue receives fresh credit.
pub(super) fn charge(budget: &mut u64, work: usize, progress: &EmissionProgress<'_>) -> Option<()> {
    progress.poll().then_some(())?;
    let remaining = u64::try_from(work).ok().and_then(|n| budget.checked_sub(n));
    match remaining {
        Some(remaining) => *budget = remaining,
        None => return exhausted(budget),
    }
    progress.poll().then_some(())
}

pub(super) fn exhausted<T>(budget: &mut u64) -> Option<T> {
    *budget = 0;
    None
}

/// Fallible scratch growth, admitted before allocation or relocation. Units are
/// logical element storage/copies, as with the existing clause-visit allowance;
/// this is not a claim to meter allocator internals or every hash-table probe.
pub(super) fn reserve<T>(
    values: &mut Vec<T>,
    additional: usize,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<()> {
    charge(budget, additional, progress)?;
    if values.capacity().saturating_sub(values.len()) < additional {
        charge(budget, values.len(), progress)?;
        if values.try_reserve(additional).is_err() {
            return exhausted(budget);
        }
    }
    progress.poll().then_some(())
}

#[derive(Default)]
pub(super) struct Occurrences {
    rows: HashMap<T, Vec<usize>>,
    clauses: usize,
}

#[cfg(test)]
thread_local! {
    static INDEX_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn index_builds() -> usize {
    INDEX_BUILDS.with(std::cell::Cell::get)
}

impl Occurrences {
    pub(super) fn new(
        db: &[Clause],
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Self> {
        charge(budget, 1, progress)?;
        #[cfg(test)]
        INDEX_BUILDS.with(|count| count.set(count.get() + 1));
        let mut index = Self::default();
        for clause in db {
            index.append(clause, budget, progress)?;
        }
        progress.poll().then_some(())?;
        Some(index)
    }

    /// Preserve every occurrence, including duplicate/opposite literals. Queue
    /// membership coalesces advice, never the original clause's literal count.
    pub(super) fn append(
        &mut self,
        clause: &Clause,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<()> {
        charge(budget, 1, progress)?;
        let Some(next) = self.clauses.checked_add(1) else {
            return exhausted(budget);
        };
        for &(atom, _) in clause {
            charge(budget, 1, progress)?;
            if !self.rows.contains_key(&atom) {
                if self.rows.len() == self.rows.capacity() {
                    charge(budget, self.rows.len(), progress)?;
                    if self.rows.try_reserve(1).is_err() {
                        return exhausted(budget);
                    }
                }
                self.rows.insert(atom, Vec::new());
                progress.poll().then_some(())?;
            }
            let rows = self.rows.get_mut(&atom)?;
            reserve(rows, 1, budget, progress)?;
            rows.push(self.clauses);
        }
        self.clauses = next;
        progress.poll().then_some(())
    }

    pub(super) fn sweep(&self, budget: &mut u64, progress: &EmissionProgress<'_>) -> Option<Sweep> {
        Some(Sweep {
            queue: Queue::all(self.clauses, budget, progress)?,
            clauses: self.clauses,
            round: 0,
            cursor: 0,
        })
    }

    /// A monotone child of a completed localsat fixed point only changes rows
    /// mentioning its decided atom. Queue the exact original occurrences in
    /// round zero; unlike a full initial sweep, other suffix rows are NOT
    /// implicitly pending. Later propagation uses the same cyclic row order.
    pub(super) fn sweep_after_decision(
        &self,
        seed: &ChildSeed<'_>,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Sweep> {
        charge(budget, 1, progress)?;
        let Some(atom) = seed.atom_for(self) else {
            return exhausted(budget);
        };
        let mut queue = Queue::sparse(self.clauses, budget, progress)?;
        if let Some(rows) = self.rows.get(&atom) {
            for &clause in rows {
                charge(budget, 1, progress)?;
                queue.insert((0, clause), budget, progress)?;
            }
        }
        progress.poll().then_some(())?;
        Some(Sweep {
            queue,
            clauses: self.clauses,
            round: 0,
            cursor: 0,
        })
    }
}

pub(super) struct Sweep {
    queue: Queue,
    clauses: usize,
    round: usize,
    cursor: usize,
}

impl Sweep {
    /// Outer None is refusal, inner None is a genuine propagation fixed point.
    pub(super) fn next(
        &mut self,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<Option<usize>> {
        let Some((round, clause)) = self.queue.pop(budget, progress)? else {
            progress.poll().then_some(())?;
            return Some(None);
        };
        self.round = round;
        self.cursor = clause;
        #[cfg(test)]
        tests::visited();
        Some(Some(clause))
    }

    pub(super) fn assigned(
        &mut self,
        index: &Occurrences,
        atom: T,
        budget: &mut u64,
        progress: &EmissionProgress<'_>,
    ) -> Option<()> {
        #[cfg(test)]
        tests::assigned(atom, self.cursor);
        charge(budget, 1, progress)?;
        if index.clauses != self.clauses {
            // Appending a row requires a new sweep, including the new row.
            return exhausted(budget);
        }
        if let Some(rows) = index.rows.get(&atom) {
            for &clause in rows {
                charge(budget, 1, progress)?;
                if self.queue.implicitly_pending(clause) {
                    // append records row IDs in nondecreasing order, including
                    // repeated literals. Every row in this suffix is already
                    // pending in the implicit initial sweep. Stop walking the
                    // occurrence suffix, not merely inserting each no-op notice.
                    // Later rounds still need both current- and next-round rows.
                    break;
                }
                let round = if clause > self.cursor {
                    self.round
                } else {
                    let Some(next) = self.round.checked_add(1) else {
                        return exhausted(budget);
                    };
                    next
                };
                self.queue.insert((round, clause), budget, progress)?;
            }
        }
        progress.poll().then_some(())
    }
}

#[cfg(test)]
mod tests;
