// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lazy cost-bounded depth-first search over original clause occurrences.
//! Queries take turns after each explicit search transition, not after a whole
//! unsuccessful subtree. One shared caller control governs every cost layer.

use super::{Derivation, QuantifiedChcProblem, SourceControl};

mod cursor;
mod index;
mod output;

use cursor::Cursor;
use index::Index;

enum CursorStep {
    Progress,
    Candidate(Derivation),
    Finished,
}

pub(super) enum Step {
    Pending,
    Candidate(Derivation),
    Exhausted,
}

pub(super) struct Search<'a> {
    index: Index<'a>,
    queries: Vec<Cursor>,
    next_query: usize,
    active: usize,
    stopped: bool,
}

impl<'a> Search<'a> {
    pub(super) fn new(
        problem: &'a QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> Option<Self> {
        let index = Index::new(problem, control)?;
        let mut queries = Vec::new();
        for (clause, source) in index.clauses.iter().enumerate() {
            control.charge(1)?;
            if matches!(source.head, crate::ClauseHead::False) {
                if let Some(cost) = index.costs[clause] {
                    control.bytes(std::mem::size_of::<Cursor>().checked_mul(2)?)?;
                    queries.try_reserve(1).ok()?;
                    queries.push(Cursor::new(clause, cost, &index, control)?);
                }
            }
        }
        let active = queries.len();
        control.poll()?;
        Some(Self {
            index,
            queries,
            next_query: 0,
            active,
            stopped: false,
        })
    }

    pub(super) fn step(&mut self, control: &SourceControl<'_>) -> Option<Step> {
        if self.stopped {
            return None;
        }
        let result = self.step_inner(control);
        if result.is_none() {
            // Refusal cannot be revived by passing a fresh control or resetting
            // the caller's token to this cursor.
            self.stopped = true;
        }
        result
    }

    fn step_inner(&mut self, control: &SourceControl<'_>) -> Option<Step> {
        control.poll()?;
        if self.active == 0 {
            return Some(Step::Exhausted);
        }
        let count = self.queries.len();
        let query = self.queries.get_mut(self.next_query)?;
        self.next_query = self.next_query.checked_add(1)? % count;
        if query.finished() {
            return Some(Step::Pending);
        }
        let result = match query.advance(&self.index, control)? {
            CursorStep::Progress => Step::Pending,
            CursorStep::Finished => {
                self.active = self.active.checked_sub(1)?;
                if self.active == 0 {
                    Step::Exhausted
                } else {
                    Step::Pending
                }
            }
            CursorStep::Candidate(candidate) => Step::Candidate(candidate),
        };
        control.poll()?;
        Some(result)
    }

    #[cfg(test)]
    pub(super) fn next(&mut self, control: &SourceControl<'_>) -> Option<Derivation> {
        loop {
            match self.step(control)? {
                Step::Pending => {}
                Step::Candidate(candidate) => return Some(candidate),
                Step::Exhausted => return None,
            }
        }
    }
}

#[cfg(test)]
mod tests;
