// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit-stack iterative cost deepening for one original query.

use super::CursorStep as Step;
use super::*;

pub(super) struct Occurrence {
    pub(super) clause: usize,
    pub(super) children: Vec<Option<usize>>,
}

#[derive(Clone, Copy)]
struct Goal {
    parent: usize,
    position: usize,
    predicate: usize,
}

struct Choice {
    goal: Goal,
    next: usize,
    nodes_before: usize,
    pending_before: usize,
    bound_before: usize,
}

enum Phase {
    Descend,
    Choose,
    Retreat,
    Finished,
}

pub(super) struct Cursor {
    nodes: Vec<Occurrence>,
    pending: Vec<Goal>,
    choices: Vec<Choice>,
    phase: Phase,
    lower_bound: usize,
    limit: usize,
    next_limit: Option<usize>,
}

impl Cursor {
    pub(super) fn new(
        query: usize,
        cost: usize,
        index: &Index<'_>,
        control: &SourceControl<'_>,
    ) -> Option<Self> {
        let mut cursor = Self {
            nodes: Vec::new(),
            pending: Vec::new(),
            choices: Vec::new(),
            phase: Phase::Descend,
            lower_bound: cost,
            limit: cost,
            next_limit: None,
        };
        cursor.append(query, index, control)?;
        Some(cursor)
    }

    pub(super) fn finished(&self) -> bool {
        matches!(self.phase, Phase::Finished)
    }

    pub(super) fn advance(
        &mut self,
        index: &Index<'_>,
        control: &SourceControl<'_>,
    ) -> Option<Step> {
        control.charge(1)?;
        match self.phase {
            Phase::Descend => self.descend(control),
            Phase::Choose => self.choose(index, control),
            Phase::Retreat => self.retreat(control),
            Phase::Finished => Some(Step::Finished),
        }
    }

    fn descend(&mut self, control: &SourceControl<'_>) -> Option<Step> {
        let Some(goal) = self.pending.pop() else {
            self.phase = Phase::Retreat;
            // Earlier cost layers already emitted all smaller complete trees.
            return if self.nodes.len() == self.limit {
                Some(Step::Candidate(output::postorder(&self.nodes, control)?))
            } else {
                Some(Step::Progress)
            };
        };
        control.bytes(std::mem::size_of::<Choice>().checked_mul(2)?)?;
        self.choices.try_reserve(1).ok()?;
        self.choices.push(Choice {
            goal,
            next: 0,
            nodes_before: self.nodes.len(),
            pending_before: self.pending.len(),
            bound_before: self.lower_bound,
        });
        self.phase = Phase::Choose;
        Some(Step::Progress)
    }

    fn choose(&mut self, index: &Index<'_>, control: &SourceControl<'_>) -> Option<Step> {
        let choice = self.choices.last_mut()?;
        let definitions = index.definitions.get(choice.goal.predicate)?;
        let Some(&clause) = definitions.get(choice.next) else {
            let choice = self.choices.pop()?;
            // Descendant choices restore their consumed goals before returning
            // here. That makes each ancestor's pending-length rollback exact.
            control.bytes(std::mem::size_of::<Goal>().checked_mul(2)?)?;
            self.pending.try_reserve(1).ok()?;
            self.pending.push(choice.goal);
            self.phase = Phase::Retreat;
            return Some(Step::Progress);
        };
        choice.next = choice.next.checked_add(1)?;
        let Some(cost) = index.costs[clause] else {
            return Some(Step::Progress);
        };
        let rest = choice
            .bound_before
            .checked_sub(index.minimum[choice.goal.predicate]?)?;
        let Some(bound) = rest.checked_add(cost) else {
            // This alternative cannot fit a representable complete vector;
            // retain other alternatives and independent query cursors.
            return Some(Step::Progress);
        };
        if bound > self.limit {
            self.next_limit = Some(self.next_limit.map_or(bound, |old| old.min(bound)));
            return Some(Step::Progress);
        }
        let goal = choice.goal;
        let child = self.nodes.len();
        self.append(clause, index, control)?;
        *self
            .nodes
            .get_mut(goal.parent)?
            .children
            .get_mut(goal.position)? = Some(child);
        self.lower_bound = bound;
        self.phase = Phase::Descend;
        Some(Step::Progress)
    }

    fn retreat(&mut self, control: &SourceControl<'_>) -> Option<Step> {
        if let Some(choice) = self.choices.last() {
            control.charge(self.nodes.len().checked_sub(choice.nodes_before)?)?;
            control.charge(self.pending.len().checked_sub(choice.pending_before)?)?;
            self.nodes.truncate(choice.nodes_before);
            self.pending.truncate(choice.pending_before);
            *self
                .nodes
                .get_mut(choice.goal.parent)?
                .children
                .get_mut(choice.goal.position)? = None;
            self.lower_bound = choice.bound_before;
            self.phase = Phase::Choose;
            return Some(Step::Progress);
        }
        if let Some(next) = self.next_limit.take() {
            if next <= self.limit {
                return None;
            }
            self.limit = next;
            self.phase = Phase::Descend;
            Some(Step::Progress)
        } else {
            self.phase = Phase::Finished;
            Some(Step::Finished)
        }
    }

    fn append(
        &mut self,
        clause: usize,
        index: &Index<'_>,
        control: &SourceControl<'_>,
    ) -> Option<()> {
        let body = &index.clauses.get(clause)?.body.predicates;
        control.charge(body.len().checked_add(1)?)?;
        control.bytes(std::mem::size_of::<Occurrence>().checked_mul(2)?)?;
        control.bytes(body.len().checked_mul(
            std::mem::size_of::<Option<usize>>() + 2 * std::mem::size_of::<Goal>(),
        )?)?;
        let mut children = Vec::new();
        children.try_reserve_exact(body.len()).ok()?;
        self.nodes.try_reserve(1).ok()?;
        self.pending.try_reserve(body.len()).ok()?;
        for _ in body {
            control.charge(1)?;
            children.push(None);
        }
        let parent = self.nodes.len();
        self.nodes.push(Occurrence { clause, children });
        for (position, (predicate, _)) in body.iter().enumerate().rev() {
            control.charge(1)?;
            self.pending.push(Goal {
                parent,
                position,
                predicate: predicate.index(),
            });
        }
        Some(())
    }
}
