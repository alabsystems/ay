// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

pub(super) use super::environments::Environment;
use super::environments::{Environments, WorkStack};
use super::*;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Task {
    Node(NodeId, NodeId, Environment),
    Sort(SortId, SortId, Environment),
    Data(DataId, DataId, Environment),
}

pub(super) struct Engine<'a> {
    pub left: &'a QueryDraft,
    pub right: &'a QueryDraft,
    tasks: WorkStack<Task>,
    seen: BTreeSet<Task>,
    pub environments: Environments,
}

pub(super) fn matches(
    left: &QueryDraft,
    right: &QueryDraft,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(1)?;
    let mut engine = Engine {
        left,
        right,
        tasks: WorkStack::default(),
        seen: BTreeSet::new(),
        environments: Environments::default(),
    };
    if !engine.attributes(&left.typing, &right.typing, &Environment::default(), work)?
        || left.initial_lifetime != right.initial_lifetime
        || left.reset_assertions != right.reset_assertions
        || left.reset_lifetime != right.reset_lifetime
        || left.declarations.len() != right.declarations.len()
        || left.commands.len() != right.commands.len()
    {
        return Ok(false);
    }
    for (a, b) in left.declarations.iter().zip(&right.declarations) {
        work.charge(1)?;
        if !engine.declaration(a, b, work)? {
            return Ok(false);
        }
    }
    for (a, b) in left.commands.iter().zip(&right.commands) {
        work.charge(1)?;
        if !engine.command(a, b, work)? {
            return Ok(false);
        }
    }
    engine.run(work)
}

impl Engine<'_> {
    pub(super) fn node(
        &mut self,
        a: NodeId,
        b: NodeId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        work.charge(1)?;
        self.tasks.push(Task::Node(a, b, *env), work)
    }

    pub(super) fn sort(
        &mut self,
        a: SortId,
        b: SortId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        work.charge(1)?;
        self.tasks.push(Task::Sort(a, b, *env), work)
    }

    pub(super) fn data(
        &mut self,
        a: DataId,
        b: DataId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        work.charge(1)?;
        self.tasks.push(Task::Data(a, b, *env), work)
    }

    fn run(&mut self, work: &mut WorkBudget<'_>) -> Result<bool, QueryError> {
        while let Some(task) = self.tasks.pop(work)? {
            work.charge(1)?;
            work.tree(self.seen.len())?;
            if !self.seen.insert(task) {
                continue;
            }
            let equal = match task {
                Task::Node(a, b, env) => self.node_pair(a, b, &env, work)?,
                Task::Sort(a, b, env) => self.sort_pair(a, b, &env, work)?,
                Task::Data(a, b, env) => self.data_pair(a, b, &env, work)?,
            };
            if !equal {
                work.charge(0)?;
                return Ok(false);
            }
        }
        work.charge(0)?;
        Ok(true)
    }

    pub(super) fn nodes(
        &mut self,
        a: &[NodeId],
        b: &[NodeId],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        work.charge(1)?;
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            self.node(*a, *b, env, work)?;
        }
        Ok(true)
    }

    pub(super) fn sorts(
        &mut self,
        a: &[SortId],
        b: &[SortId],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        work.charge(1)?;
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            self.sort(*a, *b, env, work)?;
        }
        Ok(true)
    }

    pub(super) fn binders(
        &mut self,
        a: &[Binder],
        b: &[Binder],
        incoming: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<Environment>, QueryError> {
        if a.len() != b.len() {
            return Ok(None);
        }
        let mut env = *incoming;
        for (a, b) in a.iter().zip(b) {
            work.charge(1)?;
            work.text(&a.name.text)?;
            work.text(&b.name.text)?;
            self.sort(a.sort, b.sort, incoming, work)?;
            env = self.environments.term(env, a, b, work)?;
        }
        Ok(Some(env))
    }

    pub(super) fn type_parameters(
        &mut self,
        a: &[TypeParameter],
        b: &[TypeParameter],
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<Environment>, QueryError> {
        if a.len() != b.len() {
            return Ok(None);
        }
        let mut env = Environment::default();
        for (a, b) in a.iter().zip(b) {
            work.charge(1)?;
            work.text(&a.name.text)?;
            work.text(&b.name.text)?;
            env = self.environments.parameter(env, a, b, work)?;
        }
        Ok(Some(env))
    }
}
