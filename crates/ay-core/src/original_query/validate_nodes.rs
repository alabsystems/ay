// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

pub(super) use super::environments::Environment;
use super::environments::{Environments, WorkStack};
use super::validate_headers::{invalid, sort_ref, symbol};
use super::*;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Task {
    Node(NodeId, Environment),
    Sort(SortId, Environment),
    Data(DataId, Environment),
}

pub(super) struct Walker<'a> {
    draft: &'a QueryDraft,
    visible: &'a BTreeSet<DeclId>,
    tasks: WorkStack<Task>,
    seen: BTreeSet<Task>,
    environments: Environments,
}

impl<'a> Walker<'a> {
    pub(super) fn new(draft: &'a QueryDraft, visible: &'a BTreeSet<DeclId>) -> Self {
        Self {
            draft,
            visible,
            tasks: WorkStack::default(),
            seen: BTreeSet::new(),
            environments: Environments::default(),
        }
    }

    pub(super) fn types(
        &mut self,
        incoming: Environment,
        params: &[TypeParameter],
        work: &mut WorkBudget<'_>,
    ) -> Result<Environment, QueryError> {
        let mut env = incoming;
        for param in params {
            work.charge(1)?;
            symbol(&param.name, work)?;
            env = self.environments.parameter(env, param, param, work)?;
        }
        Ok(env)
    }

    pub(super) fn parameters(
        &mut self,
        incoming: Environment,
        binders: &[Binder],
        work: &mut WorkBudget<'_>,
    ) -> Result<Environment, QueryError> {
        let mut env = incoming;
        for binder in binders {
            work.charge(1)?;
            symbol(&binder.name, work)?;
            self.sort(binder.sort, &incoming, work)?;
            env = self.environments.term(env, binder, binder, work)?;
        }
        Ok(env)
    }

    pub(super) fn attributes(
        &mut self,
        attrs: &[Attribute],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        for attr in attrs {
            work.charge(1)?;
            if let Some(id) = attr.value {
                self.data(id, env, work)?;
            }
        }
        Ok(())
    }

    pub(super) fn data(
        &mut self,
        id: DataId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        if id.0 as usize >= self.draft.data.len() {
            return Err(invalid("missing structured payload"));
        }
        self.tasks.push(Task::Data(id, *env), work)
    }

    pub(super) fn node(
        &mut self,
        id: NodeId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        validate_headers::node_ref(self.draft, id)?;
        self.tasks.push(Task::Node(id, *env), work)
    }

    pub(super) fn sort(
        &mut self,
        id: SortId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        sort_ref(self.draft, id)?;
        self.tasks.push(Task::Sort(id, *env), work)
    }

    pub(super) fn run(&mut self, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
        while let Some(task) = self.tasks.pop(work)? {
            work.tree(self.seen.len())?;
            if !self.seen.insert(task) {
                continue;
            }
            match task {
                Task::Node(id, env) => self.node_children(id, &env, work)?,
                Task::Sort(id, env) => self.sort_children(id, &env, work)?,
                Task::Data(id, env) => self.data_children(id, &env, work)?,
            }
        }
        work.charge(0)
    }

    fn visible(&self, id: DeclId, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
        work.tree(self.visible.len())?;
        if self.visible.contains(&id) {
            Ok(())
        } else {
            Err(invalid("declaration is not visible at this occurrence"))
        }
    }

    fn head_scope(
        &self,
        head: &OperatorHead,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        match head {
            OperatorHead::Declaration(id) => self.visible(*id, work),
            OperatorHead::Bound(id) if self.environments.term_sort(*env, *id, work)?.is_none() => {
                Err(invalid("unbound operator"))
            }
            _ => Ok(()),
        }
    }

    fn data_children(
        &mut self,
        id: DataId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        let draft = self.draft;
        match &draft.data[id.0 as usize] {
            DataNode::Reference(head) => self.head_scope(head, env, work),
            DataNode::List(children) => {
                for child in children {
                    self.data(*child, env, work)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn index_scope(
        &self,
        indices: &[IndexToken],
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        for index in indices {
            work.charge(1)?;
            if let IndexToken::Reference { reference, .. } = index {
                self.head_scope(reference, env, work)?;
            }
        }
        Ok(())
    }

    fn sort_children(
        &mut self,
        id: SortId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        let draft = self.draft;
        match &draft.sorts[id.0 as usize] {
            SortNode::Parameter(id) if !self.environments.has_type(*env, *id, work)? => {
                return Err(invalid("unbound type parameter"))
            }
            SortNode::Parameter(_) => {}
            SortNode::Builtin {
                indices, arguments, ..
            } => {
                self.index_scope(indices, env, work)?;
                for child in arguments {
                    self.sort(*child, env, work)?;
                }
            }
            SortNode::Nominal {
                declaration,
                arguments,
            } => {
                self.visible(*declaration, work)?;
                for child in arguments {
                    self.sort(*child, env, work)?;
                }
            }
        }
        Ok(())
    }

    fn node_children(
        &mut self,
        id: NodeId,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        let draft = self.draft;
        let node = &draft.nodes[id.0 as usize];
        self.sort(node.sort, env, work)?;
        match &node.kind {
            NodeKind::Literal(_) => {}
            NodeKind::Free(id) => self.visible(*id, work)?,
            NodeKind::Bound(id) => {
                if self.environments.term_sort(*env, *id, work)? != Some(node.sort) {
                    return Err(invalid("unbound variable or binder sort mismatch"));
                }
            }
            NodeKind::Apply {
                operator,
                arguments,
            } => {
                self.head_scope(&operator.head, env, work)?;
                self.index_scope(&operator.indices, env, work)?;
                if let Some(sort) = operator.qualification {
                    self.sort(sort, env, work)?;
                }
                for child in arguments {
                    self.node(*child, env, work)?;
                }
            }
            NodeKind::Let { bindings, body } => {
                let mut bound = *env;
                for binding in bindings {
                    // Values and binder sorts see the incoming scope only.
                    self.node(binding.value, env, work)?;
                    bound = self.parameters(bound, std::slice::from_ref(&binding.binder), work)?;
                }
                self.node(*body, &bound, work)?;
            }
            NodeKind::Quantified { binders, body, .. } => {
                let bound = self.parameters(*env, binders, work)?;
                self.node(*body, &bound, work)?;
            }
            NodeKind::Match { scrutinee, cases } => {
                self.node(*scrutinee, env, work)?;
                for case in cases {
                    let bound = self.pattern(&case.pattern, env, work)?;
                    self.node(case.body, &bound, work)?;
                }
            }
            NodeKind::Annotated { body, attributes } => {
                self.node(*body, env, work)?;
                self.attributes(attributes, env, work)?;
            }
        }
        Ok(())
    }

    fn pattern(
        &mut self,
        pattern: &MatchPattern,
        env: &Environment,
        work: &mut WorkBudget<'_>,
    ) -> Result<Environment, QueryError> {
        let mut bound = *env;
        match pattern {
            MatchPattern::Variable(binder) => {
                bound = self.parameters(*env, std::slice::from_ref(binder), work)?
            }
            MatchPattern::Wildcard => {}
            MatchPattern::Constructor {
                declaration,
                fields,
            } => {
                self.visible(*declaration, work)?;
                for field in fields {
                    work.charge(1)?;
                    match field {
                        PatternField::Binder(binder) => {
                            bound = self.parameters(bound, std::slice::from_ref(binder), work)?
                        }
                        PatternField::Wildcard(sort) => self.sort(*sort, env, work)?,
                    }
                }
            }
        }
        Ok(bound)
    }
}
