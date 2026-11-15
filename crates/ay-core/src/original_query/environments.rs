// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Operation-local persistent environments: flat rows, constant-size keys.

use super::*;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Environment(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Binding {
    Term {
        left: BinderId,
        right: BinderId,
        left_sort: SortId,
        right_sort: SortId,
    },
    Type {
        left: TypeParameterId,
        right: TypeParameterId,
    },
}

#[derive(Clone, Copy)]
struct Row {
    parent: Environment,
    binding: Binding,
}

#[derive(Default)]
pub(super) struct Environments {
    rows: BTreeMap<usize, Row>,
    intern: BTreeMap<(Environment, Binding), Environment>,
}

#[derive(Clone, Copy)]
enum Side {
    Left,
    Right,
}

impl Environments {
    fn append(
        &mut self,
        parent: Environment,
        binding: Binding,
        work: &mut WorkBudget<'_>,
    ) -> Result<Environment, QueryError> {
        work.tree(self.intern.len())?;
        if let Some(id) = self.intern.get(&(parent, binding)) {
            return Ok(*id);
        }
        work.tree(self.rows.len())?;
        let id = self
            .rows
            .len()
            .checked_add(1)
            .ok_or_else(|| work.exhausted())?;
        self.rows.insert(id, Row { parent, binding });
        work.tree(self.intern.len())?;
        self.intern.insert((parent, binding), Environment(id));
        Ok(Environment(id))
    }

    pub(super) fn term(
        &mut self,
        parent: Environment,
        left: &Binder,
        right: &Binder,
        work: &mut WorkBudget<'_>,
    ) -> Result<Environment, QueryError> {
        if self.find_term(parent, left.id, Side::Left, work)?.is_some()
            || self
                .find_term(parent, right.id, Side::Right, work)?
                .is_some()
        {
            return Err(QueryError::Invalid("duplicate active term-binder locator"));
        }
        self.append(
            parent,
            Binding::Term {
                left: left.id,
                right: right.id,
                left_sort: left.sort,
                right_sort: right.sort,
            },
            work,
        )
    }

    pub(super) fn parameter(
        &mut self,
        parent: Environment,
        left: &TypeParameter,
        right: &TypeParameter,
        work: &mut WorkBudget<'_>,
    ) -> Result<Environment, QueryError> {
        if self.find_type(parent, left.id, Side::Left, work)?.is_some()
            || self
                .find_type(parent, right.id, Side::Right, work)?
                .is_some()
        {
            return Err(QueryError::Invalid(
                "duplicate active type-parameter locator",
            ));
        }
        self.append(
            parent,
            Binding::Type {
                left: left.id,
                right: right.id,
            },
            work,
        )
    }

    fn row(&self, id: Environment, work: &mut WorkBudget<'_>) -> Result<Row, QueryError> {
        work.tree(self.rows.len())?;
        self.rows
            .get(&id.0)
            .copied()
            .ok_or(QueryError::Invalid("missing operation-local environment"))
    }

    fn find_term(
        &self,
        mut env: Environment,
        binder: BinderId,
        side: Side,
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<(Environment, SortId)>, QueryError> {
        while env.0 != 0 {
            work.charge(1)?;
            let row = self.row(env, work)?;
            if let Binding::Term {
                left,
                right,
                left_sort,
                right_sort,
            } = row.binding
            {
                let (id, sort) = match side {
                    Side::Left => (left, left_sort),
                    Side::Right => (right, right_sort),
                };
                if id == binder {
                    return Ok(Some((env, sort)));
                }
            }
            env = row.parent;
        }
        Ok(None)
    }

    fn find_type(
        &self,
        mut env: Environment,
        parameter: TypeParameterId,
        side: Side,
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<Environment>, QueryError> {
        while env.0 != 0 {
            work.charge(1)?;
            let row = self.row(env, work)?;
            if let Binding::Type { left, right } = row.binding {
                if match side {
                    Side::Left => left,
                    Side::Right => right,
                } == parameter
                {
                    return Ok(Some(env));
                }
            }
            env = row.parent;
        }
        Ok(None)
    }

    pub(super) fn term_sort(
        &self,
        env: Environment,
        binder: BinderId,
        work: &mut WorkBudget<'_>,
    ) -> Result<Option<SortId>, QueryError> {
        Ok(self
            .find_term(env, binder, Side::Left, work)?
            .map(|(_, sort)| sort))
    }

    pub(super) fn has_type(
        &self,
        env: Environment,
        parameter: TypeParameterId,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        Ok(self.find_type(env, parameter, Side::Left, work)?.is_some())
    }

    pub(super) fn terms_match(
        &self,
        env: Environment,
        left: BinderId,
        right: BinderId,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        let a = self
            .find_term(env, left, Side::Left, work)?
            .map(|(id, _)| id);
        let b = self
            .find_term(env, right, Side::Right, work)?
            .map(|(id, _)| id);
        Ok(a.is_some() && a == b)
    }

    pub(super) fn types_match(
        &self,
        env: Environment,
        left: TypeParameterId,
        right: TypeParameterId,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        let a = self.find_type(env, left, Side::Left, work)?;
        let b = self.find_type(env, right, Side::Right, work)?;
        Ok(a.is_some() && a == b)
    }
}

/// A flat, bounded-search stack; no large vector reallocation or recursive drop.
pub(super) struct WorkStack<T> {
    values: BTreeMap<usize, T>,
    next: usize,
}

impl<T> Default for WorkStack<T> {
    fn default() -> Self {
        Self {
            values: BTreeMap::new(),
            next: 0,
        }
    }
}

impl<T> WorkStack<T> {
    pub(super) fn push(&mut self, value: T, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
        work.tree(self.values.len())?;
        self.next = self.next.checked_add(1).ok_or_else(|| work.exhausted())?;
        self.values.insert(self.next, value);
        Ok(())
    }

    pub(super) fn pop(&mut self, work: &mut WorkBudget<'_>) -> Result<Option<T>, QueryError> {
        work.tree(self.values.len())?;
        Ok(self.values.pop_last().map(|(_, value)| value))
    }
}
