// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{reserve, Error, Owner, Result};
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Sort<'a> {
    Bool,
    BitVec(u32),
    Product(&'a str),
}

impl<'a> Sort<'a> {
    pub(super) fn read(sort: &'a ChcSort) -> Result<Self> {
        match sort {
            ChcSort::Bool => Ok(Self::Bool),
            ChcSort::BitVec(width) if *width > 0 && *width <= crate::MAX_BITVECTOR_WIDTH => {
                Ok(Self::BitVec(*width))
            }
            ChcSort::Datatype { name, .. } => Ok(Self::Product(name)),
            _ => Err(Error::Unsupported),
        }
    }

    pub(super) fn scalar(self) -> Result<ChcSort> {
        match self {
            Self::Bool => Ok(ChcSort::Bool),
            Self::BitVec(width) => Ok(ChcSort::BitVec(width)),
            Self::Product(_) => Err(Error::Unsupported),
        }
    }

    pub(super) fn matches(self, other: Self, owner: &mut Owner) -> Result<bool> {
        for sort in [self, other] {
            if let Self::Product(name) = sort {
                owner.admit(name.len(), 0)?;
            }
        }
        Ok(self == other)
    }
}

pub(super) struct Variables<'a> {
    pub(super) declarations: Vec<&'a ChcVar>,
    pub(super) frames: Vec<DetHashMap<&'a str, usize>>,
    parents: Vec<usize>,
}

impl<'a> Variables<'a> {
    pub(super) fn new(problem: &'a ChcProblem, path: &[usize], owner: &mut Owner) -> Result<Self> {
        let mut result = Self {
            declarations: Vec::new(),
            frames: Vec::new(),
            parents: Vec::new(),
        };
        reserve(&mut result.frames, path.len(), owner)?;
        for &index in path {
            let clause = problem.clauses().get(index).ok_or(Error::InvalidSource)?;
            let mut frame = DetHashMap::default();
            let mut seen = DetHashSet::default();
            for (_, arguments) in &clause.body.predicates {
                for argument in arguments {
                    result.collect(argument, &mut frame, &mut seen, owner)?;
                }
            }
            if let Some(constraint) = &clause.body.constraint {
                result.collect(constraint, &mut frame, &mut seen, owner)?;
            }
            if let ClauseHead::Predicate(_, arguments) = &clause.head {
                for argument in arguments {
                    result.collect(argument, &mut frame, &mut seen, owner)?;
                }
            }
            result.frames.push(frame);
        }
        result.join_columns(problem, path, owner)?;
        Ok(result)
    }

    fn collect(
        &mut self,
        root: &'a ChcExpr,
        frame: &mut DetHashMap<&'a str, usize>,
        seen: &mut DetHashSet<*const ChcExpr>,
        owner: &mut Owner,
    ) -> Result<()> {
        let mut pending = Vec::new();
        reserve(&mut pending, 1, owner)?;
        pending.push(root);
        while let Some(expr) = pending.pop() {
            owner.admit(1, std::mem::size_of::<usize>() * 4)?;
            if seen.try_reserve(1).is_err() {
                return owner.refuse(Error::Resource);
            }
            if !seen.insert(std::ptr::from_ref(expr)) {
                continue;
            }
            if let ChcExpr::Var(var) = expr {
                self.variable(var, frame, owner)?;
            }
            let children = crate::expr::dag::children(expr);
            reserve(&mut pending, children.len(), owner)?;
            pending.extend(children.iter().map(|child| child.as_ref()));
        }
        Ok(())
    }

    fn variable(
        &mut self,
        var: &'a ChcVar,
        frame: &mut DetHashMap<&'a str, usize>,
        owner: &mut Owner,
    ) -> Result<()> {
        owner.admit(var.name.len().saturating_add(1), 64)?;
        let sort = Sort::read(&var.sort)?;
        if let Some(&index) = frame.get(var.name.as_str()) {
            if !Sort::read(&self.declarations[index].sort)?.matches(sort, owner)? {
                return Err(Error::InvalidSource);
            }
            return Ok(());
        }
        if frame.try_reserve(1).is_err() {
            return owner.refuse(Error::Resource);
        }
        reserve(&mut self.declarations, 1, owner)?;
        reserve(&mut self.parents, 1, owner)?;
        let index = self.declarations.len();
        self.declarations.push(var);
        self.parents.push(index);
        frame.insert(var.name.as_str(), index);
        Ok(())
    }

    pub(super) fn root(&self, mut index: usize, owner: &mut Owner) -> Result<usize> {
        loop {
            owner.admit(1, 0)?;
            let parent = *self.parents.get(index).ok_or(Error::InvalidSource)?;
            if parent == index {
                return Ok(index);
            }
            index = parent;
        }
    }

    pub(super) fn lookup(&self, frame: usize, var: &ChcVar, owner: &mut Owner) -> Result<usize> {
        owner.admit(var.name.len().saturating_add(1), 0)?;
        let index = *self
            .frames
            .get(frame)
            .and_then(|vars| vars.get(var.name.as_str()))
            .ok_or(Error::InvalidSource)?;
        if !Sort::read(&self.declarations[index].sort)?.matches(Sort::read(&var.sort)?, owner)? {
            return Err(Error::InvalidSource);
        }
        self.root(index, owner)
    }

    fn join_columns(
        &mut self,
        problem: &ChcProblem,
        path: &[usize],
        owner: &mut Owner,
    ) -> Result<()> {
        for step in 1..path.len() {
            let previous = &problem.clauses()[path[step - 1]];
            let current = &problem.clauses()[path[step]];
            let ClauseHead::Predicate(head, head_args) = &previous.head else {
                return Err(Error::InvalidSource);
            };
            let [(body, body_args)] = current.body.predicates.as_slice() else {
                return Err(Error::InvalidSource);
            };
            if head != body || head_args.len() != body_args.len() {
                return Err(Error::InvalidSource);
            }
            for (left, right) in head_args.iter().zip(body_args) {
                owner.admit(1, 0)?;
                let (ChcExpr::Var(left), ChcExpr::Var(right)) = (left, right) else {
                    return Err(Error::Unsupported);
                };
                if !Sort::read(&left.sort)?.matches(Sort::read(&right.sort)?, owner)? {
                    return Err(Error::InvalidSource);
                }
                let left = self.lookup(step - 1, left, owner)?;
                let right = self.lookup(step, right, owner)?;
                self.parents[left.max(right)] = left.min(right);
            }
        }
        Ok(())
    }
}
