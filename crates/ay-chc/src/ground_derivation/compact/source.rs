// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Error, Owner, Result};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

mod expressions;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Type<'a> {
    Bool,
    BitVec(u32),
    Datatype(&'a str),
}

#[derive(Clone, Copy)]
pub(super) struct Function<'a> {
    pub sort: &'a str,
    pub field: Option<usize>,
}

pub(super) struct Source<'a> {
    pub problem: &'a ChcProblem,
    functions: DetHashMap<&'a str, Function<'a>>,
    selector_overloads: Vec<(&'a str, Function<'a>)>,
    checked: DetHashSet<(&'a str, crate::expr::ChcDtId)>,
    active: DetHashSet<&'a str>,
}

pub(super) struct Expressions<'a> {
    pub vars: DetHashMap<&'a str, Type<'a>>,
    cache: DetHashMap<usize, Type<'a>>,
}

impl<'a> Expressions<'a> {
    pub fn new() -> Self {
        Self {
            vars: DetHashMap::default(),
            cache: DetHashMap::default(),
        }
    }
}

impl<'a> Source<'a> {
    pub fn new(problem: &'a ChcProblem, owner: &mut Owner) -> Result<Self> {
        owner.poll()?;
        if problem.has_stripped_body_forall() {
            return Err(Error::InvalidSource);
        }
        let mut source = Self {
            problem,
            functions: DetHashMap::default(),
            selector_overloads: Vec::new(),
            checked: DetHashSet::default(),
            active: DetHashSet::default(),
        };
        for (sort, constructors) in problem.datatype_defs() {
            owner.admit(sort.len().saturating_add(1), 128)?;
            if sort.contains('\0') {
                return Err(Error::InvalidSource);
            }
            let [(constructor, fields)] = constructors.as_slice() else {
                return Err(Error::Unsupported);
            };
            source.add_function(constructor, Function { sort, field: None }, owner)?;
            for (index, (name, _)) in fields.iter().enumerate() {
                source.add_function(
                    name,
                    Function {
                        sort,
                        field: Some(index),
                    },
                    owner,
                )?;
            }
        }
        Ok(source)
    }

    fn add_function(
        &mut self,
        name: &'a str,
        function: Function<'a>,
        owner: &mut Owner,
    ) -> Result<()> {
        owner.admit(name.len().saturating_add(1), 128)?;
        if name.contains('\0') {
            return Err(Error::InvalidSource);
        }
        if let Some(previous) = self.functions.get(name) {
            // The parser deliberately supports selectors overloaded by their
            // datatype domain. Retain every owner rather than ending source
            // validation early and hiding a later invalid declaration.
            if previous.field.is_none()
                || function.field.is_none()
                || previous.sort == function.sort
            {
                return Err(Error::InvalidSource);
            }
            for (known_name, known) in &self.selector_overloads {
                owner.admit(known_name.len().saturating_add(known.sort.len()), 0)?;
                if *known_name == name && known.sort == function.sort {
                    return Err(Error::InvalidSource);
                }
            }
            owner.admit(1, std::mem::size_of::<(&str, Function<'_>)>())?;
            if self.selector_overloads.try_reserve_exact(1).is_err() {
                return owner.refuse(Error::Resource);
            }
            self.selector_overloads.push((name, function));
            return Ok(());
        }
        if self.functions.try_reserve(1).is_err() {
            return owner.refuse(Error::Resource);
        }
        self.functions.insert(name, function);
        Ok(())
    }

    /// A selector's argument domain uniquely identifies its declared owner.
    pub(super) fn function(
        &self,
        name: &str,
        domain: Option<&str>,
        owner: &mut Owner,
    ) -> Result<Function<'a>> {
        let first = *self.functions.get(name).ok_or(Error::Unsupported)?;
        if first.field.is_none() || domain == Some(first.sort) {
            return Ok(first);
        }
        let domain = domain.ok_or(Error::InvalidSource)?;
        for (candidate_name, candidate) in &self.selector_overloads {
            owner.admit(candidate_name.len().saturating_add(candidate.sort.len()), 0)?;
            if *candidate_name == name && candidate.sort == domain {
                return Ok(*candidate);
            }
        }
        Err(Error::InvalidSource)
    }

    /// Read a validated argument's domain from its source type, never from a
    /// candidate value that could have been assigned the wrong datatype.
    pub(super) fn datatype_domain(
        &mut self,
        expr: &'a ChcExpr,
        owner: &mut Owner,
        depth: usize,
    ) -> Result<Option<&'a str>> {
        owner.admit(1, 0)?;
        if depth > 512 {
            return Err(Error::Unsupported);
        }
        let sort = match expr {
            ChcExpr::Var(var) => &var.sort,
            ChcExpr::FuncApp(_, sort, _) => sort,
            ChcExpr::Op(ChcOp::Ite, args) => {
                return self.datatype_domain(
                    args.get(1).ok_or(Error::InvalidSource)?,
                    owner,
                    depth + 1,
                );
            }
            _ => return Ok(None),
        };
        Ok(match self.sort(sort, owner, 0)? {
            Type::Datatype(name) => Some(name),
            _ => None,
        })
    }

    pub fn sort(&mut self, sort: &'a ChcSort, owner: &mut Owner, depth: usize) -> Result<Type<'a>> {
        owner.admit(1, 0)?;
        if depth > 512 {
            return Err(Error::Unsupported);
        }
        match sort {
            ChcSort::Bool => Ok(Type::Bool),
            ChcSort::BitVec(width) if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width) => {
                Ok(Type::BitVec(*width))
            }
            ChcSort::Datatype { name, constructors } => {
                owner.admit(name.len(), 128)?;
                let (registered, definition) = self
                    .problem
                    .datatype_defs()
                    .get_key_value(name)
                    .ok_or(Error::InvalidSource)?;
                if self
                    .checked
                    .contains(&(registered.as_str(), constructors.id()))
                {
                    return Ok(Type::Datatype(registered));
                }
                let [(ctor, fields)] = definition.as_slice() else {
                    return Err(Error::Unsupported);
                };
                if constructors.len() != 1
                    || constructors[0].name != *ctor
                    || constructors[0].selectors.len() != fields.len()
                {
                    return Err(Error::InvalidSource);
                }
                if self.active.contains(registered.as_str()) {
                    return Err(Error::Unsupported);
                }
                if self.active.try_reserve(1).is_err() || self.checked.try_reserve(1).is_err() {
                    return owner.refuse(Error::Resource);
                }
                self.active.insert(registered);
                for (actual, (expected, field_sort)) in constructors[0].selectors.iter().zip(fields)
                {
                    owner.admit(
                        actual
                            .name
                            .len()
                            .saturating_add(expected.len())
                            .saturating_add(1),
                        0,
                    )?;
                    if actual.name != *expected || actual.sort != *field_sort {
                        return Err(Error::InvalidSource);
                    }
                    self.sort(field_sort, owner, depth + 1)?;
                }
                self.active.remove(registered.as_str());
                self.checked.insert((registered, constructors.id()));
                Ok(Type::Datatype(registered))
            }
            _ => Err(Error::Unsupported),
        }
    }

    pub fn validate(&mut self, owner: &mut Owner) -> Result<()> {
        let mut predicate_names = DetHashSet::default();
        for constructors in self.problem.datatype_defs().values() {
            for (_, fields) in constructors {
                for (_, sort) in fields {
                    self.sort(sort, owner, 0)?;
                }
            }
        }
        for (index, predicate) in self.problem.predicates().iter().enumerate() {
            owner.admit(predicate.name.len().saturating_add(1), 128)?;
            if predicate.id.index() != index
                || self.functions.contains_key(predicate.name.as_str())
                || predicate.name.contains('\0')
                || predicate_names.contains(predicate.name.as_str())
            {
                return Err(Error::InvalidSource);
            }
            if predicate_names.try_reserve(1).is_err() {
                return owner.refuse(Error::Resource);
            }
            predicate_names.insert(predicate.name.as_str());
            for sort in &predicate.arg_sorts {
                self.sort(sort, owner, 0)?;
            }
        }
        for clause in self.problem.clauses() {
            self.clause(clause, owner)?;
        }
        owner.poll()
    }

    pub fn clause(&mut self, clause: &'a HornClause, owner: &mut Owner) -> Result<Expressions<'a>> {
        owner.poll()?;
        if clause
            .action_id
            .is_some_and(|id| self.problem.action_name(id).is_none())
        {
            return Err(Error::InvalidSource);
        }
        let mut expressions = Expressions::new();
        for (predicate, args) in &clause.body.predicates {
            self.application(*predicate, args, &mut expressions, owner)?;
        }
        if let Some(guard) = &clause.body.constraint {
            if self.expression(guard, &mut expressions, owner, 0)? != Type::Bool {
                return Err(Error::InvalidSource);
            }
        }
        if let ClauseHead::Predicate(predicate, args) = &clause.head {
            self.application(*predicate, args, &mut expressions, owner)?;
        }
        Ok(expressions)
    }

    fn application(
        &mut self,
        id: PredicateId,
        args: &'a [ChcExpr],
        expressions: &mut Expressions<'a>,
        owner: &mut Owner,
    ) -> Result<()> {
        let predicate = self
            .problem
            .predicates()
            .get(id.index())
            .ok_or(Error::InvalidSource)?;
        if predicate.id != id || predicate.arg_sorts.len() != args.len() {
            return Err(Error::InvalidSource);
        }
        for (arg, expected) in args.iter().zip(&predicate.arg_sorts) {
            if self.expression(arg, expressions, owner, 0)? != self.sort(expected, owner, 0)? {
                return Err(Error::InvalidSource);
            }
        }
        Ok(())
    }

    pub fn value_type(&mut self, node: &super::ValueNode, owner: &mut Owner) -> Result<Type<'a>> {
        match node {
            super::ValueNode::Bool(_) => Ok(Type::Bool),
            super::ValueNode::BitVec { width, .. } => Ok(Type::BitVec(*width)),
            super::ValueNode::Datatype { sort, .. } => {
                owner.admit(sort.len().saturating_add(1), 0)?;
                self.problem
                    .datatype_defs()
                    .get_key_value(sort)
                    .map(|(name, _)| Type::Datatype(name.as_str()))
                    .ok_or(Error::InvalidValue)
            }
        }
    }
}

pub(super) fn operation_type<'a>(
    op: ChcOp,
    args: &[Type<'a>],
    owner: &mut Owner,
) -> Result<Type<'a>> {
    for arg in args {
        if let Type::Datatype(name) = arg {
            owner.admit(name.len(), 0)?;
        }
    }
    if matches!(op, ChcOp::Eq | ChcOp::Ne) && args.len() == 2 && args[0] == args[1] {
        return Ok(Type::Bool);
    }
    if op == ChcOp::Ite {
        return match args {
            [Type::Bool, left, right] if left == right => Ok(*left),
            _ => Err(Error::InvalidSource),
        };
    }
    owner.admit(
        args.len(),
        args.len().checked_mul(64).ok_or(Error::Resource)?,
    )?;
    let mut sorts = Vec::new();
    if sorts.try_reserve(args.len()).is_err() {
        return owner.refuse(Error::Resource);
    }
    for arg in args {
        sorts.push(match arg {
            Type::Bool => ChcSort::Bool,
            Type::BitVec(w) => ChcSort::BitVec(*w),
            Type::Datatype(_) => return Err(Error::Unsupported),
        });
    }
    match crate::pdr::validate_qf_operation(op, &sorts).map_err(|_| Error::InvalidSource)? {
        ChcSort::Bool => Ok(Type::Bool),
        ChcSort::BitVec(w) if (1..=crate::MAX_BITVECTOR_WIDTH).contains(&w) => Ok(Type::BitVec(w)),
        _ => Err(Error::Unsupported),
    }
}
