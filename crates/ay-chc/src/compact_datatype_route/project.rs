// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::variables::{Sort, Variables};
use super::{reserve, Error, Owner, Result, MAX_DEPTH};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcVar};
use ay_core::kani_compat::DetHashMap;
use std::fmt::Write;
use std::sync::Arc;

pub(super) struct Demand<'a> {
    pub(super) root: usize,
    pub(super) path: Vec<usize>,
    pub(super) sort: Sort<'a>,
    pub(super) name: String,
}

pub(super) struct Projection<'a> {
    pub(super) formula: ChcExpr,
    pub(super) demands: Vec<Demand<'a>>,
    indices: DetHashMap<(usize, Vec<usize>), usize>,
}

impl<'a> Projection<'a> {
    pub(super) fn new(
        problem: &'a ChcProblem,
        path: &[usize],
        variables: &Variables<'a>,
        owner: &mut Owner<'_>,
    ) -> Result<Self> {
        let mut projection = Self {
            formula: ChcExpr::Bool(true),
            demands: Vec::new(),
            indices: DetHashMap::default(),
        };
        let mut constraints = Vec::new();
        reserve(&mut constraints, path.len(), owner)?;
        for (frame, &index) in path.iter().enumerate() {
            if let Some(expr) = &problem.clauses()[index].body.constraint {
                let mut memo = DetHashMap::default();
                constraints.push(
                    projection.expression(problem, variables, frame, expr, 0, &mut memo, owner)?,
                );
            }
        }
        projection.formula = ChcExpr::Op(ChcOp::And, constraints);
        Ok(projection)
    }

    fn expression(
        &mut self,
        problem: &'a ChcProblem,
        variables: &Variables<'a>,
        frame: usize,
        expr: &'a ChcExpr,
        depth: usize,
        memo: &mut DetHashMap<*const ChcExpr, Arc<ChcExpr>>,
        owner: &mut Owner<'_>,
    ) -> Result<Arc<ChcExpr>> {
        owner.admit(1, 0)?;
        if depth >= MAX_DEPTH {
            return owner.refuse(Error::Resource);
        }
        let key = std::ptr::from_ref(expr);
        if let Some(value) = memo.get(&key) {
            return Ok(Arc::clone(value));
        }
        owner.admit(1, std::mem::size_of::<ChcExpr>() + 80)?;
        let rewritten = match expr {
            ChcExpr::Bool(value) => ChcExpr::Bool(*value),
            ChcExpr::BitVec(value, width) => ChcExpr::BitVec(*value, *width),
            ChcExpr::Var(_) | ChcExpr::FuncApp(..) => {
                let read = read(problem, variables, frame, expr, owner)?;
                self.scalar(read, owner)?
            }
            ChcExpr::Op(op, children) if scalar_operation(*op) => {
                let mut output = Vec::new();
                reserve(&mut output, children.len(), owner)?;
                for child in children {
                    output.push(self.expression(
                        problem,
                        variables,
                        frame,
                        child,
                        depth + 1,
                        memo,
                        owner,
                    )?);
                }
                ChcExpr::Op(*op, output)
            }
            _ => return Err(Error::Unsupported),
        };
        if memo.try_reserve(1).is_err() {
            return owner.refuse(Error::Resource);
        }
        let value = Arc::new(rewritten);
        memo.insert(key, Arc::clone(&value));
        Ok(value)
    }

    fn scalar(&mut self, read: Read<'a>, owner: &mut Owner<'_>) -> Result<ChcExpr> {
        let sort = read.sort.scalar()?;
        owner.admit(read.path.len().saturating_add(1), 0)?;
        let key = (read.root, read.path);
        if let Some(&index) = self.indices.get(&key) {
            let demand = &self.demands[index];
            if demand.sort != read.sort {
                return Err(Error::InvalidSource);
            }
            return Ok(ChcExpr::Var(ChcVar::new(
                super::text(&demand.name, owner)?,
                sort,
            )));
        }
        owner.admit(1, 128)?;
        if self.indices.try_reserve(1).is_err() {
            return owner.refuse(Error::Resource);
        }
        let index = self.demands.len();
        // No original variables survive in the projected namespace.
        let mut name = String::new();
        if name.try_reserve(64).is_err() || write!(&mut name, "compact_leaf_{index}").is_err() {
            return owner.refuse(Error::Resource);
        }
        let mut path = Vec::new();
        reserve(&mut path, key.1.len(), owner)?;
        path.extend_from_slice(&key.1);
        let variable = ChcVar::new(super::text(&name, owner)?, sort);
        reserve(&mut self.demands, 1, owner)?;
        self.demands.push(Demand {
            root: read.root,
            path,
            sort: read.sort,
            name,
        });
        self.indices.insert(key, index);
        Ok(ChcExpr::Var(variable))
    }
}

struct Read<'a> {
    root: usize,
    path: Vec<usize>,
    sort: Sort<'a>,
}

fn read<'a>(
    problem: &'a ChcProblem,
    variables: &Variables<'a>,
    frame: usize,
    mut expr: &'a ChcExpr,
    owner: &mut Owner<'_>,
) -> Result<Read<'a>> {
    let mut selectors = Vec::new();
    while let ChcExpr::FuncApp(name, sort, args) = expr {
        if args.len() != 1 {
            return Err(Error::Unsupported);
        }
        if selectors.len() >= MAX_DEPTH {
            return owner.refuse(Error::Resource);
        }
        reserve(&mut selectors, 1, owner)?;
        selectors.push((name.as_str(), sort));
        expr = &args[0];
    }
    let ChcExpr::Var(var) = expr else {
        return Err(Error::Unsupported);
    };
    let root = variables.lookup(frame, var, owner)?;
    let mut sort = Sort::read(&var.sort)?;
    let mut path = Vec::new();
    reserve(&mut path, selectors.len(), owner)?;
    for (selector, stated) in selectors.into_iter().rev() {
        let Sort::Product(name) = sort else {
            return Err(Error::Unsupported);
        };
        owner.admit(name.len().saturating_add(selector.len()), 0)?;
        let definitions = problem
            .datatype_defs()
            .get(name)
            .ok_or(Error::InvalidSource)?;
        let [(_, fields)] = definitions.as_slice() else {
            return Err(Error::Unsupported);
        };
        let mut selected = None;
        for (index, (field, field_sort)) in fields.iter().enumerate() {
            owner.admit(field.len().saturating_add(1), 0)?;
            if field == selector {
                if selected.is_some() {
                    return Err(Error::InvalidSource);
                }
                selected = Some((index, Sort::read(field_sort)?));
            }
        }
        let (index, next) = selected.ok_or(Error::Unsupported)?;
        if !next.matches(Sort::read(stated)?, owner)? {
            return Err(Error::InvalidSource);
        }
        sort = next;
        path.push(index);
    }
    Ok(Read { root, path, sort })
}

fn scalar_operation(op: ChcOp) -> bool {
    matches!(
        op,
        ChcOp::Not
            | ChcOp::And
            | ChcOp::Or
            | ChcOp::Implies
            | ChcOp::Iff
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::Ite
            | ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvUDiv
            | ChcOp::BvURem
            | ChcOp::BvSDiv
            | ChcOp::BvSRem
            | ChcOp::BvSMod
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
            | ChcOp::BvNot
            | ChcOp::BvNeg
            | ChcOp::BvShl
            | ChcOp::BvLShr
            | ChcOp::BvAShr
            | ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
            | ChcOp::BvComp
            | ChcOp::BvConcat
            | ChcOp::BvExtract(..)
            | ChcOp::BvZeroExtend(_)
            | ChcOp::BvSignExtend(_)
            | ChcOp::BvRotateLeft(_)
            | ChcOp::BvRotateRight(_)
            | ChcOp::BvRepeat(_)
    )
}
