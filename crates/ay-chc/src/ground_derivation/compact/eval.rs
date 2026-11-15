// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::source::{operation_type, Source, Type};
use super::{Arena, Error, Owner, Result, ValueId, ValueNode};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap;
use std::sync::Arc;

pub(super) struct Evaluation<'a, 'b, 'p> {
    pub source: &'b mut Source<'a>,
    pub arena: &'b mut Arena,
    pub env: &'b DetHashMap<&'a str, ValueId>,
    pub owner: &'b mut Owner<'p>,
    pub cache: DetHashMap<usize, ValueId>,
}

impl<'a> Evaluation<'a, '_, '_> {
    pub fn expression(&mut self, expr: &'a ChcExpr, depth: usize) -> Result<ValueId> {
        self.owner.admit(1, 128)?;
        if depth > 512 {
            return Err(Error::Unsupported);
        }
        let key = std::ptr::from_ref(expr) as usize;
        if let Some(value) = self.cache.get(&key) {
            return Ok(*value);
        }
        let value = match expr {
            ChcExpr::Bool(value) => self.arena.intern(&ValueNode::Bool(*value), self.owner)?,
            ChcExpr::BitVec(value, width) => self.arena.intern(
                &ValueNode::BitVec {
                    value: (*value).into(),
                    width: *width,
                },
                self.owner,
            )?,
            ChcExpr::Var(var) => {
                self.owner.admit(var.name.len(), 0)?;
                *self
                    .env
                    .get(var.name.as_str())
                    .ok_or(Error::InvalidDerivation)?
            }
            ChcExpr::Op(op, args) => {
                let values = self.children(args, depth)?;
                self.operation(*op, &values)?
            }
            ChcExpr::FuncApp(name, _, args) => {
                let domain = match args.as_slice() {
                    [arg] => self.source.datatype_domain(arg, self.owner, 0)?,
                    _ => None,
                };
                let function = self.source.function(name, domain, self.owner)?;
                let values = self.children(args, depth)?;
                if let Some(index) = function.field {
                    let [root] = values.as_slice() else {
                        return Err(Error::InvalidDerivation);
                    };
                    let Some(ValueNode::Datatype { sort, fields, .. }) = self.arena.get(*root)
                    else {
                        return Err(Error::InvalidValue);
                    };
                    if sort != function.sort {
                        return Err(Error::InvalidValue);
                    }
                    *fields.get(index).ok_or(Error::InvalidValue)?
                } else {
                    self.owner.admit(
                        name.len().saturating_add(function.sort.len()),
                        name.len().saturating_add(function.sort.len()),
                    )?;
                    self.arena.intern(
                        &ValueNode::Datatype {
                            sort: function.sort.to_owned(),
                            constructor: name.clone(),
                            fields: values,
                        },
                        self.owner,
                    )?
                }
            }
            _ => return Err(Error::Unsupported),
        };
        if self.cache.try_reserve(1).is_err() {
            return self.owner.refuse(Error::Resource);
        }
        self.cache.insert(key, value);
        Ok(value)
    }

    fn children(&mut self, args: &'a [Arc<ChcExpr>], depth: usize) -> Result<Vec<ValueId>> {
        self.owner.admit(
            args.len(),
            args.len().checked_mul(16).ok_or(Error::Resource)?,
        )?;
        let mut values = Vec::new();
        if values.try_reserve(args.len()).is_err() {
            return self.owner.refuse(Error::Resource);
        }
        for arg in args {
            values.push(self.expression(arg, depth + 1)?);
        }
        Ok(values)
    }

    fn operation(&mut self, op: ChcOp, args: &[ValueId]) -> Result<ValueId> {
        if matches!(op, ChcOp::Eq | ChcOp::Ne) {
            let [left, right] = args else {
                return Err(Error::InvalidSource);
            };
            return self.arena.intern(
                &ValueNode::Bool((*left == *right) == (op == ChcOp::Eq)),
                self.owner,
            );
        }
        if op == ChcOp::Ite {
            let [condition, yes, no] = args else {
                return Err(Error::InvalidSource);
            };
            return match self.arena.get(*condition) {
                Some(ValueNode::Bool(b)) => Ok(if *b { *yes } else { *no }),
                _ => Err(Error::InvalidValue),
            };
        }
        self.scalar(op, args)
    }

    fn scalar(&mut self, op: ChcOp, args: &[ValueId]) -> Result<ValueId> {
        self.owner.admit(
            args.len(),
            args.len().checked_mul(512).ok_or(Error::Resource)?,
        )?;
        let mut types = Vec::new();
        if types.try_reserve(args.len()).is_err() {
            return self.owner.refuse(Error::Resource);
        }
        for id in args {
            types.push(
                self.source
                    .value_type(self.arena.get(*id).ok_or(Error::InvalidValue)?, self.owner)?,
            );
        }
        let result_type = operation_type(op, &types, self.owner)?;
        let width = types
            .iter()
            .chain(std::iter::once(&result_type))
            .map(|sort| match sort {
                Type::BitVec(w) => *w as usize,
                _ => 1,
            })
            .max()
            .unwrap_or(1);
        // Existing scalar evaluation is opaque to progress. A conservative
        // bit-quadratic precharge covers multiplication/division, repeated
        // concatenation and their intermediate storage, before any conversion.
        let cost = width
            .checked_mul(width)
            .and_then(|n| n.checked_mul(args.len().saturating_add(1)))
            .ok_or(Error::Resource)?;
        self.owner
            .admit(cost, cost.checked_add(1024).ok_or(Error::Resource)?)?;
        let mut model = DetHashMap::default();
        let mut expressions = Vec::new();
        if model.try_reserve(args.len()).is_err() || expressions.try_reserve(args.len()).is_err() {
            return self.owner.refuse(Error::Resource);
        }
        for (index, id) in args.iter().enumerate() {
            let name = format!("c{index}");
            let (value, sort) = scalar_value(self.arena.get(*id).ok_or(Error::InvalidValue)?)?;
            expressions.push(Arc::new(ChcExpr::Var(ChcVar::new(name.clone(), sort))));
            model.insert(name, value);
        }
        let expression = ChcExpr::Op(op, expressions);
        let value = crate::expr::evaluate_expr(&expression, &model).ok_or(Error::Unsupported)?;
        self.owner.poll()?;
        let node = match value {
            crate::smt::SmtValue::Bool(b) => ValueNode::Bool(b),
            crate::smt::SmtValue::BitVec(value, width) => ValueNode::BitVec {
                value: value.into(),
                width,
            },
            crate::smt::SmtValue::BigBitVec(value, width) => ValueNode::BitVec {
                value: value.as_ref().clone(),
                width,
            },
            _ => return Err(Error::Unsupported),
        };
        if self.source.value_type(&node, self.owner)? != result_type {
            return Err(Error::InvalidValue);
        }
        self.arena.intern(&node, self.owner)
    }
}

fn scalar_value(node: &ValueNode) -> Result<(crate::smt::SmtValue, ChcSort)> {
    match node {
        ValueNode::Bool(b) => Ok((crate::smt::SmtValue::Bool(*b), ChcSort::Bool)),
        ValueNode::BitVec { value, width } => Ok((
            crate::smt::SmtValue::try_bitvec_from_biguint(value.clone(), *width)
                .map_err(|_| Error::InvalidValue)?,
            ChcSort::BitVec(*width),
        )),
        _ => Err(Error::Unsupported),
    }
}
