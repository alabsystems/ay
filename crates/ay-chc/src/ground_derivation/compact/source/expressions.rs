// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{operation_type, Error, Expressions, Owner, Result, Source, Type};
use crate::ChcExpr;

impl<'a> Source<'a> {
    pub(super) fn expression(
        &mut self,
        expr: &'a ChcExpr,
        state: &mut Expressions<'a>,
        owner: &mut Owner,
        depth: usize,
    ) -> Result<Type<'a>> {
        owner.admit(1, 128)?;
        if depth > 512 {
            return Err(Error::Unsupported);
        }
        let key = std::ptr::from_ref(expr) as usize;
        if let Some(sort) = state.cache.get(&key) {
            return Ok(*sort);
        }
        let sort = match expr {
            ChcExpr::Bool(_) => Type::Bool,
            ChcExpr::BitVec(value, width) => {
                if *width == 0
                    || *width > crate::MAX_BITVECTOR_WIDTH
                    || (*width < 128 && *value >> *width != 0)
                {
                    return Err(Error::InvalidSource);
                }
                Type::BitVec(*width)
            }
            ChcExpr::Var(var) => {
                owner.admit(var.name.len(), var.name.len().saturating_add(128))?;
                if var.name.contains('\0') {
                    return Err(Error::InvalidSource);
                }
                let sort = self.sort(&var.sort, owner, 0)?;
                if state
                    .vars
                    .get(var.name.as_str())
                    .is_some_and(|old| *old != sort)
                {
                    return Err(Error::InvalidSource);
                }
                if state.vars.try_reserve(1).is_err() {
                    return owner.refuse(Error::Resource);
                }
                state.vars.insert(&var.name, sort);
                sort
            }
            ChcExpr::Op(op, args) => {
                let types = self.children(args, state, owner, depth)?;
                operation_type(*op, &types, owner)?
            }
            ChcExpr::FuncApp(name, declared, args) => {
                owner.admit(name.len().saturating_add(1), 0)?;
                let types = self.children(args, state, owner, depth)?;
                let domain = match types.as_slice() {
                    [Type::Datatype(domain)] => Some(*domain),
                    _ => None,
                };
                let function = self.function(name, domain, owner)?;
                let definition = self
                    .problem
                    .datatype_defs()
                    .get(function.sort)
                    .ok_or(Error::InvalidSource)?;
                let fields = &definition[0].1;
                let actual = if let Some(index) = function.field {
                    if types.as_slice() != [Type::Datatype(function.sort)] {
                        return Err(Error::InvalidSource);
                    }
                    self.sort(&fields[index].1, owner, 0)?
                } else {
                    if types.len() != fields.len() {
                        return Err(Error::InvalidSource);
                    }
                    for (actual, (_, expected)) in types.iter().zip(fields) {
                        if *actual != self.sort(expected, owner, 0)? {
                            return Err(Error::InvalidSource);
                        }
                    }
                    Type::Datatype(function.sort)
                };
                if actual != self.sort(declared, owner, 0)? {
                    return Err(Error::InvalidSource);
                }
                actual
            }
            _ => return Err(Error::Unsupported),
        };
        if state.cache.try_reserve(1).is_err() {
            return owner.refuse(Error::Resource);
        }
        state.cache.insert(key, sort);
        Ok(sort)
    }

    fn children(
        &mut self,
        args: &'a [std::sync::Arc<ChcExpr>],
        state: &mut Expressions<'a>,
        owner: &mut Owner,
        depth: usize,
    ) -> Result<Vec<Type<'a>>> {
        owner.admit(
            args.len(),
            args.len().checked_mul(64).ok_or(Error::Resource)?,
        )?;
        let mut types = Vec::new();
        if types.try_reserve(args.len()).is_err() {
            return owner.refuse(Error::Resource);
        }
        for arg in args {
            types.push(self.expression(arg, state, owner, depth + 1)?);
        }
        Ok(types)
    }
}
