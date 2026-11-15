// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::kani_compat::DetHashMap;
use ay_core::original_query::CountedAdmission;

use super::{allocation, exhausted, Error, Result};
use crate::{ChcOp, ChcSort};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Type {
    Bool,
    BitVec(u32),
    Array(usize, usize),
}

#[derive(Default)]
pub(super) struct Types {
    entries: Vec<Type>,
    canonical: DetHashMap<Type, usize>,
    source: DetHashMap<usize, usize>,
    max_bitvector_width: u32,
}

impl Types {
    pub(super) fn get(&self, id: usize) -> Result<Type> {
        self.entries.get(id).copied().ok_or(Error::IllTyped)
    }

    pub(super) fn max_bitvector_width(&self) -> u32 {
        self.max_bitvector_width
    }

    pub(super) fn intern(&mut self, ty: Type, owner: &CountedAdmission) -> Result<usize> {
        owner.admit(1, 0)?;
        if let Some(id) = self.canonical.get(&ty) {
            return Ok(*id);
        }
        allocation::vector(&mut self.entries, 1, owner)?;
        allocation::map(&mut self.canonical, 1, owner)?;
        if let Type::BitVec(width) = ty {
            self.max_bitvector_width = self.max_bitvector_width.max(width);
        }
        let id = self.entries.len();
        self.entries.push(ty);
        self.canonical.insert(ty, id);
        Ok(id)
    }

    pub(super) fn read(&mut self, sort: &ChcSort, owner: &CountedAdmission) -> Result<usize> {
        let mut stack = Vec::new();
        allocation::vector(&mut stack, 1, owner)?;
        stack.push((sort, false));
        while let Some((sort, expanded)) = stack.pop() {
            owner.admit(1, 0)?;
            let address = std::ptr::from_ref(sort) as usize;
            if self.source.contains_key(&address) {
                continue;
            }
            if let ChcSort::Array(key, value) = sort {
                if !expanded {
                    owner.admit(2, 0)?;
                    allocation::vector(&mut stack, 3, owner)?;
                    stack.push((sort, true));
                    stack.push((value.as_ref(), false));
                    stack.push((key.as_ref(), false));
                    continue;
                }
            }
            let ty = match sort {
                ChcSort::Bool => Type::Bool,
                ChcSort::BitVec(width) => bitvector(*width)?,
                ChcSort::Array(key, value) => {
                    Type::Array(self.source_id(key)?, self.source_id(value)?)
                }
                _ => return Err(Error::Unsupported),
            };
            let id = self.intern(ty, owner)?;
            allocation::map(&mut self.source, 1, owner)?;
            self.source.insert(address, id);
        }
        self.source_id(sort)
    }

    fn source_id(&self, sort: &ChcSort) -> Result<usize> {
        self.source
            .get(&(std::ptr::from_ref(sort) as usize))
            .copied()
            .ok_or(Error::IllTyped)
    }

    pub(super) fn operation(
        &mut self,
        op: ChcOp,
        args: &[usize],
        owner: &CountedAdmission,
    ) -> Result<usize> {
        let work = args.len().checked_add(1).ok_or_else(|| exhausted(owner))?;
        owner.admit(work, 0)?;
        let result = match (op, args) {
            (ChcOp::Eq | ChcOp::Ne, [a, b]) if a == b => Some(Type::Bool),
            (ChcOp::Ite, [c, a, b]) if self.get(*c)? == Type::Bool && a == b => return Ok(*a),
            (ChcOp::Select, [array, index]) => match self.get(*array)? {
                Type::Array(key, value) if key == *index => return Ok(value),
                _ => return Err(Error::IllTyped),
            },
            (ChcOp::Store, [array, index, value]) => match self.get(*array)? {
                Type::Array(key, val) if key == *index && val == *value => return Ok(*array),
                _ => return Err(Error::IllTyped),
            },
            _ => None,
        };
        if let Some(result) = result {
            return self.intern(result, owner);
        }
        self.scalar_operation(op, args, owner)
    }

    fn scalar_operation(
        &mut self,
        op: ChcOp,
        args: &[usize],
        owner: &CountedAdmission,
    ) -> Result<usize> {
        // Reuse the authoritative operator signature checker. Only scalar
        // sorts are materialized, so no nested array clone/hash is possible.
        let mut scalar = Vec::new();
        allocation::vector(&mut scalar, args.len(), owner)?;
        for id in args {
            scalar.push(match self.get(*id)? {
                Type::Bool => ChcSort::Bool,
                Type::BitVec(width) => ChcSort::BitVec(width),
                Type::Array(..) => return Err(Error::IllTyped),
            });
        }
        // The existing validator may allocate a bounded scalar error message.
        let work = args.len().checked_add(1).ok_or_else(|| exhausted(owner))?;
        owner.admit(work, 256)?;
        let result = crate::pdr::validate_qf_operation(op, &scalar).map_err(|_| Error::IllTyped)?;
        let ty = match result {
            ChcSort::Bool => Type::Bool,
            ChcSort::BitVec(width) => bitvector(width)?,
            _ => return Err(Error::Unsupported),
        };
        self.intern(ty, owner)
    }
}

pub(super) fn bitvector(width: u32) -> Result<Type> {
    if (1..=crate::MAX_BITVECTOR_WIDTH).contains(&width) {
        Ok(Type::BitVec(width))
    } else {
        Err(Error::IllTyped)
    }
}
