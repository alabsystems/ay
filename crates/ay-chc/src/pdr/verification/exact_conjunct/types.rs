// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Error, Owner, Result};
use crate::{ChcOp, ChcSort};

pub(super) const MAX_DEPTH: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Sort {
    Bool,
    Int,
    Real,
    BitVec(u32),
    Array(usize, usize),
}

#[derive(Default)]
pub(super) struct Types(Vec<Sort>);

impl Types {
    pub(super) fn get(&self, id: usize) -> Sort {
        self.0[id]
    }

    pub(super) fn intern(&mut self, sort: Sort, owner: &mut Owner) -> Result<usize> {
        owner.admit(self.0.len().checked_add(1).ok_or(Error::Resource)?, 0)?;
        if let Some(id) = self.0.iter().position(|entry| *entry == sort) {
            return Ok(id);
        }
        owner.admit(1, 2 * std::mem::size_of::<Sort>() + 64)?;
        self.0.try_reserve(1).map_err(|_| Error::Resource)?;
        self.0.push(sort);
        Ok(self.0.len() - 1)
    }

    pub(super) fn read(
        &mut self,
        sort: &ChcSort,
        depth: usize,
        owner: &mut Owner,
    ) -> Result<usize> {
        owner.admit(1, 0)?;
        if depth >= MAX_DEPTH {
            return Err(Error::Resource);
        }
        let key = match sort {
            ChcSort::Bool => Sort::Bool,
            ChcSort::Int => Sort::Int,
            ChcSort::Real => Sort::Real,
            ChcSort::BitVec(width) if *width > 0 && *width <= crate::MAX_BITVECTOR_WIDTH => {
                Sort::BitVec(*width)
            }
            ChcSort::BitVec(_) => return Err(Error::InvalidSource),
            ChcSort::Array(key, value) => {
                let key = self.read(key, depth + 1, owner)?;
                let value = self.read(value, depth + 1, owner)?;
                Sort::Array(key, value)
            }
            _ => return Err(Error::Unsupported),
        };
        self.intern(key, owner)
    }

    pub(super) fn operation(
        &mut self,
        op: ChcOp,
        args: &[usize],
        owner: &mut Owner,
    ) -> Result<usize> {
        owner.admit(args.len().checked_add(1).ok_or(Error::Resource)?, 0)?;
        // Array signatures compare canonical sort IDs, not recursive clones.
        let result = match (op, args) {
            (ChcOp::Eq | ChcOp::Ne, [a, b]) if a == b => Some(Sort::Bool),
            (ChcOp::Ite, [c, a, b]) if self.get(*c) == Sort::Bool && a == b => {
                return Ok(*a);
            }
            (ChcOp::Select, [array, index]) => match self.get(*array) {
                Sort::Array(key, value) if key == *index => return Ok(value),
                _ => return Err(Error::InvalidSource),
            },
            (ChcOp::Store, [array, index, value]) => match self.get(*array) {
                Sort::Array(key, val) if key == *index && val == *value => return Ok(*array),
                _ => return Err(Error::InvalidSource),
            },
            _ => None,
        };
        if let Some(result) = result {
            return self.intern(result, owner);
        }
        let bytes = args
            .len()
            .checked_mul(std::mem::size_of::<ChcSort>())
            .ok_or(Error::Resource)?;
        owner.admit(args.len(), bytes)?;
        let mut scalar = Vec::new();
        scalar
            .try_reserve_exact(args.len())
            .map_err(|_| Error::Resource)?;
        for arg in args {
            scalar.push(match self.get(*arg) {
                Sort::Bool => ChcSort::Bool,
                Sort::Int => ChcSort::Int,
                Sort::Real => ChcSort::Real,
                Sort::BitVec(width) => ChcSort::BitVec(width),
                Sort::Array(..) => return Err(Error::InvalidSource),
            });
        }
        let result =
            crate::pdr::validate_qf_operation(op, &scalar).map_err(|_| Error::InvalidSource)?;
        self.read(&result, 0, owner)
    }
}
