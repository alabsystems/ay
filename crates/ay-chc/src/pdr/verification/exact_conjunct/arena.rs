// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::types::{Sort, Types, MAX_DEPTH};
use super::{Error, Owner, Result};
use crate::{ChcExpr, ChcOp};
use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};

#[derive(Debug, PartialEq, Eq, Hash)]
pub(super) enum Key<'a> {
    Bool(bool),
    Int(i128),
    Real(i64, i64),
    BitVec(u128, u32),
    Var(&'a str, usize),
    Op(ChcOp, Vec<usize>),
    ConstArray(usize, usize),
}

pub(super) struct Node<'a> {
    pub(super) key: Key<'a>,
    pub(super) sort: usize,
    weight: usize,
}

#[derive(Default)]
pub(super) struct Arena<'a> {
    types: Types,
    nodes: Vec<Node<'a>>,
    buckets: HashMap<u64, Vec<usize>>,
    memo: HashMap<*const ChcExpr, usize>,
    names: HashMap<u64, Vec<(&'a str, usize, usize)>>,
}

impl<'a> Arena<'a> {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn node(&self, id: usize) -> &Node<'a> {
        &self.nodes[id]
    }

    pub(super) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(super) fn boolean(&mut self, value: bool, owner: &mut Owner) -> Result<usize> {
        let sort = self.types.intern(Sort::Bool, owner)?;
        self.intern(Key::Bool(value), sort, owner)
    }

    pub(super) fn bitvector(
        &mut self,
        value: u128,
        width: u32,
        owner: &mut Owner,
    ) -> Result<usize> {
        if width == 0 || width > 128 || (width < 128 && value >> width != 0) {
            return Err(Error::Unsupported);
        }
        let sort = self.types.intern(Sort::BitVec(width), owner)?;
        self.intern(Key::BitVec(value, width), sort, owner)
    }

    pub(super) fn is_bool(&self, id: usize) -> bool {
        self.types.get(self.nodes[id].sort) == Sort::Bool
    }

    pub(super) fn read(
        &mut self,
        expr: &'a ChcExpr,
        depth: usize,
        owner: &mut Owner,
    ) -> Result<usize> {
        owner.admit(1, 0)?;
        if depth >= MAX_DEPTH {
            return Err(Error::Resource);
        }
        let address = expr as *const ChcExpr;
        if let Some(id) = self.memo.get(&address) {
            return Ok(*id);
        }
        if let ChcExpr::Var(var) = expr {
            // The complete sort and name lookup already establishes this
            // variable's canonical key. Reuse its node instead of hashing and
            // comparing the same name again in the general interner.
            let sort = self.types.read(&var.sort, 0, owner)?;
            let id = self.variable(&var.name, sort, owner)?;
            return self.remember(address, id, owner);
        }
        let (key, sort) = match expr {
            ChcExpr::Bool(value) => (Key::Bool(*value), self.types.intern(Sort::Bool, owner)?),
            ChcExpr::Int(value) => (Key::Int(*value), self.types.intern(Sort::Int, owner)?),
            ChcExpr::Real(n, d) if *d != 0 => {
                (Key::Real(*n, *d), self.types.intern(Sort::Real, owner)?)
            }
            ChcExpr::Real(..) => return Err(Error::InvalidSource),
            ChcExpr::BitVec(value, width) => {
                if *width == 0
                    || *width > crate::MAX_BITVECTOR_WIDTH
                    || (*width < 128 && *value >> *width != 0)
                {
                    return Err(Error::InvalidSource);
                }
                (
                    Key::BitVec(*value, *width),
                    self.types.intern(Sort::BitVec(*width), owner)?,
                )
            }
            ChcExpr::Op(op, args) => self.operation(*op, args, depth, owner)?,
            ChcExpr::ConstArray(key, value) => {
                let key = self.types.read(key, 0, owner)?;
                let value = self.read(value, depth + 1, owner)?;
                let sort = self
                    .types
                    .intern(Sort::Array(key, self.nodes[value].sort), owner)?;
                (Key::ConstArray(key, value), sort)
            }
            _ => return Err(Error::Unsupported),
        };
        let id = self.intern(key, sort, owner)?;
        self.remember(address, id, owner)
    }

    fn remember(&mut self, address: *const ChcExpr, id: usize, owner: &mut Owner) -> Result<usize> {
        owner.admit(1, 64)?;
        self.memo.try_reserve(1).map_err(|_| Error::Resource)?;
        self.memo.insert(address, id);
        Ok(id)
    }

    fn operation(
        &mut self,
        op: ChcOp,
        args: &'a [std::sync::Arc<ChcExpr>],
        depth: usize,
        owner: &mut Owner,
    ) -> Result<(Key<'a>, usize)> {
        let bytes = args
            .len()
            .checked_mul(2 * std::mem::size_of::<usize>())
            .ok_or(Error::Resource)?;
        owner.admit(args.len(), bytes)?;
        let mut children = Vec::new();
        let mut sorts = Vec::new();
        children
            .try_reserve_exact(args.len())
            .map_err(|_| Error::Resource)?;
        sorts
            .try_reserve_exact(args.len())
            .map_err(|_| Error::Resource)?;
        for arg in args {
            let id = self.read(arg, depth + 1, owner)?;
            children.push(id);
            sorts.push(self.nodes[id].sort);
        }
        let sort = self.types.operation(op, &sorts, owner)?;
        Ok((Key::Op(op, children), sort))
    }

    fn intern(&mut self, key: Key<'a>, sort: usize, owner: &mut Owner) -> Result<usize> {
        let weight = match &key {
            Key::Var(name, _) => name.len(),
            Key::Op(_, args) => args.len(),
            _ => 1,
        }
        .checked_add(1)
        .ok_or(Error::Resource)?;
        owner.admit(weight, 0)?;
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        if let Some(bucket) = self.buckets.get(&hash) {
            for id in bucket {
                owner.admit(weight.max(self.nodes[*id].weight), 0)?;
                // Hashes select candidates only. Every collision is charged,
                // and full keys (including complete child IDs) must match.
                if self.nodes[*id].sort == sort && self.nodes[*id].key == key {
                    return Ok(*id);
                }
            }
        }
        self.reserve_node(owner)?;
        owner.admit(0, 256)?;
        self.buckets.try_reserve(1).map_err(|_| Error::Resource)?;
        let bucket = self.buckets.entry(hash).or_default();
        bucket.try_reserve(1).map_err(|_| Error::Resource)?;
        let id = self.nodes.len();
        bucket.push(id);
        self.nodes.push(Node { key, sort, weight });
        Ok(id)
    }

    fn reserve_node(&mut self, owner: &mut Owner) -> Result<()> {
        owner.admit(1, 2 * std::mem::size_of::<Node<'a>>())?;
        self.nodes.try_reserve(1).map_err(|_| Error::Resource)
    }

    fn variable(&mut self, name: &'a str, sort: usize, owner: &mut Owner) -> Result<usize> {
        let weight = name.len().checked_add(1).ok_or(Error::Resource)?;
        owner.admit(weight, 0)?;
        let mut hasher = DefaultHasher::new();
        name.hash(&mut hasher);
        let hash = hasher.finish();
        if let Some(bucket) = self.names.get(&hash) {
            for (previous, previous_sort, id) in bucket {
                owner.admit(name.len().max(previous.len()), 0)?;
                if *previous == name {
                    return if *previous_sort == sort {
                        Ok(*id)
                    } else {
                        Err(Error::InvalidSource)
                    };
                }
            }
        }
        // The complete name-and-sort lookup established this key is new.
        // Variables use that table exclusively: hashing the same key again
        // into the general expression buckets establishes no additional fact.
        // The name entry additionally retains a canonical node ID. Charge its
        // possible vector growth before installing the reusable key.
        owner.admit(1, 256 + 2 * std::mem::size_of::<usize>())?;
        self.names.try_reserve(1).map_err(|_| Error::Resource)?;
        self.names
            .entry(hash)
            .or_default()
            .try_reserve(1)
            .map_err(|_| Error::Resource)?;
        self.reserve_node(owner)?;
        let id = self.nodes.len();
        self.nodes.push(Node {
            key: Key::Var(name, sort),
            sort,
            weight,
        });
        self.names.entry(hash).or_default().push((name, sort, id));
        Ok(id)
    }
}

#[cfg(test)]
#[path = "arena_variable_tests.rs"]
mod variable_tests;
