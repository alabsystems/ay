// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::kani_compat::DetHashMap;
use ay_core::original_query::CountedAdmission;

use super::types::{self, Type, Types};
use super::{allocation, exhausted, Census, Error, Query, Result};
use crate::ChcExpr;

#[derive(Default)]
struct Walk<'a> {
    pending: Vec<(&'a ChcExpr, bool)>,
    seen: DetHashMap<usize, Option<usize>>,
    nodes: Vec<(&'a ChcExpr, Type)>,
    node_types: Vec<usize>,
    types: Types,
    census: Census,
}

pub(super) fn read<'a>(original: &'a ChcExpr, owner: &CountedAdmission) -> Result<Query<'a>> {
    let mut walk = Walk::default();
    allocation::vector(&mut walk.pending, 1, owner)?;
    walk.pending.push((original, false));
    while let Some((node, expanded)) = walk.pending.pop() {
        owner.admit(1, 0)?;
        if expanded {
            walk.finish(node, owner)?;
        } else {
            walk.enter(node, owner)?;
        }
    }
    let root = walk.node_type(original)?;
    if walk.types.get(root)? != Type::Bool {
        return Err(Error::IllTyped);
    }
    // Array-only key/value widths need not occur in any scalar expression.
    walk.census.max_bitvector_width = walk.types.max_bitvector_width();
    Ok(Query {
        original,
        census: walk.census,
        nodes: walk.nodes,
        types: walk.types,
        node_ids: walk.seen,
        owner: owner.clone(),
    })
}

impl<'a> Walk<'a> {
    fn enter(&mut self, node: &'a ChcExpr, owner: &CountedAdmission) -> Result<()> {
        let address = std::ptr::from_ref(node) as usize;
        match self.seen.get(&address) {
            Some(Some(_)) => return Ok(()),
            Some(None) => return Err(Error::IllTyped),
            None => {}
        }
        // Classify unsupported syntax before inspecting any of its payload.
        match node {
            ChcExpr::Bool(_)
            | ChcExpr::BitVec(..)
            | ChcExpr::Var(_)
            | ChcExpr::Op(..)
            | ChcExpr::ConstArray(..) => {}
            _ => return Err(Error::Unsupported),
        }
        let children = crate::expr::dag::children(node);
        owner.admit(children.len(), 0)?;
        self.census.nodes = self
            .census
            .nodes
            .checked_add(1)
            .ok_or_else(|| exhausted(owner))?;
        self.census.edges = self
            .census
            .edges
            .checked_add(children.len())
            .ok_or_else(|| exhausted(owner))?;
        allocation::map(&mut self.seen, 1, owner)?;
        self.seen.insert(address, None);
        let extra = children
            .len()
            .checked_add(1)
            .ok_or_else(|| exhausted(owner))?;
        allocation::vector(&mut self.pending, extra, owner)?;
        self.pending.push((node, true));
        self.pending
            .extend(children.iter().rev().map(|child| (child.as_ref(), false)));
        Ok(())
    }

    fn finish(&mut self, node: &'a ChcExpr, owner: &CountedAdmission) -> Result<()> {
        let id = match node {
            ChcExpr::Bool(_) => self.types.intern(Type::Bool, owner)?,
            ChcExpr::BitVec(value, width) => {
                let ty = types::bitvector(*width)?;
                if *width < 128 && *value >> *width != 0 {
                    return Err(Error::IllTyped);
                }
                self.types.intern(ty, owner)?
            }
            ChcExpr::Var(var) => {
                owner.admit(var.name.len(), 0)?;
                self.census.name_bytes = self
                    .census
                    .name_bytes
                    .checked_add(var.name.len())
                    .ok_or_else(|| exhausted(owner))?;
                self.census.variable_occurrences = self
                    .census
                    .variable_occurrences
                    .checked_add(1)
                    .ok_or_else(|| exhausted(owner))?;
                self.types.read(&var.sort, owner)?
            }
            ChcExpr::Op(op, children) => {
                let mut args = Vec::new();
                allocation::vector(&mut args, children.len(), owner)?;
                owner.admit(children.len(), 0)?;
                for child in children {
                    args.push(self.node_type(child)?);
                }
                self.types.operation(*op, &args, owner)?
            }
            ChcExpr::ConstArray(key, value) => {
                let key = self.types.read(key, owner)?;
                let value = self.node_type(value)?;
                self.types.intern(Type::Array(key, value), owner)?
            }
            _ => return Err(Error::Unsupported),
        };
        let ty = self.types.get(id)?;
        self.record_type(ty, owner)?;
        allocation::vector(&mut self.nodes, 1, owner)?;
        allocation::vector(&mut self.node_types, 1, owner)?;
        let index = self.nodes.len();
        self.nodes.push((node, ty));
        self.node_types.push(id);
        self.seen
            .insert(std::ptr::from_ref(node) as usize, Some(index));
        Ok(())
    }

    fn node_type(&self, node: &ChcExpr) -> Result<usize> {
        let index = self
            .seen
            .get(&(std::ptr::from_ref(node) as usize))
            .copied()
            .flatten()
            .ok_or(Error::IllTyped)?;
        self.node_types.get(index).copied().ok_or(Error::IllTyped)
    }

    fn record_type(&mut self, ty: Type, owner: &CountedAdmission) -> Result<()> {
        match ty {
            Type::BitVec(width) => {
                self.census.bitvector_nodes = self
                    .census
                    .bitvector_nodes
                    .checked_add(1)
                    .ok_or_else(|| exhausted(owner))?;
                self.census.bitvector_width_sum = self
                    .census
                    .bitvector_width_sum
                    .checked_add(u64::from(width))
                    .ok_or_else(|| exhausted(owner))?;
                self.census.max_bitvector_width = self.census.max_bitvector_width.max(width);
            }
            Type::Array(..) => self.census.has_arrays = true,
            Type::Bool => {}
        }
        Ok(())
    }
}
