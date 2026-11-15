// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Count the same typed expression topology once, matching the gate cache.
//! Every source occurrence still undergoes full validation and
//! occurrence/name/depth accounting. Keys contain complete operands; hash
//! collisions cannot merge different expressions. The actual emitted-gate cap
//! remains independent.
//!
//! The table also records which interned node every source OCCURRENCE is, by
//! its address in the borrowed expression tree. The encoder blasts each
//! interned node once and reuses its output bits at every other occurrence
//! (`ExprBlaster::blast`), which is what makes the distinct-node count, not
//! the occurrence count, the measure of encoding work.

use super::{BvExpr, BvExprExportError};
use std::{collections::HashMap, mem::size_of};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Operation {
    Leaf,
    Constant,
    Add,
    Sub,
    ZeroExt,
    Extract,
    Or,
    And,
    Xor,
    SignExt,
    Shl,
    Lshr,
    Ashr,
    Not,
    Eq,
    Ult,
    CarryOut,
    Mul,
    UDiv,
    URem,
}

#[derive(PartialEq, Eq, Hash)]
struct Key {
    operation: Operation,
    width: u32,
    parameter: u128,
    children: [u32; 2],
    name: String,
}

#[derive(Default)]
pub(super) struct Sharing {
    keys: HashMap<Key, u32>,
    /// Occurrence address -> interned node. Valid only while the preflighted
    /// trees stay borrowed, which the single export call guarantees.
    occurrences: HashMap<usize, u32>,
    bytes: usize,
}

impl Sharing {
    pub(super) fn bytes(&self) -> usize {
        self.bytes
    }

    /// The bytes held after `additional` more, when within `limit`. Every
    /// table here (keys, the transient key name, occurrences) is charged
    /// through this one check against one ceiling.
    fn admit(&self, additional: usize, limit: usize) -> Result<usize, BvExprExportError> {
        self.bytes
            .checked_add(additional)
            .filter(|&bytes| bytes <= limit)
            .ok_or_else(|| refused(limit))
    }

    /// Hand the occurrence table to the encoder of the SAME borrowed trees.
    pub(super) fn take_occurrences(&mut self) -> HashMap<usize, u32> {
        std::mem::take(&mut self.occurrences)
    }

    pub(super) fn intern(
        &mut self,
        expr: &BvExpr,
        width: u32,
        children: [u32; 2],
        limit: usize,
    ) -> Result<(u32, bool), BvExprExportError> {
        let (operation, parameter, name) = match expr {
            BvExpr::Leaf { name, .. } => (Operation::Leaf, 0, name.as_str()),
            BvExpr::Const { value, .. } => (Operation::Constant, *value, ""),
            BvExpr::Add(..) => (Operation::Add, 0, ""),
            BvExpr::Sub(..) => (Operation::Sub, 0, ""),
            BvExpr::ZeroExt(_, amount) => (Operation::ZeroExt, u128::from(*amount), ""),
            BvExpr::SignExt(_, amount) => (Operation::SignExt, u128::from(*amount), ""),
            BvExpr::Extract { high, low, .. } => (
                Operation::Extract,
                (u128::from(*high) << 32) | u128::from(*low),
                "",
            ),
            BvExpr::Or(..) => (Operation::Or, 0, ""),
            BvExpr::And(..) => (Operation::And, 0, ""),
            BvExpr::Xor(..) => (Operation::Xor, 0, ""),
            BvExpr::Shl(..) => (Operation::Shl, 0, ""),
            BvExpr::Lshr(..) => (Operation::Lshr, 0, ""),
            BvExpr::Ashr(..) => (Operation::Ashr, 0, ""),
            BvExpr::Not(..) => (Operation::Not, 0, ""),
            BvExpr::Eq(..) => (Operation::Eq, 0, ""),
            BvExpr::Ult(..) => (Operation::Ult, 0, ""),
            BvExpr::CarryOut { is_sub, .. } => (Operation::CarryOut, u128::from(*is_sub), ""),
            BvExpr::Mul(..) => (Operation::Mul, 0, ""),
            BvExpr::UDiv(..) => (Operation::UDiv, 0, ""),
            BvExpr::URem(..) => (Operation::URem, 0, ""),
        };
        // The transient candidate name is bounded before allocation too.
        self.admit(name.len(), limit)?;
        let mut owned = String::new();
        owned
            .try_reserve_exact(name.len())
            .map_err(|_| refused(limit))?;
        owned.push_str(name);
        let key = Key {
            operation,
            width,
            parameter,
            children,
            name: owned,
        };
        let (id, fresh) = if let Some(&id) = self.keys.get(&key) {
            (id, false)
        } else {
            let additional = (2 * size_of::<(Key, u32)>())
                .checked_add(key.name.len())
                .ok_or_else(|| refused(limit))?;
            let bytes = self.admit(additional, limit)?;
            self.keys.try_reserve(1).map_err(|_| refused(limit))?;
            let id = u32::try_from(self.keys.len()).map_err(|_| refused(limit))?;
            self.keys.insert(key, id);
            self.bytes = bytes;
            (id, true)
        };
        self.record_occurrence(expr, id, limit)?;
        Ok((id, fresh))
    }

    fn record_occurrence(
        &mut self,
        expr: &BvExpr,
        id: u32,
        limit: usize,
    ) -> Result<(), BvExprExportError> {
        let bytes = self.admit(2 * size_of::<(usize, u32)>(), limit)?;
        self.occurrences
            .try_reserve(1)
            .map_err(|_| refused(limit))?;
        self.occurrences
            .insert(std::ptr::from_ref(expr) as usize, id);
        self.bytes = bytes;
        Ok(())
    }
}

fn refused(limit: usize) -> BvExprExportError {
    BvExprExportError::ResourceLimit {
        resource: "expression sharing bytes",
        limit,
        actual: limit.saturating_add(1),
    }
}

#[cfg(test)]
mod tests;
