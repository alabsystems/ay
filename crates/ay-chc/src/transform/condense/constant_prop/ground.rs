// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded concrete values for the PRIVATE constant-propagation analysis.
//!
//! McCarthy arrays are total functions. Distinct defaults do not imply
//! inequality on a finite index domain: the union of the exception maps can
//! cover that entire domain. `equivalent` checks this without enumerating it.
//! Structural equality below is only a fixpoint convergence optimization;
//! all logical comparisons go through `equivalent`.

use std::collections::BTreeMap;
use std::sync::Arc;

use ay_core::resource::{
    check_stop_requested, current_check_stop, current_guard, CheckStop, Guard,
};

use crate::{ChcExpr, ChcOp, ChcSort};

pub(super) const MAX_ARRAY_ENTRIES: usize = 128;
pub(super) const MAX_DEPTH: usize = 128;
// Variable-name bytes are charged too: consumer names routinely exceed 100
// bytes. This is one cumulative allowance, not a fresh one per clause/sweep.
const WORK_LIMIT: usize = 16_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Stopped;

/// One allowance shared by candidate discovery, justification and rewriting.
/// Failure abandons the entire transform, never just the unfinished clause.
pub(super) struct Budget {
    remaining: usize,
    rewrite_remaining: usize,
    original_stop: Option<CheckStop>,
    original_guard: Option<Guard>,
    stopped: bool,
}

impl Budget {
    pub(super) fn new() -> Self {
        let original = current_check_stop();
        let stopped = original.is_err();
        Self {
            remaining: WORK_LIMIT,
            rewrite_remaining: 1_000_000,
            original_stop: original.ok().flatten(),
            original_guard: current_guard(),
            stopped,
        }
    }

    pub(super) fn charge(&mut self, amount: usize) -> Result<(), Stopped> {
        if self.stopped {
            return Err(self.stop());
        }
        // Foreign callbacks may unwind. A caller that catches that panic must
        // not resume this allowance as though the poll had admitted work.
        self.stopped = true;
        if self.original_stop.as_ref().is_some_and(|stop| stop())
            || self
                .original_guard
                .as_ref()
                .is_some_and(|guard| guard.poll().is_some())
            || check_stop_requested()
        {
            return Err(self.stop());
        }
        match self.remaining.checked_sub(amount) {
            Some(remaining) => {
                self.remaining = remaining;
                // The local ceiling limits this algorithm; it is not fresh
                // caller credit. Debit the captured node even after another
                // scope replaces it in TLS, before the caller does the work.
                if self.original_guard.as_ref().is_some_and(|guard| {
                    u64::try_from(amount)
                        .ok()
                        .and_then(|cost| guard.tick(cost).ok())
                        .is_none()
                }) {
                    return Err(self.stop());
                }
                self.stopped = false;
                Ok(())
            }
            None => Err(self.stop()),
        }
    }

    pub(super) fn remaining(&self) -> usize {
        self.remaining
    }

    pub(super) fn stop(&mut self) -> Stopped {
        self.stopped = true;
        self.remaining = 0;
        Stopped
    }

    pub(super) fn reserve_output(&mut self, nodes: usize) -> Result<(), Stopped> {
        self.charge(0)?;
        self.rewrite_remaining = self
            .rewrite_remaining
            .checked_sub(nodes)
            .ok_or_else(|| self.stop())?;
        self.charge(nodes)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Value {
    Scalar(ChcExpr),
    Array(Arc<BoolArray>),
}

#[derive(Debug, PartialEq)]
pub(super) struct BoolArray {
    pub(super) width: u32,
    pub(super) default: bool,
    // Canonical indices; newest write wins; default-valued writes absent.
    entries: BTreeMap<u128, bool>,
}

pub(super) fn mask(width: u32) -> Option<u128> {
    match width {
        1..=127 => Some((1u128 << width) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

impl BoolArray {
    pub(super) fn constant(width: u32, default: bool) -> Option<Self> {
        mask(width)?;
        Some(Self {
            width,
            default,
            entries: BTreeMap::new(),
        })
    }

    pub(super) fn select(&self, index: u128) -> bool {
        self.entries.get(&index).copied().unwrap_or(self.default)
    }

    pub(super) fn store(
        self: &Arc<Self>,
        index: u128,
        value: bool,
        budget: &mut Budget,
    ) -> Result<Arc<Self>, Stopped> {
        budget.charge(self.entries.len() + 1)?;
        if self.select(index) == value {
            return Ok(Arc::clone(self));
        }
        let mut entries = self.entries.clone();
        if value == self.default {
            entries.remove(&index);
        } else {
            if entries.len() >= MAX_ARRAY_ENTRIES && !entries.contains_key(&index) {
                return Err(budget.stop());
            }
            entries.insert(index, value);
        }
        Ok(Arc::new(Self {
            width: self.width,
            default: self.default,
            entries,
        }))
    }

    fn equivalent(&self, other: &Self, budget: &mut Budget) -> Result<bool, Stopped> {
        budget.charge(self.entries.len() + other.entries.len() + 1)?;
        if self.width != other.width {
            return Ok(false);
        }
        let mut union_size = self.entries.len();
        for (&index, &value) in &self.entries {
            if value != other.select(index) {
                return Ok(false);
            }
        }
        for (&index, &value) in &other.entries {
            if value != self.select(index) {
                return Ok(false);
            }
            if !self.entries.contains_key(&index) {
                union_size += 1;
            }
        }
        // A domain too large for usize cannot be covered by these bounded
        // maps. In particular, never compute `1 << 128` or enumerate BV32.
        Ok(self.default == other.default
            || 1usize
                .checked_shl(self.width)
                .is_some_and(|size| size == union_size))
    }

    fn to_expr(&self, budget: &mut Budget) -> Result<ChcExpr, Stopped> {
        budget.charge(2 + self.entries.len() * 3)?;
        let mut expr = ChcExpr::ConstArray(
            ChcSort::BitVec(self.width),
            Arc::new(ChcExpr::Bool(self.default)),
        );
        for (&index, &value) in &self.entries {
            expr = ChcExpr::Op(
                ChcOp::Store,
                vec![
                    Arc::new(expr),
                    Arc::new(ChcExpr::BitVec(index, self.width)),
                    Arc::new(ChcExpr::Bool(value)),
                ],
            );
        }
        Ok(expr)
    }
}

impl Value {
    pub(super) fn comparison_cost(&self) -> usize {
        match self {
            Self::Scalar(_) => 1,
            Self::Array(array) => array.entries.len() + 1,
        }
    }

    pub(super) fn matches_sort(&self, sort: &ChcSort) -> bool {
        match (self, sort) {
            (Self::Array(array), ChcSort::Array(key, value)) => {
                **key == ChcSort::BitVec(array.width) && **value == ChcSort::Bool
            }
            (Self::Scalar(ChcExpr::Bool(_)), ChcSort::Bool)
            | (Self::Scalar(ChcExpr::Int(_)), ChcSort::Int)
            | (Self::Scalar(ChcExpr::Real(_, _)), ChcSort::Real) => true,
            (Self::Scalar(ChcExpr::BitVec(_, width)), ChcSort::BitVec(expected)) => {
                width == expected
            }
            _ => false,
        }
    }

    pub(super) fn equivalent(&self, other: &Self, budget: &mut Budget) -> Result<bool, Stopped> {
        budget.charge(1)?;
        match (self, other) {
            (Self::Array(a), Self::Array(b)) => a.equivalent(b, budget),
            (Self::Scalar(ChcExpr::Real(a, b)), Self::Scalar(ChcExpr::Real(c, d))) => {
                Ok(i128::from(*a) * i128::from(*d) == i128::from(*c) * i128::from(*b))
            }
            (Self::Scalar(a), Self::Scalar(b)) => Ok(a == b),
            _ => Ok(false),
        }
    }

    pub(super) fn to_expr(&self, budget: &mut Budget) -> Result<ChcExpr, Stopped> {
        budget.charge(1)?;
        match self {
            Self::Scalar(expr) => Ok(expr.clone()),
            Self::Array(array) => array.to_expr(budget),
        }
    }
}
