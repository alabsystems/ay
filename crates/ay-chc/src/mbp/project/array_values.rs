// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed array model instances for MBP (adapted from 328db18f2).
//! A concrete instance implies the existential it replaces. It is still an
//! untrusted candidate: original-clause validation must accept the projection.

use ay_core::resource::{current_check_stop, current_guard, CheckStop, Guard};
use num_bigint::{BigInt, Sign};
use num_traits::ToPrimitive;
use std::sync::Arc;

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};

// Structural admission bounds, not renewed caller allowances. In particular,
// a store chain is recursive when dropped; do not construct an unbounded one.
const MAX_DEPTH: usize = 128;
const MAX_STORES: usize = 128;
// One optional candidate's cumulative logical node/edge/scratch allowance,
// including fallback. This is not a solver width limit: refused candidates
// retain the symbolic variable. The full supported BV width still fits.
const MAX_BUILD_UNITS: usize = 1_000_000;

#[derive(Clone, Copy)]
enum NumberKind {
    Integer,
    BitVector,
}

pub(super) fn model_value(var: &ChcVar, value: Option<&SmtValue>) -> Option<ChcExpr> {
    let mut owner = Owner::capture();
    let result = owner.literal(&var.sort, value?, 0)?;
    owner.admit(0)?;
    Some(result)
}

pub(super) fn model_value_or_default(var: &ChcVar, value: Option<&SmtValue>) -> Option<ChcExpr> {
    let mut owner = Owner::capture();
    let result = value
        .and_then(|value| owner.literal(&var.sort, value, 0))
        .or_else(|| owner.default(&var.sort, 0))?;
    owner.admit(0)?;
    Some(result)
}

/// Capture once across conversion AND fallback: a one-shot stop cannot be
/// renewed by trying the default. No child guard, deadline or work grant is made.
struct Owner {
    guard: Option<Guard>,
    callback: Option<CheckStop>,
    stopped: bool,
    remaining: usize,
}

impl Owner {
    fn capture() -> Self {
        let callback = current_check_stop();
        Self {
            guard: current_guard(),
            stopped: callback.is_err(),
            callback: callback.ok().flatten(),
            remaining: MAX_BUILD_UNITS,
        }
    }

    fn admit(&mut self, depth: usize) -> Option<()> {
        self.admit_work(depth, 1)
    }

    fn refuse<T>(&mut self) -> Option<T> {
        self.stopped = true;
        None
    }

    fn admit_work(&mut self, depth: usize, cost: usize) -> Option<()> {
        if self.stopped || depth > MAX_DEPTH {
            return self.refuse();
        }
        // Pre-arm before arbitrary caller code so a caught unwind cannot
        // resume the same owner, including through the default fallback.
        self.stopped = true;
        if self.callback.as_ref().is_some_and(|stop| stop())
            || self
                .guard
                .as_ref()
                .is_some_and(|guard| guard.poll().is_some())
            || ay_core::resource::process_cancelled()
            || crate::smt::smt_deadline_expired()
        {
            return None;
        }
        self.remaining = self.remaining.checked_sub(cost)?;
        if let Some(guard) = &self.guard {
            guard.tick(u64::try_from(cost).ok()?).ok()?;
        }
        self.stopped = false;
        Some(())
    }

    /// Validate/cost the full key sort before cloning it into a const array.
    /// Datatype/uninterpreted literals are deliberately outside this fragment.
    fn key(&mut self, sort: &ChcSort, depth: usize) -> Option<()> {
        self.admit(depth)?;
        match sort {
            ChcSort::Bool | ChcSort::Int | ChcSort::Real => Some(()),
            ChcSort::BitVec(width) if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width) => Some(()),
            ChcSort::Array(key, value) => {
                self.key(key, depth + 1)?;
                self.key(value, depth + 1)
            }
            _ => None,
        }
    }

    fn literal(&mut self, sort: &ChcSort, value: &SmtValue, depth: usize) -> Option<ChcExpr> {
        self.admit(depth)?;
        match (sort, value) {
            (ChcSort::Bool, SmtValue::Bool(value)) => Some(ChcExpr::Bool(*value)),
            (ChcSort::Int, SmtValue::Int(value)) => Some(ChcExpr::Int(*value)),
            (ChcSort::Int, SmtValue::BigInt(value)) => self.integer(value, depth),
            (ChcSort::Real, SmtValue::Real(value)) => Some(ChcExpr::Real(
                value.numer().to_i64()?,
                value.denom().to_i64()?,
            )),
            (
                ChcSort::BitVec(width),
                value @ (SmtValue::BitVec(_, actual) | SmtValue::BigBitVec(_, actual)),
            ) if *width > 0 && width == actual => match value {
                SmtValue::BitVec(value, _) => self.bitvector(
                    *width,
                    [*value as u64, (*value >> 64) as u64].into_iter(),
                    depth,
                ),
                SmtValue::BigBitVec(value, _) => {
                    self.bitvector(*width, value.iter_u64_digits(), depth)
                }
                _ => None,
            },
            (ChcSort::Array(key, element), SmtValue::ConstArray(default)) => {
                self.key(key, depth + 1)?;
                let default = self.literal(element, default, depth + 1)?;
                Some(ChcExpr::const_array(key.as_ref().clone(), default))
            }
            (ChcSort::Array(key, element), SmtValue::ArrayMap { default, entries }) => {
                if entries.len() > MAX_STORES {
                    return None;
                }
                // Count the emitted store spine too, not just model nesting;
                // nested maps must not multiply the recursive output depth.
                let child_depth = depth.checked_add(entries.len() + 1)?;
                self.admit(child_depth)?;
                self.key(key, depth + 1)?;
                let default = self.literal(element, default, child_depth)?;
                let mut array = ChcExpr::const_array(key.as_ref().clone(), default);
                for (index, value) in entries {
                    let index = self.literal(key, index, child_depth)?;
                    let value = self.literal(element, value, child_depth)?;
                    self.admit(depth)?;
                    array = ChcExpr::store(array, index, value);
                }
                Some(array)
            }
            _ => None,
        }
    }

    fn default(&mut self, sort: &ChcSort, depth: usize) -> Option<ChcExpr> {
        self.admit(depth)?;
        match sort {
            ChcSort::Bool => Some(ChcExpr::Bool(false)),
            ChcSort::Int => Some(ChcExpr::Int(0)),
            ChcSort::Real => Some(ChcExpr::Real(0, 1)),
            ChcSort::BitVec(width) if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width) => {
                Some(ChcExpr::BitVec(0, *width))
            }
            ChcSort::Array(key, element) => {
                self.key(key, depth + 1)?;
                let default = self.default(element, depth + 1)?;
                Some(ChcExpr::const_array(key.as_ref().clone(), default))
            }
            _ => None,
        }
    }

    /// Reserve numeric construction before allocating its first buffer. The
    /// bound includes leaves, operator nodes/edges, both geometric scratch
    /// buffers and shared integer power nodes. No byte/allocator claim is made.
    fn number_shape(
        &mut self,
        depth: usize,
        leaves: usize,
        kind: NumberKind,
        negative: bool,
    ) -> Option<()> {
        let levels = usize::BITS as usize - leaves.saturating_sub(1).leading_zeros() as usize;
        let (edges, units) = match kind {
            NumberKind::Integer => (2usize, 12usize),
            NumberKind::BitVector => (1, 8),
        };
        let shape = levels
            .checked_mul(edges)
            .and_then(|height| height.checked_add(usize::from(negative)))
            .and_then(|height| depth.checked_add(height))
            .zip(
                leaves
                    .checked_mul(units)
                    .and_then(|n| n.checked_add(levels * 3 + 2)),
            );
        let Some((height, work)) = shape else {
            return self.refuse();
        };
        self.admit_work(height, work)
    }

    fn scratch(&mut self, count: usize, depth: usize) -> Option<Vec<Arc<ChcExpr>>> {
        self.admit_work(depth, 0)?;
        let mut result = Vec::new();
        if result.try_reserve_exact(count).is_err() {
            return self.refuse();
        }
        Some(result)
    }

    fn integer(&mut self, value: &BigInt, depth: usize) -> Option<ChcExpr> {
        if let Some(value) = value.to_i128() {
            return Some(ChcExpr::Int(value));
        }
        let Ok(leaves) = usize::try_from(value.bits().div_ceil(64)) else {
            return self.refuse();
        };
        let negative = value.sign() == Sign::Minus;
        self.number_shape(depth, leaves, NumberKind::Integer, negative)?;
        let mut parts = self.scratch(leaves, depth)?;
        // Borrow limbs directly: no full BigInt clone or decimal conversion.
        for digit in value.iter_u64_digits() {
            self.admit_work(depth, 0)?;
            parts.push(Arc::new(ChcExpr::Int(i128::from(digit))));
        }
        let result = self.join_numbers(parts, NumberKind::Integer, depth)?;
        self.admit_work(depth, 0)?;
        Some(if negative {
            ChcExpr::Op(ChcOp::Neg, vec![Arc::new(result)])
        } else {
            result
        })
    }

    fn bitvector(
        &mut self,
        width: u32,
        mut digits: impl Iterator<Item = u64>,
        depth: usize,
    ) -> Option<ChcExpr> {
        if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
            return None;
        }
        let chunk = |digits: &mut dyn Iterator<Item = u64>, bits: u32| {
            let value = u128::from(digits.next().unwrap_or(0))
                | (u128::from(digits.next().unwrap_or(0)) << 64);
            if bits == 128 {
                value
            } else {
                value & ((1u128 << bits) - 1)
            }
        };
        if width <= 128 {
            // Only the needed low limbs are read even if a directly-built
            // BigBitVec carries a gigantic noncanonical high payload.
            return Some(ChcExpr::BitVec(chunk(&mut digits, width), width));
        }
        let leaves = (width as usize).div_ceil(128);
        self.number_shape(depth, leaves, NumberKind::BitVector, false)?;
        let mut parts = self.scratch(leaves, depth)?;
        let mut remaining = width;
        while remaining != 0 {
            self.admit_work(depth, 0)?;
            let bits = remaining.min(128);
            parts.push(Arc::new(ChcExpr::BitVec(chunk(&mut digits, bits), bits)));
            remaining -= bits;
        }
        self.join_numbers(parts, NumberKind::BitVector, depth)
    }

    /// Adjacent low/high blocks are joined in rounds, so output depth is
    /// logarithmic. At integer round k every paired low block has 2^k limbs;
    /// its shared scale is (2^64)^(2^k). An odd high block waits for next round.
    fn join_numbers(
        &mut self,
        mut parts: Vec<Arc<ChcExpr>>,
        kind: NumberKind,
        depth: usize,
    ) -> Option<ChcExpr> {
        let mut scale = match kind {
            NumberKind::Integer => Some(Arc::new(ChcExpr::Int(1i128 << 64))),
            NumberKind::BitVector => None,
        };
        while parts.len() > 1 {
            let mut next = self.scratch(parts.len().div_ceil(2), depth)?;
            let mut iter = parts.into_iter();
            while let Some(low) = iter.next() {
                self.admit_work(depth, 0)?;
                let Some(high) = iter.next() else {
                    next.push(low);
                    break;
                };
                let value = match &scale {
                    Some(scale) => ChcExpr::Op(
                        ChcOp::Add,
                        vec![
                            Arc::new(ChcExpr::Op(ChcOp::Mul, vec![high, Arc::clone(scale)])),
                            low,
                        ],
                    ),
                    None => ChcExpr::Op(ChcOp::BvConcat, vec![high, low]),
                };
                next.push(Arc::new(value));
            }
            parts = next;
            if parts.len() > 1 {
                if let Some(previous) = scale.take() {
                    self.admit_work(depth, 0)?;
                    scale = Some(Arc::new(ChcExpr::Op(
                        ChcOp::Mul,
                        vec![Arc::clone(&previous), previous],
                    )));
                }
            }
        }
        self.admit_work(depth, 0)?;
        parts.pop().map(|result| result.as_ref().clone())
    }
}

#[cfg(test)]
mod tests;
