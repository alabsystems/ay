// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A private append-only, typed word DAG. Handles cannot be imported or used
//! across programs through a public API. No recursive tree clone is required.
//! Fixed word matching admits one exact reservation; canonical source programs
//! admit each bounded growth before reserving it. Allocator metadata, source
//! storage, destruction and opaque bit-blast intervals remain separate costs.

use super::{Reference, ReferenceError, Result};
use ay_core::TermId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct RefId(pub(super) usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Operation {
    Input(TermId),
    Small(u64),
    Ones,
    Not(RefId),
    Resize(RefId),
    Extract(RefId, u32, u32),
    Binary(Binary, RefId, RefId),
    Select(RefId, RefId, RefId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Binary {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Eq,
    Ult,
    Shl,
    Lshr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Node {
    pub(super) width: u32,
    pub(super) operation: Operation,
}

#[derive(Clone, Copy)]
pub(super) struct Bits {
    pub(super) sign: RefId,
    pub(super) exponent: RefId,
    pub(super) fraction: RefId,
}

impl Reference<'_, '_> {
    fn append(&mut self, width: u32, operation: Operation) -> Result<RefId> {
        if width == 0 {
            return self.stop(ReferenceError::Width);
        }
        self.charge(1, 0)?;
        if self.nodes.len() >= self.node_limit {
            return self.stop(ReferenceError::Resource);
        }
        if self.nodes.len() == self.nodes.capacity() {
            let growth = 64usize.min(self.node_limit - self.nodes.len());
            let bytes = growth
                .checked_mul(size_of::<Node>())
                .ok_or(ReferenceError::Width)?;
            self.storage(growth, bytes)?;
            if self.nodes.try_reserve_exact(growth).is_err() {
                return self.stop(ReferenceError::Allocation);
            }
        }
        let id = RefId(self.nodes.len());
        self.nodes.push(Node { width, operation });
        Ok(id)
    }

    pub(super) fn width(&mut self, id: RefId) -> Result<u32> {
        self.charge(1, 0)?;
        let Some(node) = self.nodes.get(id.0) else {
            return self.stop(ReferenceError::Source);
        };
        Ok(node.width)
    }

    pub(super) fn input(&mut self, source: TermId, width: u32) -> Result<RefId> {
        // Exact repeated source TermIds share bits; display names do not.
        // Canonical source queries can retain additional genuine typed leaves
        // without accepting caller-provided aliases or decompositions.
        for index in 0..self.nodes.len() {
            self.charge(1, 0)?;
            let node = self.nodes[index];
            if node.operation == Operation::Input(source) {
                if node.width != width {
                    return self.stop(ReferenceError::Source);
                }
                return Ok(RefId(index));
            }
        }
        self.append(width, Operation::Input(source))
    }

    pub(super) fn small(&mut self, value: u64, width: u32) -> Result<RefId> {
        if width == 0 || (width < 64 && value >> width != 0) {
            return self.stop(ReferenceError::Width);
        }
        self.append(width, Operation::Small(value))
    }

    pub(super) fn ones(&mut self, width: u32) -> Result<RefId> {
        self.append(width, Operation::Ones)
    }

    pub(super) fn not(&mut self, value: RefId) -> Result<RefId> {
        let width = self.width(value)?;
        self.append(width, Operation::Not(value))
    }

    pub(super) fn resize(&mut self, value: RefId, width: u32) -> Result<RefId> {
        let old = self.width(value)?;
        if width == old {
            return Ok(value);
        }
        self.append(width, Operation::Resize(value))
    }

    pub(super) fn bit(&mut self, value: RefId, bit: u32) -> Result<RefId> {
        self.extract(value, bit, bit)
    }

    pub(super) fn extract(&mut self, value: RefId, high: u32, low: u32) -> Result<RefId> {
        if low > high || high >= self.width(value)? {
            return self.stop(ReferenceError::Width);
        }
        self.append(high - low + 1, Operation::Extract(value, high, low))
    }

    pub(super) fn binary(&mut self, op: Binary, a: RefId, b: RefId) -> Result<RefId> {
        let width = self.width(a)?;
        if width != self.width(b)? {
            return self.stop(ReferenceError::Width);
        }
        let result_width = match op {
            Binary::Eq | Binary::Ult => 1,
            _ => width,
        };
        self.append(result_width, Operation::Binary(op, a, b))
    }

    pub(super) fn select(&mut self, condition: RefId, yes: RefId, no: RefId) -> Result<RefId> {
        let width = self.width(yes)?;
        if self.width(condition)? != 1 || width != self.width(no)? {
            return self.stop(ReferenceError::Width);
        }
        self.append(width, Operation::Select(condition, yes, no))
    }

    pub(super) fn is_zero(&mut self, value: RefId) -> Result<RefId> {
        let width = self.width(value)?;
        let zero = self.small(0, width)?;
        self.binary(Binary::Eq, value, zero)
    }

    pub(super) fn nonzero(&mut self, value: RefId) -> Result<RefId> {
        let zero = self.is_zero(value)?;
        self.not(zero)
    }

    pub(super) fn slt(&mut self, a: RefId, b: RefId) -> Result<RefId> {
        let width = self.width(a)?;
        if width != self.width(b)? {
            return self.stop(ReferenceError::Width);
        }
        let a_sign = self.bit(a, width - 1)?;
        let b_sign = self.bit(b, width - 1)?;
        let differs = self.binary(Binary::Xor, a_sign, b_sign)?;
        let unsigned = self.binary(Binary::Ult, a, b)?;
        self.select(differs, a_sign, unsigned)
    }

    pub(super) fn power(&mut self, bit: u32, width: u32) -> Result<RefId> {
        if bit >= width {
            return self.stop(ReferenceError::Width);
        }
        let one = self.small(1, width)?;
        let amount = self.small(u64::from(bit), width)?;
        self.binary(Binary::Shl, one, amount)
    }

    /// Clamp at data width BEFORE narrowing: huge mathematical shifts never
    /// wrap modulo a small amount carrier. Signed-negative amounts are used
    /// only on a discarded conditional branch, but are still over-shifts.
    pub(super) fn shift(&mut self, op: Binary, value: RefId, amount: RefId) -> Result<RefId> {
        if !matches!(op, Binary::Shl | Binary::Lshr) {
            return self.stop(ReferenceError::Source);
        }
        let data_width = self.width(value)?;
        let amount_width = self.width(amount)?;
        let count_bits = data_width.bit_width();
        let common = amount_width.max(count_bits);
        let amount = self.resize(amount, common)?;
        let cap = self.small(u64::from(data_width), common)?;
        let below = self.binary(Binary::Ult, amount, cap)?;
        let clamped = self.select(below, amount, cap)?;
        let resized = self.resize(clamped, data_width)?;
        self.binary(op, value, resized)
    }
}
