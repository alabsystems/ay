// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{super::graph::Binary, Pair, RefId, Reference, ReferenceError, Result};
use ay_core::{Sort, Symbol, TermData, TermId};

impl Reference<'_, '_> {
    pub(super) fn indexed_unary(
        &mut self,
        target: TermId,
        name: &str,
        indices: &[u32],
    ) -> Result<TermId> {
        let (data, _) = self.term(target)?;
        let TermData::App(Symbol::Indexed(actual, got), args) = data else {
            return Err(ReferenceError::Source);
        };
        self.charge(name.len() + indices.len() + 2, 0)?;
        if actual.as_str() != name
            || got.as_slice() != indices
            || args.len() != 1
            || self.terms.is_declared_function(actual)
        {
            return Err(ReferenceError::Source);
        }
        Ok(args[0])
    }

    pub(super) fn boolean(&mut self, id: TermId) -> Result<()> {
        let (_, sort) = self.term(id)?;
        if !matches!(sort, Sort::Bool) {
            return Err(ReferenceError::Source);
        }
        Ok(())
    }

    pub(super) fn bit_condition(&mut self, condition: TermId) -> Result<TermId> {
        self.boolean(condition)?;
        let [bit, one] = self.app(condition, "=")?;
        let (_, sort) = self.term(bit)?;
        if !matches!(sort, Sort::BitVec(actual) if actual.width == 1) {
            return Err(ReferenceError::Source);
        }
        self.constant(one, 1, Some(1))?;
        Ok(bit)
    }

    pub(super) fn match_binary(
        &mut self,
        target: TermId,
        op: Binary,
        a: RefId,
        b: RefId,
        todo: &mut Vec<Pair>,
    ) -> Result<()> {
        let comparison = matches!(op, Binary::Eq | Binary::Ult);
        let target = if comparison {
            let (data, _) = self.term(target)?;
            let TermData::Ite(test, one, zero) = data else {
                return Err(ReferenceError::Source);
            };
            self.boolean(*test)?;
            self.constant(*one, 1, Some(1))?;
            self.constant(*zero, 1, Some(0))?;
            *test
        } else {
            target
        };
        let name = match op {
            Binary::Add => "bvadd",
            Binary::Sub => "bvsub",
            Binary::Mul => "bvmul",
            Binary::And => "bvand",
            Binary::Or => "bvor",
            Binary::Xor => "bvxor",
            Binary::Eq => "=",
            Binary::Ult => "bvult",
            Binary::Shl => "bvshl",
            Binary::Lshr => "bvlshr",
        };
        let [left, right] = self.app(target, name)?;
        self.pair(todo, (a, left))?;
        self.pair(todo, (b, right))
    }
}
