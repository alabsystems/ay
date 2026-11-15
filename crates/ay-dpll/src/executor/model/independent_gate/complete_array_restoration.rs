// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Narrow arming, NOT confirmation, for complete-array universal model checks.
//! The original conjunct is never folded or replaced. Every quantified sibling
//! must still confirm, including the unchanged checked full-matrix UNSAT route.

use std::sync::Arc;

use super::super::Model;
use super::Executor;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};

struct Grammar<'a> {
    exec: &'a Executor,
    model: &'a Model,
    name: &'a str,
    bound: TermId,
    array_sort: &'a Sort,
}

impl Executor {
    /// An exact selected array merely arms the ordinary all-leaf checker. It
    /// does not prove the universal, repair a model, or grant SAT authority.
    pub(in crate::executor::model) fn complete_array_restoration_candidate(
        &self,
        root: TermId,
    ) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        if model.functional_arrays.is_none()
            || model.charge_functional_array_work(self, 128).is_err()
            || model.projection_ufs.has_interpretations()
        {
            return false;
        }
        let source = self.ctx.source_context_stamp();
        let epoch = self.query_authority_epoch.clone();
        let birth = self.ctx.terms.entry_stamp(root);
        let admitted = model.validate_functional_array_source(self).is_ok()
            && self.complete_array_restoration_shape(model, root).is_some();
        // No callbacks, model replacements, arena rollback, or source changes
        // can turn an old arming observation into current model authority.
        let current = source == self.ctx.source_context_stamp()
            && epoch.is_same_epoch(&self.query_authority_epoch)
            && birth.is_some()
            && birth == self.ctx.terms.entry_stamp(root)
            && model.validate_functional_array_source(self).is_ok();
        let final_poll = model.charge_functional_array_work(self, 0).is_ok();
        admitted && current && final_poll
    }

    fn complete_array_restoration_shape(&self, model: &Model, root: TermId) -> Option<()> {
        model.charge_functional_array_work(self, 64).ok()?;
        if (root.0 as usize) >= self.ctx.terms.len() || self.ctx.terms.sort(root) != &Sort::Bool {
            return None;
        }
        let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(root) else {
            return None;
        };
        let [(name, Sort::BitVec(index))] = vars.as_slice() else {
            return None;
        };
        if index.width != 64 || !triggers.is_empty() || name.len() > 128 {
            return None;
        }
        // Fixed grammar: no DAG work stack, owned names, or new allowance.
        let mut probe = Grammar {
            exec: self,
            model,
            name,
            bound: root,
            array_sort: self.ctx.terms.sort(root),
        };
        probe.matrix(*body)
    }
}

impl<'a> Grammar<'a> {
    fn pay(&self) -> Option<()> {
        self.model.charge_functional_array_work(self.exec, 64).ok()
    }

    fn node(&self, term: TermId) -> Option<&'a TermData> {
        self.pay()?;
        ((term.0 as usize) < self.exec.ctx.terms.len()).then(|| self.exec.ctx.terms.get(term))
    }

    fn app(&self, term: TermId, head: &str, arity: usize, sort: &Sort) -> Option<&'a [TermId]> {
        let TermData::App(symbol, args) = self.node(term)? else {
            return None;
        };
        let Symbol::Named(name) = symbol else {
            return None;
        };
        if name != head
            || args.len() != arity
            || self.exec.ctx.terms.sort(term) != sort
            || args
                .iter()
                .any(|child| (child.0 as usize) >= self.exec.ctx.terms.len())
        {
            return None;
        }
        Some(args)
    }

    fn binder(&self, term: TermId) -> Option<()> {
        let TermData::Var(name, _) = self.node(term)? else {
            return None;
        };
        if term != self.bound
            || name != self.name
            || !matches!(self.exec.ctx.terms.sort(term), Sort::BitVec(index) if index.width == 64)
        {
            return None;
        }
        Some(())
    }

    fn literal(&self, term: TermId, sort: &Sort) -> Option<()> {
        let TermData::Const(value) = self.node(term)? else {
            return None;
        };
        if self.exec.ctx.terms.sort(term) != sort {
            return None;
        }
        match (value, sort) {
            (Constant::Bool(_), Sort::Bool) => Some(()),
            (Constant::BitVec { value, width }, Sort::BitVec(expected))
                if *width == expected.width
                    && (1..=128).contains(width)
                    && value.sign() != num_bigint::Sign::Minus
                    && value.bits() <= u64::from(*width) =>
            {
                Some(())
            }
            _ => None,
        }
    }

    fn index_literal(&self, term: TermId) -> Option<()> {
        let sort = self.exec.ctx.terms.sort(self.bound);
        self.literal(term, sort)
    }

    fn array(&self, term: TermId) -> Option<()> {
        let TermData::Var(name, _) = self.node(term)? else {
            return None;
        };
        if name == self.name || self.exec.ctx.terms.sort(term) != self.array_sort {
            return None;
        }
        let birth = self.exec.ctx.terms.entry_stamp(term)?;
        // Complete original DATA is mandatory for every source/target/frame,
        // even an unchosen range arm. No fallback, missing cell, or default.
        let captured = self.model.functional_array_value(self.exec, term).ok()??;
        self.pay()?;
        let current = self.model.functional_array_value(self.exec, term).ok()??;
        let valid = captured.sort() == self.array_sort
            && Arc::ptr_eq(&captured, &current)
            && self.exec.ctx.terms.entry_stamp(term) == Some(birth);
        drop((current, captured));
        self.pay()?;
        valid.then_some(())
    }

    fn ite(&self, term: TermId, sort: &Sort) -> Option<(TermId, TermId, TermId)> {
        let parts = match self.node(term)? {
            TermData::Ite(c, p, n) => (*c, *p, *n),
            _ => {
                let args = self.app(term, "ite", 3, sort)?;
                (args[0], args[1], args[2])
            }
        };
        if [parts.0, parts.1, parts.2]
            .iter()
            .any(|child| (child.0 as usize) >= self.exec.ctx.terms.len())
            || self.exec.ctx.terms.sort(term) != sort
            || self.exec.ctx.terms.sort(parts.0) != &Sort::Bool
            || self.exec.ctx.terms.sort(parts.1) != sort
            || self.exec.ctx.terms.sort(parts.2) != sort
        {
            return None;
        }
        Some(parts)
    }

    fn target(&mut self, read_term: TermId) -> Option<&'a Sort> {
        let sort = self.exec.ctx.terms.sort(read_term);
        let read = self.app(read_term, "select", 2, sort)?;
        let Sort::Array(array) = self.exec.ctx.terms.sort(read[0]) else {
            return None;
        };
        if !matches!(&array.index_sort, Sort::BitVec(index) if index.width == 64)
            || !(array.element_sort == Sort::Bool
                || matches!(&array.element_sort, Sort::BitVec(cell) if (1..=128).contains(&cell.width)))
            || sort != &array.element_sort
        {
            return None;
        }
        self.bound = read[1];
        self.array_sort = self.exec.ctx.terms.sort(read[0]);
        self.binder(read[1])?;
        self.array(read[0])?;
        Some(&array.element_sort)
    }

    fn equality(&self, term: TermId) -> Option<(TermId, TermId)> {
        let equal = self.app(term, "=", 2, &Sort::Bool)?;
        if self
            .app(equal[0], "select", 2, self.exec.ctx.terms.sort(equal[1]))
            .is_some()
        {
            Some((equal[0], equal[1]))
        } else {
            Some((equal[1], equal[0]))
        }
    }

    fn matrix(&mut self, body: TermId) -> Option<()> {
        if let Some((target, rhs)) = self.equality(body) {
            let cell = self.target(target)?;
            if self.literal(rhs, cell).is_some() {
                return Some(());
            }
            let (condition, positive, negative) = self.ite(rhs, cell)?;
            return self.range(condition, positive, negative, cell);
        }
        // The ordinary frontend distributes non-Bool equality over an ITE.
        // Recognize only the exact shared target/read, never generic guards or
        // conditionals containing an unrelated universal. The matrix is kept.
        let (condition, positive, negative) = self.ite(body, &Sort::Bool)?;
        let positive = self.app(positive, "=", 2, &Sort::Bool)?;
        let negative = self.app(negative, "=", 2, &Sort::Bool)?;
        // Equality canonicalization may independently reverse either branch.
        // Four prepaid identity comparisons suffice; there is no graph search.
        for p in 0..2 {
            for n in 0..2 {
                self.pay()?;
                if positive[p] != negative[n] {
                    continue;
                }
                if let Some(cell) = self.target(positive[p]) {
                    return self.range(condition, positive[1 - p], negative[1 - n], cell);
                }
            }
        }
        None
    }

    fn range(
        &self,
        condition: TermId,
        positive: TermId,
        negative: TermId,
        cell: &Sort,
    ) -> Option<()> {
        let guards = self.app(condition, "and", 2, &Sort::Bool)?;
        let (lo, hi) = if let (Some(low), Some(high)) = (
            self.app(guards[0], "bvule", 2, &Sort::Bool),
            self.app(guards[1], "bvult", 2, &Sort::Bool),
        ) {
            (low, high)
        } else {
            (
                self.app(guards[1], "bvule", 2, &Sort::Bool)?,
                self.app(guards[0], "bvult", 2, &Sort::Bool)?,
            )
        };
        self.index_literal(lo[0])?;
        self.binder(lo[1])?;
        self.binder(hi[0])?;
        self.index_literal(hi[1])?;
        let source = self.app(positive, "select", 2, cell)?;
        let destination = self.app(negative, "select", 2, cell)?;
        self.array(source[0])?;
        self.array(destination[0])?;
        self.binder(destination[1])?;
        let index_sort = self.exec.ctx.terms.sort(self.bound);
        let shift = if let Some(add) = self.app(source[1], "bvadd", 2, index_sort) {
            if self.app(add[0], "bvsub", 2, index_sort).is_some() {
                self.index_literal(add[1])?;
                add[0]
            } else {
                self.index_literal(add[0])?;
                add[1]
            }
        } else {
            source[1]
        };
        let subtraction = self.app(shift, "bvsub", 2, index_sort)?;
        self.binder(subtraction[0])?;
        if subtraction[1] != lo[0] {
            return None;
        }
        self.index_literal(subtraction[1])?;
        Some(())
    }
}

#[cfg(test)]
mod tests;
