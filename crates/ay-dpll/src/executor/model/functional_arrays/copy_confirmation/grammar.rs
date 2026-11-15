// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use ay_model_check::ModelView;
use num_traits::{Signed, ToPrimitive};

use super::{Executor, IndependentModelView, PinAdmission};

pub(super) struct Copy {
    pub(super) arrays: [TermId; 3],
    pub(super) lo: u64,
    pub(super) hi: u64,
    pub(super) source_lo: u64,
}

struct Probe<'a, 'b, 'm> {
    exec: &'a Executor,
    view: &'b IndependentModelView<'m>,
    admission: &'b mut PinAdmission,
    name: &'a str,
}

pub(super) fn recognize(
    exec: &Executor,
    view: &IndependentModelView<'_>,
    root: TermId,
    admission: &mut PinAdmission,
) -> Option<Copy> {
    admission.pay(256, 0).ok()?;
    if (root.0 as usize) >= exec.ctx.terms.len() {
        return None;
    }
    let TermData::Forall(bindings, body, triggers) = exec.ctx.terms.get(root) else {
        return None;
    };
    let [(name, Sort::BitVec(index))] = bindings.as_slice() else {
        return None;
    };
    if index.width != 64
        || !triggers.is_empty()
        || name.len() > 128
        || exec.ctx.terms.sort(root) != &Sort::Bool
    {
        return None;
    }
    Probe {
        exec,
        view,
        admission,
        name,
    }
    .matrix(*body)
}

impl<'a, 'b, 'm> Probe<'a, 'b, 'm> {
    fn node(&mut self, term: TermId) -> Option<&'a TermData> {
        self.admission.pay(128, 0).ok()?;
        if (term.0 as usize) >= self.exec.ctx.terms.len() {
            return None;
        }
        let node = self.exec.ctx.terms.get(term);
        // Reject arbitrary/Indexed UF spellings before the projection lookup
        // can hash them. Every admitted head is a fixed bounded literal.
        if let TermData::App(symbol, _) = node {
            let Symbol::Named(name) = symbol else {
                return None;
            };
            if !matches!(
                name.as_str(),
                "=" | "ite" | "select" | "and" | "bvule" | "bvult" | "bvadd" | "bvsub"
            ) {
                return None;
            }
        }
        if self.view.projection_argument(term).ok()?.is_some() {
            return None;
        }
        Some(node)
    }

    fn app(&mut self, term: TermId, head: &str, arity: usize, sort: &Sort) -> Option<&'a [TermId]> {
        let TermData::App(Symbol::Named(name), args) = self.node(term)? else {
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

    fn binder(&mut self, term: TermId) -> Option<()> {
        let TermData::Var(name, _) = self.node(term)? else {
            return None;
        };
        (name == self.name && self.exec.ctx.terms.sort(term) == &Sort::bitvec(64)).then_some(())
    }

    fn literal(&mut self, term: TermId) -> Option<u64> {
        let TermData::Const(Constant::BitVec { value, width: 64 }) = self.node(term)? else {
            return None;
        };
        if self.exec.ctx.terms.sort(term) != &Sort::bitvec(64)
            || value.is_negative()
            || value.bits() > 64
        {
            return None;
        }
        value.to_u64()
    }

    fn array(&mut self, term: TermId, sort: &Sort) -> Option<()> {
        let TermData::Var(name, _) = self.node(term)? else {
            return None;
        };
        (name != self.name && self.exec.ctx.terms.sort(term) == sort).then_some(())
    }

    fn ite(&mut self, term: TermId, sort: &Sort) -> Option<[TermId; 3]> {
        let parts = match self.node(term)? {
            TermData::Ite(c, p, n) => [*c, *p, *n],
            _ => self.app(term, "ite", 3, sort)?.try_into().ok()?,
        };
        if self.exec.ctx.terms.sort(term) != sort
            || parts
                .iter()
                .any(|child| (child.0 as usize) >= self.exec.ctx.terms.len())
            || self.exec.ctx.terms.sort(parts[0]) != &Sort::Bool
            || self.exec.ctx.terms.sort(parts[1]) != sort
            || self.exec.ctx.terms.sort(parts[2]) != sort
        {
            return None;
        }
        Some(parts)
    }

    fn matrix(&mut self, body: TermId) -> Option<Copy> {
        if let Some(eq) = self.app(body, "=", 2, &Sort::Bool) {
            for side in 0..2 {
                let rhs_sort = self.exec.ctx.terms.sort(eq[1 - side]);
                self.admission.pay(128, 0).ok()?;
                if !(rhs_sort == &Sort::Bool
                    || matches!(rhs_sort, Sort::BitVec(b) if (1..=128).contains(&b.width)))
                {
                    continue;
                }
                if let Some([condition, source, destination]) = self.ite(eq[1 - side], rhs_sort) {
                    if let Some(copy) = self.range(eq[side], condition, source, destination) {
                        return Some(copy);
                    }
                }
            }
            return None;
        }
        let [condition, positive, negative] = self.ite(body, &Sort::Bool)?;
        let positive = self.app(positive, "=", 2, &Sort::Bool)?;
        let negative = self.app(negative, "=", 2, &Sort::Bool)?;
        for p in 0..2 {
            for n in 0..2 {
                self.admission.pay(128, 0).ok()?;
                if positive[p] == negative[n] {
                    if let Some(copy) =
                        self.range(positive[p], condition, positive[1 - p], negative[1 - n])
                    {
                        return Some(copy);
                    }
                }
            }
        }
        None
    }

    fn range(
        &mut self,
        target: TermId,
        condition: TermId,
        source: TermId,
        destination: TermId,
    ) -> Option<Copy> {
        let cell = self.exec.ctx.terms.sort(target);
        if !(cell == &Sort::Bool
            || matches!(cell, Sort::BitVec(bv) if (1..=128).contains(&bv.width)))
        {
            return None;
        }
        let target = self.app(target, "select", 2, cell)?;
        let sort = self.exec.ctx.terms.sort(target[0]);
        let Sort::Array(array) = sort else {
            return None;
        };
        if array.index_sort != Sort::bitvec(64) || &array.element_sort != cell {
            return None;
        }
        self.array(target[0], sort)?;
        self.binder(target[1])?;
        let source = self.app(source, "select", 2, cell)?;
        let destination = self.app(destination, "select", 2, cell)?;
        self.array(source[0], sort)?;
        self.array(destination[0], sort)?;
        if destination[1] != target[1] {
            return None;
        }
        let (lo_term, lower, upper) = self.guards(condition, target[1])?;
        let source_lo = self.offset(source[1], target[1], lo_term)?;
        Some(Copy {
            arrays: [target[0], destination[0], source[0]],
            lo: lower,
            hi: upper,
            source_lo,
        })
    }

    fn guards(&mut self, condition: TermId, bound: TermId) -> Option<(TermId, u64, u64)> {
        let guards = self.app(condition, "and", 2, &Sort::Bool)?;
        let (lo, hi) = if let (Some(lo), Some(hi)) = (
            self.app(guards[0], "bvule", 2, &Sort::Bool),
            self.app(guards[1], "bvult", 2, &Sort::Bool),
        ) {
            (lo, hi)
        } else {
            (
                self.app(guards[1], "bvule", 2, &Sort::Bool)?,
                self.app(guards[0], "bvult", 2, &Sort::Bool)?,
            )
        };
        if lo[1] != bound || hi[0] != bound {
            return None;
        }
        let lower = self.literal(lo[0])?;
        let upper = self.literal(hi[1])?;
        Some((lo[0], lower, upper))
    }

    fn offset(&mut self, index: TermId, bound: TermId, lo: TermId) -> Option<u64> {
        let (shift, source_lo) = if let Some(add) = self.app(index, "bvadd", 2, &Sort::bitvec(64)) {
            if self.app(add[0], "bvsub", 2, &Sort::bitvec(64)).is_some() {
                (add[0], self.literal(add[1])?)
            } else {
                (add[1], self.literal(add[0])?)
            }
        } else {
            (index, 0)
        };
        let subtract = self.app(shift, "bvsub", 2, &Sort::bitvec(64))?;
        if subtract != [bound, lo] {
            return None;
        }
        Some(source_lo)
    }
}
