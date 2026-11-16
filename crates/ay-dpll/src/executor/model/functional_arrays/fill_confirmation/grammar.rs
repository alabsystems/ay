// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use ay_model_check::ModelView;
use num_traits::{Signed, ToPrimitive};

use super::{Executor, IndependentModelView, PinAdmission};

pub(super) struct Fill<'a> {
    pub(super) arrays: [TermId; 2],
    pub(super) lo: u64,
    pub(super) hi: u64,
    pub(super) value: &'a Constant,
    pub(super) literal_term: Option<TermId>,
}

/// The Bool fill condition: `c` itself, or the two guards whose De Morgan
/// negation the elaborator stored in place of `not(c)`.
enum Condition {
    Guard(TermId),
    NegatedPair([TermId; 2]),
}

const TRUE: Constant = Constant::Bool(true);
const FALSE: Constant = Constant::Bool(false);

struct Probe<'a, 'b, 'm> {
    exec: &'a Executor,
    view: &'b IndependentModelView<'m>,
    admission: &'b mut PinAdmission,
    name: &'a str,
}

/// Fixed header gate only; no view, model truth, source copy or owned parser.
pub(super) fn header(exec: &Executor, root: TermId) -> bool {
    if (root.0 as usize) >= exec.ctx.terms.len() {
        return false;
    }
    let TermData::Forall(bindings, _, triggers) = exec.ctx.terms.get(root) else {
        return false;
    };
    matches!(bindings.as_slice(), [(name, Sort::BitVec(index))]
        if index.width == 64 && name.len() <= 128)
        && triggers.is_empty()
        && exec.ctx.terms.sort(root) == &Sort::Bool
}

pub(super) fn recognize<'a>(
    exec: &'a Executor,
    view: &IndependentModelView<'_>,
    root: TermId,
    admission: &mut PinAdmission,
) -> Option<Fill<'a>> {
    admission.pay(256, 0).ok()?;
    if !header(exec, root) {
        return None;
    }
    let TermData::Forall(bindings, body, _) = exec.ctx.terms.get(root) else {
        return None;
    };
    Probe {
        exec,
        view,
        admission,
        name: &bindings[0].0,
    }
    .matrix(*body)
}

impl<'a> Probe<'a, '_, '_> {
    fn node(&mut self, term: TermId) -> Option<&'a TermData> {
        self.admission.pay(128, 0).ok()?;
        if (term.0 as usize) >= self.exec.ctx.terms.len() {
            return None;
        }
        let node = self.exec.ctx.terms.get(term);
        if let TermData::App(symbol, _) = node {
            let Symbol::Named(name) = symbol else {
                return None;
            };
            if !matches!(
                name.as_str(),
                "=" | "ite" | "select" | "and" | "or" | "not" | "bvule" | "bvult"
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
                .any(|t| (t.0 as usize) >= self.exec.ctx.terms.len())
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

    fn literal(&mut self, term: TermId, cell: &Sort) -> Option<&'a Constant> {
        let TermData::Const(value) = self.node(term)? else {
            return None;
        };
        if self.exec.ctx.terms.sort(term) != cell {
            return None;
        }
        match value {
            Constant::Bool(_) if cell == &Sort::Bool => Some(value),
            Constant::BitVec { value: n, width }
                if (1..=128).contains(width)
                    && !n.is_negative()
                    && n.bits() <= u64::from(*width)
                    && cell == &Sort::bitvec(*width) =>
            {
                Some(value)
            }
            _ => None,
        }
    }

    fn endpoint(&mut self, term: TermId) -> Option<u64> {
        let Constant::BitVec { value, width: 64 } = self.literal(term, &Sort::bitvec(64))? else {
            return None;
        };
        value.to_u64()
    }

    fn ite(&mut self, term: TermId, sort: &Sort) -> Option<[TermId; 3]> {
        let parts = match self.node(term)? {
            TermData::Ite(c, p, n) => [*c, *p, *n],
            _ => self.app(term, "ite", 3, sort)?.try_into().ok()?,
        };
        if self.exec.ctx.terms.sort(term) != sort
            || parts
                .iter()
                .any(|t| (t.0 as usize) >= self.exec.ctx.terms.len())
            || self.exec.ctx.terms.sort(parts[0]) != &Sort::Bool
            || self.exec.ctx.terms.sort(parts[1]) != sort
            || self.exec.ctx.terms.sort(parts[2]) != sort
        {
            return None;
        }
        Some(parts)
    }

    fn matrix(&mut self, body: TermId) -> Option<Fill<'a>> {
        if let Some(eq) = self.app(body, "=", 2, &Sort::Bool) {
            for side in 0..2 {
                let rhs = eq[1 - side];
                let cell = self.exec.ctx.terms.sort(rhs);
                self.admission.pay(128, 0).ok()?;
                if !(cell == &Sort::Bool
                    || matches!(cell, Sort::BitVec(b) if (1..=128).contains(&b.width)))
                {
                    continue;
                }
                if let Some([condition, literal, frame]) = self.ite(rhs, cell) {
                    if let Some(fill) = self.range(eq[side], condition, literal, frame) {
                        return Some(fill);
                    }
                }
                if cell == &Sort::Bool {
                    if let Some(fill) = self.boolean(eq[side], rhs) {
                        return Some(fill);
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
                    if let Some(fill) =
                        self.range(positive[p], condition, positive[1 - p], negative[1 - n])
                    {
                        return Some(fill);
                    }
                }
            }
        }
        None
    }

    fn reads(&mut self, target: TermId, frame: TermId) -> Option<[TermId; 2]> {
        let cell = self.exec.ctx.terms.sort(target);
        if !(cell == &Sort::Bool || matches!(cell, Sort::BitVec(b) if (1..=128).contains(&b.width)))
        {
            return None;
        }
        let target = self.app(target, "select", 2, cell)?;
        let frame = self.app(frame, "select", 2, cell)?;
        let sort = self.exec.ctx.terms.sort(target[0]);
        let Sort::Array(array) = sort else {
            return None;
        };
        if array.index_sort != Sort::bitvec(64)
            || &array.element_sort != cell
            || self.exec.ctx.terms.sort(frame[0]) != sort
            || target[1] != frame[1]
        {
            return None;
        }
        self.binder(target[1])?;
        for term in [target[0], frame[0]] {
            let TermData::Var(name, _) = self.node(term)? else {
                return None;
            };
            if name == self.name || self.exec.ctx.terms.sort(term) != sort {
                return None;
            }
        }
        Some([target[0], frame[0]])
    }

    fn guards(&mut self, condition: TermId, bound: TermId) -> Option<(u64, u64)> {
        let parts = self.app(condition, "and", 2, &Sort::Bool)?;
        self.guard_pair([parts[0], parts[1]], bound)
    }

    fn guard_pair(&mut self, parts: [TermId; 2], bound: TermId) -> Option<(u64, u64)> {
        for order in [parts, [parts[1], parts[0]]] {
            if let (Some(lo), Some(hi)) = (
                self.app(order[0], "bvule", 2, &Sort::Bool),
                self.app(order[1], "bvult", 2, &Sort::Bool),
            ) {
                if lo[1] == bound && hi[0] == bound {
                    return Some((self.endpoint(lo[0])?, self.endpoint(hi[1])?));
                }
            }
        }
        None
    }

    fn range(
        &mut self,
        target: TermId,
        condition: TermId,
        literal: TermId,
        frame: TermId,
    ) -> Option<Fill<'a>> {
        let arrays = self.reads(target, frame)?;
        let target_parts = self.app(target, "select", 2, self.exec.ctx.terms.sort(target))?;
        let (lo, hi) = self.guards(condition, target_parts[1])?;
        let value = self.literal(literal, self.exec.ctx.terms.sort(target))?;
        Some(Fill {
            arrays,
            lo,
            hi,
            value,
            literal_term: Some(literal),
        })
    }

    fn boolean(&mut self, target: TermId, rhs: TermId) -> Option<Fill<'a>> {
        // Exactly ite(c,true,d[i]) => or(c,d[i]), or
        // ite(c,false,d[i]) => and(not(c),d[i]), whose not(c) the elaborator
        // stores as or(not(lo),not(hi)); no general Boolean rewrite.
        self.admission.pay(128, 0).ok()?;
        if self.exec.ctx.terms.sort(target) != &Sort::Bool {
            return None;
        }
        let (parts, value) = if let Some(parts) = self.app(rhs, "or", 2, &Sort::Bool) {
            (parts, &TRUE)
        } else {
            (self.app(rhs, "and", 2, &Sort::Bool)?, &FALSE)
        };
        for side in 0..2 {
            let condition = if matches!(value, Constant::Bool(true)) {
                Condition::Guard(parts[side])
            } else if let Some(condition) = self.negated(parts[side]) {
                Condition::Guard(condition)
            } else if let Some(pair) = self.de_morgan_negation(parts[side]) {
                Condition::NegatedPair(pair)
            } else {
                continue;
            };
            if let Some(arrays) = self.reads(target, parts[1 - side]) {
                let target_parts = self.app(target, "select", 2, &Sort::Bool)?;
                let range = match condition {
                    Condition::Guard(condition) => self.guards(condition, target_parts[1]),
                    Condition::NegatedPair(pair) => self.guard_pair(pair, target_parts[1]),
                };
                if let Some((lo, hi)) = range {
                    return Some(Fill {
                        arrays,
                        lo,
                        hi,
                        value,
                        literal_term: None,
                    });
                }
            }
        }
        None
    }

    /// The elaborator's `mk_not(and(lo, hi))` (De Morgan): `or(not(lo),
    /// not(hi))`. Returns `[lo, hi]` for exactly that binary shape.
    fn de_morgan_negation(&mut self, term: TermId) -> Option<[TermId; 2]> {
        let parts = self.app(term, "or", 2, &Sort::Bool)?;
        Some([self.negated(parts[0])?, self.negated(parts[1])?])
    }

    fn negated(&mut self, term: TermId) -> Option<TermId> {
        let node = self.node(term)?;
        if self.exec.ctx.terms.sort(term) != &Sort::Bool {
            return None;
        }
        match node {
            TermData::Not(child)
                if (child.0 as usize) < self.exec.ctx.terms.len()
                    && self.exec.ctx.terms.sort(*child) == &Sort::Bool =>
            {
                Some(*child)
            }
            _ => Some(self.app(term, "not", 1, &Sort::Bool)?[0]),
        }
    }
}
