// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read ownership for model-certified constant arrays. This is not a new
//! interpretation: values come only from the existing checked package, and
//! store/nested reads use the ordinary array walker.

use super::{
    eval_guard, CertifiedConstInterpRead, EvalValue, Executor, HashSet, Model, Sort, TermData,
    TermId,
};
use crate::executor_types::UnknownOrigin;
use ay_core::term::Constant;
use ay_model_check::{EvalOutcome, ModelValue, ModelView};

mod checked;

const MAX_READ_WORK: usize = 20_000;
const MAX_READ_DEPTH: usize = 128;

struct ClosedValue;
impl ModelView for ClosedValue {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

pub(super) struct CertifiedArrayRead {
    remaining: usize,
    work_poison: u64,
    refused: bool,
    package_cost: usize,
}

impl CertifiedArrayRead {
    fn new() -> Self {
        Self {
            remaining: MAX_READ_WORK,
            work_poison: eval_guard::work_budget_poison(),
            refused: false,
            package_cost: 0,
        }
    }

    fn charge(&mut self, exec: &Executor, amount: usize) -> bool {
        if !self.live(exec) {
            return false;
        }
        if amount > self.remaining {
            exec.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
            self.refused = true;
            return false;
        }
        self.remaining -= amount;
        true
    }

    pub(super) fn live(&mut self, exec: &Executor) -> bool {
        if self.refused {
            return false;
        }
        if eval_guard::work_budget_poison() != self.work_poison {
            exec.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
            self.refused = true;
        } else if exec.w4_budget_exhausted() || exec.poll_evaluation_stop().is_err() {
            self.refused = true;
        }
        !self.refused
    }

    pub(super) fn visit(&mut self, exec: &Executor, term: TermId, depth: usize) -> bool {
        if !self.live(exec) {
            return false;
        }
        if depth > MAX_READ_DEPTH || self.remaining == 0 {
            exec.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
            self.refused = true;
            return false;
        }
        self.remaining -= 1;
        if exec.ctx.terms.entry_stamp(term).is_none() {
            self.refused = true;
            return false;
        }
        true
    }

    pub(super) fn resolve(
        &mut self,
        exec: &Executor,
        model: &Model,
        term: TermId,
    ) -> Result<Option<TermId>, ()> {
        if !self.charge(exec, self.package_cost) {
            return Err(());
        }
        match exec.ctx.terms.get(term) {
            TermData::App(symbol, args) => {
                if !self.charge(exec, symbol.name().len()) {
                    return Err(());
                }
                if model.has_certified_const_interp_symbol(symbol) {
                    if !self.charge(exec, args.len())
                        || !self.same_sort(
                            exec,
                            exec.ctx.terms.sort(term),
                            exec.ctx.terms.sort(term),
                        )
                    {
                        return Err(());
                    }
                    for &arg in args {
                        if !self.visit(exec, arg, 0)
                            || !self.same_sort(
                                exec,
                                exec.ctx.terms.sort(arg),
                                exec.ctx.terms.sort(arg),
                            )
                        {
                            return Err(());
                        }
                    }
                }
            }
            TermData::Var(name, _) => {
                if !self.charge(exec, name.len()) {
                    return Err(());
                }
                if model
                    .certified_const_interp_entries()
                    .iter()
                    .any(|entry| entry.name() == Some(name.as_str()))
                    && !self.same_sort(exec, exec.ctx.terms.sort(term), exec.ctx.terms.sort(term))
                {
                    return Err(());
                }
            }
            _ => {}
        }
        match exec.const_interp_witness_value(model, term) {
            Ok(Some(CertifiedConstInterpRead::Constant(value))) if value != term => Ok(Some(value)),
            Ok(None) => Ok(None),
            // A SYMBOLIC body has no closed value at a bare term: it has one
            // only at an evaluated argument point, and this reader evaluates
            // closed values alone. The head is still owned, so the read is an
            // owned refusal, never an unowned fall-through to raw pins.
            Ok(Some(CertifiedConstInterpRead::Constant(_)))
            | Ok(Some(CertifiedConstInterpRead::LinearInt { .. }))
            | Err(_) => {
                self.refused = true;
                Err(())
            }
        }
    }

    /// Bounded syntax-only census. No model evaluation or legacy lookup is
    /// performed for an unowned read. Only array carriers are followed, not
    /// arbitrary arguments of unrelated functions. Every pending occurrence
    /// is charged before insertion; the same ledger then meters the read.
    fn owns(&mut self, exec: &Executor, model: &Model, array: TermId) -> Result<bool, ()> {
        let mut pending = vec![(array, 0)];
        let mut seen = HashSet::default();
        let mut owned = false;
        let mut malformed = false;
        while let Some((term, depth)) = pending.pop() {
            if !self.visit(exec, term, depth) {
                return Err(());
            }
            if !seen.insert(term) {
                continue;
            }
            if let Some(value) = self.resolve(exec, model, term)? {
                owned = true;
                if !self.visit(exec, value, depth + 1) {
                    return Err(());
                }
                pending.push((value, depth + 1));
                continue;
            }
            let children: &[TermId] = match exec.ctx.terms.get(term) {
                TermData::App(symbol, args) => match symbol.name() {
                    "store" => {
                        malformed |= args.len() != 3;
                        args
                    }
                    "select" => {
                        malformed |= args.len() != 2;
                        args
                    }
                    "const-array" => {
                        malformed |= args.len() != 1;
                        args
                    }
                    _ => continue,
                },
                TermData::Ite(_, then_term, else_term) => {
                    for child in [*then_term, *else_term] {
                        if !self.visit(exec, child, depth + 1) {
                            return Err(());
                        }
                        pending.push((child, depth + 1));
                    }
                    // Keep certified carrier admission restricted: following
                    // an ordinary array ITE does not authenticate its guard
                    // for this certificate-owned read route.
                    malformed = true;
                    continue;
                }
                _ => continue,
            };
            for &child in children {
                if !self.visit(exec, child, depth + 1) {
                    return Err(());
                }
                if matches!(exec.ctx.terms.sort(child), Sort::Array(_)) {
                    pending.push((child, depth + 1));
                }
            }
            malformed |= !self.carrier_is_typed(exec, term);
        }
        if owned && malformed {
            Err(())
        } else {
            Ok(owned)
        }
    }

    fn carrier_is_typed(&mut self, exec: &Executor, term: TermId) -> bool {
        let TermData::App(symbol, args) = exec.ctx.terms.get(term) else {
            return true;
        };
        let sort = exec.ctx.terms.sort(term);
        match (symbol.name(), args.as_slice()) {
            ("store", [base, index, value]) => {
                let Sort::Array(array) = sort else {
                    return false;
                };
                self.same_sort(exec, sort, exec.ctx.terms.sort(*base))
                    && self.same_sort(exec, &array.index_sort, exec.ctx.terms.sort(*index))
                    && self.same_sort(exec, &array.element_sort, exec.ctx.terms.sort(*value))
            }
            ("select", [array, index]) => {
                let Sort::Array(array) = exec.ctx.terms.sort(*array) else {
                    return false;
                };
                self.same_sort(exec, &array.index_sort, exec.ctx.terms.sort(*index))
                    && self.same_sort(exec, &array.element_sort, sort)
            }
            ("const-array", [value]) => {
                let Sort::Array(array) = sort else {
                    return false;
                };
                self.same_sort(exec, &array.element_sort, exec.ctx.terms.sort(*value))
            }
            _ => false,
        }
    }

    pub(super) fn scalar(&mut self, exec: &Executor, model: &Model, term: TermId) -> EvalValue {
        if !self.visit(exec, term, 0) {
            return EvalValue::Unknown;
        }
        let Some(_entered) = eval_guard::enter(term) else {
            self.live(exec);
            return EvalValue::Unknown;
        };
        let value = if matches!(exec.ctx.terms.get(term), TermData::Const(_)) {
            term
        } else {
            match self.resolve(exec, model, term) {
                Ok(Some(value)) => value,
                // Unsupported scalar syntax is not permission to consult a
                // cached result or a raw pin on a certified descendant.
                Ok(None) | Err(()) => return EvalValue::Unknown,
            }
        };
        match self.closed_value(exec, value) {
            Some(value) => exec.completed_scalar_value(&value, exec.ctx.terms.sort(term)),
            None => {
                self.refused = true;
                EvalValue::Unknown
            }
        }
    }
}

impl Executor {
    /// Whole-array output uses the very same checked closed value, never the
    /// legacy array completion/default builder. The empty view cannot supply
    /// raw pins, UF guesses, asserted definitions, or replacement defaults.
    pub(super) fn certified_const_array_output(
        &self,
        model: &Model,
        term: TermId,
    ) -> Option<Result<String, String>> {
        if model.certified_const_interp_entries().is_empty()
            || !matches!(self.ctx.terms.sort(term), Sort::Array(_))
        {
            return None;
        }
        let mut read = CertifiedArrayRead::new();
        if !read.prepare(self, model) {
            return Some(Err("certified array package is unavailable".to_string()));
        }
        let result = (|| {
            if !read.visit(self, term, 0) {
                return None;
            }
            match read.resolve(self, model, term) {
                Ok(None) => {
                    return match read.owns(self, model, term) {
                        Ok(false) => Some(Ok(None)),
                        _ => Some(Err(())),
                    }
                }
                Err(()) => return Some(Err(())),
                Ok(Some(value)) => {
                    if super::dt_model::scoped_term_binding_active() {
                        return Some(Err(()));
                    }
                    let value = read.closed_value(self, value)?;
                    let rendered =
                        self.format_gate_model_value(&value, self.ctx.terms.sort(term))?;
                    if !read.live(self) {
                        return Some(Err(()));
                    }
                    Some(Ok(Some(rendered)))
                }
            }
        })();
        match result {
            Some(Ok(None)) => None,
            Some(Ok(Some(value))) => Some(Ok(value)),
            _ => Some(Err("certified array value is unavailable".to_string())),
        }
    }

    /// `None` leaves an unowned read on its existing path. `Some(Unknown)` is
    /// an owned refusal and must never be replaced by raw pins or recovery.
    pub(super) fn certified_const_array_read(
        &self,
        model: &Model,
        term: TermId,
    ) -> Option<EvalValue> {
        if model.certified_const_interp_entries().is_empty() {
            return None;
        }
        let TermData::App(symbol, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if symbol.name() != "select" {
            return None;
        }
        if args.len() != 2 {
            let &array = args.first()?;
            let mut read = CertifiedArrayRead::new();
            return if read.prepare(self, model)
                && matches!(read.owns(self, model, array), Ok(false))
            {
                None
            } else {
                Some(EvalValue::Unknown)
            };
        }
        self.certified_const_array_select_inner(model, args[0], args[1], Some(term))
    }

    pub(super) fn certified_const_array_select(
        &self,
        model: &Model,
        array: TermId,
        index: TermId,
    ) -> Option<EvalValue> {
        self.certified_const_array_select_inner(model, array, index, None)
    }

    fn certified_const_array_select_inner(
        &self,
        model: &Model,
        array: TermId,
        index: TermId,
        read_term: Option<TermId>,
    ) -> Option<EvalValue> {
        if model.certified_const_interp_entries().is_empty() {
            return None;
        }
        let mut read = CertifiedArrayRead::new();
        if !read.prepare(self, model) {
            return Some(EvalValue::Unknown);
        }
        match read.owns(self, model, array) {
            Ok(false) => return None,
            Err(()) => return Some(EvalValue::Unknown),
            Ok(true) => {}
        }
        if !read.visit(self, index, 0) {
            return Some(EvalValue::Unknown);
        }
        let Sort::Array(array_sort) = self.ctx.terms.sort(array) else {
            return Some(EvalValue::Unknown);
        };
        if !read.same_sort(self, &array_sort.index_sort, self.ctx.terms.sort(index))
            || read_term.is_some_and(|term| {
                !read.same_sort(self, &array_sort.element_sort, self.ctx.terms.sort(term))
            })
            || super::dt_model::scoped_term_binding_active()
        {
            return Some(EvalValue::Unknown);
        }
        // The early owned route precedes the ordinary memo/guard. Keep the
        // same cycle and scoped-work admission for its actual select node.
        let _entered = if let Some(term) = read_term {
            let Some(entered) = eval_guard::enter(term) else {
                read.live(self);
                return Some(EvalValue::Unknown);
            };
            Some(entered)
        } else {
            None
        };
        let mut state = Some(read);
        let value = self.evaluate_select_resolving_defs(
            model,
            array,
            index,
            &mut HashSet::default(),
            &mut state,
            0,
        );
        Some(if state.as_mut().is_some_and(|read| read.live(self)) {
            value
        } else {
            EvalValue::Unknown
        })
    }
}

#[cfg(test)]
mod tests;
