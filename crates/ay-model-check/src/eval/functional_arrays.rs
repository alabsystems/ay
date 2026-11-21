// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent whole-function comparison and reads of immutable model data.
//! A chosen model array and a lambda operand are derived independently here.

use std::sync::Arc;

use super::*;
use crate::{recognize_identity_lambda, recognize_range_lambda, ArraySnapshot};

mod fill;
mod periodic;

impl Evaluator<'_> {
    pub(super) fn charge_functional_work(&self, amount: usize) -> EvalResult<()> {
        if self.model.functional_array_interrupted() {
            return Err("functional array original owner interrupted".into());
        }
        let Some(left) = self.functional_work_left.get().checked_sub(amount) else {
            self.functional_work_left.set(0);
            return Err(EvalError::resource(
                EvalResource::Work,
                "functional array work exhausted",
            ));
        };
        self.functional_work_left.set(left);
        self.model.charge_functional_array_work(amount)?;
        self.charge_quantifier_work(amount)?;
        // The original owner may accept this charge while its interrupt
        // becomes sticky. Admission must not authorize subsequent allocation
        // or publication after that transition.
        if self.model.functional_array_interrupted() {
            return Err("functional array original owner interrupted".into());
        }
        Ok(())
    }

    pub(super) fn checked_array_snapshot(
        &self,
        term: TermId,
    ) -> EvalResult<Option<Arc<ArraySnapshot>>> {
        if !self.model.has_functional_arrays() && self.functional_capture_depth.get() == 0 {
            // Old default-absent views keep their original resource behaviour.
            // An inconsistent opt-in refuses instead of silently ignoring data.
            return match self.model.array_snapshot(term)? {
                None => Ok(None),
                Some(_) => Err("functional array hook lacks explicit activation".into()),
            };
        }
        self.charge_functional_work(1)?;
        if (term.0 as usize) >= self.terms.len() {
            return Err("invalid functional array term".into());
        }
        let value = self.model.array_snapshot(term)?;
        if let Some(value) = &value {
            if value.sort() != self.terms.sort(term)
                || !matches!(self.terms.get(term), TermData::Var(..))
                || self.term_depends_on_local_binding(term)?
            {
                return Err("functional array source/sort/binding mismatch".into());
            }
        }
        Ok(value)
    }

    pub(super) fn snapshot_work<T>(
        &self,
        operation: impl FnOnce(&mut usize) -> Result<T, crate::FunctionalArrayError>,
    ) -> EvalResult<T> {
        self.charge_functional_work(1)?;
        let before = self.functional_work_left.get();
        let mut left = before;
        let result = operation(&mut left);
        self.functional_work_left.set(left);
        self.model.charge_functional_array_work(before - left)?;
        self.charge_quantifier_work(before - left)?;
        if self.model.functional_array_interrupted() {
            return Err("functional array owner interrupted".into());
        }
        result.map_err(|error| error.to_string().into())
    }

    /// Model construction uses the SAME immutable data representation, but
    /// confirmation re-derives every lambda operand from its actual syntax.
    /// The returned data is not a confirmation or publication permit.
    pub fn capture_array_snapshot(&self, term: TermId) -> Result<Arc<ArraySnapshot>, String> {
        let mut work = self.functional_work_left.get();
        self.capture_array_snapshot_with_work(term, &mut work)
    }

    /// The caller's remaining work is debited on success AND refusal; nested
    /// candidates cannot replenish the original construction budget.
    pub fn capture_array_snapshot_with_work(
        &self,
        term: TermId,
        work: &mut usize,
    ) -> Result<Arc<ArraySnapshot>, String> {
        self.functional_work_left
            .set(self.functional_work_left.get().min(*work));
        self.functional_capture_depth
            .set(self.functional_capture_depth.get() + 1);
        let guard = CaptureGuard(&self.functional_capture_depth);
        let result = self
            .functional_snapshot(term, 0)
            .map_err(|error| error.to_string());
        *work = self.functional_work_left.get();
        drop(guard);
        result
    }

    /// Scalar captures share the SAME remaining construction work and the
    /// original stop callback; no fresh scalar evaluator replenishes it.
    pub fn evaluate_with_functional_work(&self, term: TermId, work: &mut usize) -> EvalOutcome {
        self.functional_work_left
            .set(self.functional_work_left.get().min(*work));
        self.functional_capture_depth
            .set(self.functional_capture_depth.get() + 1);
        let guard = CaptureGuard(&self.functional_capture_depth);
        let result = self.evaluate(term);
        *work = self.functional_work_left.get();
        drop(guard);
        result
    }

    fn functional_snapshot(&self, term: TermId, depth: usize) -> EvalResult<Arc<ArraySnapshot>> {
        self.charge_functional_work(1)?;
        if depth > 64 {
            return Err("functional array depth exhausted".into());
        }
        if (term.0 as usize) >= self.terms.len() {
            return Err("invalid functional array term".into());
        }
        let data = self.terms.get(term);
        let count = crate::residual::term_child_count(data)
            .ok_or_else(|| EvalError::from("unsupported functional array node"))?;
        self.charge_functional_work(count)?;
        let mut invalid = false;
        crate::residual::for_each_term_child(data, |child| {
            invalid |= self.terms.entry_stamp(child).is_none();
        })
        .ok_or_else(|| EvalError::from("unsupported functional array node"))?;
        if invalid {
            return Err("invalid functional array child".into());
        }
        // The same checked projection contract owns ordinary array semantics.
        if let Some(projected) = self.default_projection_target(term)? {
            return self.functional_snapshot(projected, depth + 1);
        }
        if let Some(value) = self.checked_or_identity_snapshot(term, depth)? {
            return Ok(value);
        }
        if let Some(value) = self.periodic_lambda_snapshot(term, depth)? {
            return Ok(value);
        }
        if let Some(value) = self.fill_lambda_snapshot(term, depth)? {
            return Ok(value);
        }
        if let Some(recipe) = recognize_range_lambda(self.terms, term) {
            self.authenticate_range_grammar(term, &recipe)?;
            for capture in [
                Some(recipe.destination),
                Some(recipe.source),
                Some(recipe.lo),
                Some(recipe.hi),
                recipe.source_lo,
            ]
            .into_iter()
            .flatten()
            {
                if self.term_contains(capture, recipe.bound)? {
                    return Err("functional array captures its lexical binder".into());
                }
            }
            let lo = self.eval_operand(recipe.lo, depth + 1)?;
            let hi = self.eval_operand(recipe.hi, depth + 1)?;
            let destination = self.functional_snapshot(recipe.destination, depth + 1)?;
            if matches!((&lo, &hi),
                (ModelValue::BitVec { value: lo, width: 64 },
                 ModelValue::BitVec { value: hi, width: 64 })
                    if !lo.is_negative() && lo.bits() <= 64 && !hi.is_negative() && hi.bits() <= 64 && lo >= hi)
            {
                return Ok(destination); // exact unsigned empty interval, no source reads
            }
            let source = self.functional_snapshot(recipe.source, depth + 1)?;
            let source_lo = match recipe.source_lo {
                Some(offset) => self.eval_operand(offset, depth + 1)?,
                None => ModelValue::bitvec(BigInt::from(0), 64),
            };
            return self.snapshot_work(|work| {
                ArraySnapshot::range_copy(destination, source, &lo, &hi, &source_lo, work)
            });
        }
        if let TermData::App(Symbol::Named(symbol), args) = self.terms.get(term) {
            if symbol.as_str() == "store" && args.len() == 3 {
                let Sort::Array(sort) = self.terms.sort(term) else {
                    return Err("functional store has nonarray result sort".into());
                };
                if args.iter().any(|arg| (arg.0 as usize) >= self.terms.len())
                    || self.terms.sort(args[0]) != self.terms.sort(term)
                    || self.terms.sort(args[1]) != &sort.index_sort
                    || self.terms.sort(args[2]) != &sort.element_sort
                {
                    return Err("functional store occurrence metadata differs from operands".into());
                }
                let base = self.functional_snapshot(args[0], depth + 1)?;
                let index = self.eval_operand(args[1], depth + 1)?;
                let value = self.eval_operand(args[2], depth + 1)?;
                return self.snapshot_work(|work| ArraySnapshot::store(base, &index, &value, work));
            }
        }
        // Opaque as-array/map/UF representations do not become new complete
        // functional authority through this range route. Existing strict
        // function-backed-array controls continue to own those cases.
        let admitted_finite = matches!(self.terms.get(term), TermData::Var(..))
            || matches!(self.terms.get(term), TermData::App(Symbol::Named(symbol), args) if symbol.as_str() == "const-array" && args.len() == 1);
        if !admitted_finite {
            return Err("unsupported functional array constructor".into());
        }
        if let TermData::App(_, args) = self.terms.get(term) {
            let Sort::Array(sort) = self.terms.sort(term) else {
                return Err("functional constant has nonarray result sort".into());
            };
            if (args[0].0 as usize) >= self.terms.len()
                || self.terms.sort(args[0]) != &sort.element_sort
            {
                return Err("functional constant occurrence metadata differs from operand".into());
            }
        }
        let value = self.eval_array_value(term, depth + 1)?;
        self.snapshot_work(|work| ArraySnapshot::finite(value, self.terms.sort(term), work))
    }

    fn checked_or_identity_snapshot(
        &self,
        term: TermId,
        depth: usize,
    ) -> EvalResult<Option<Arc<ArraySnapshot>>> {
        match self.checked_array_snapshot(term)? {
            Some(value) => Ok(Some(value)),
            None => self.identity_lambda_snapshot(term, depth),
        }
    }

    fn identity_lambda_snapshot(
        &self,
        term: TermId,
        depth: usize,
    ) -> EvalResult<Option<Arc<ArraySnapshot>>> {
        let Some(recipe) = recognize_identity_lambda(self.terms, term) else {
            return Ok(None);
        };
        // Even a same-sort projection of the inner select changes the whole
        // function. Consult the actual occurrence before literal interpretation.
        if self.default_projection_target(recipe.read)?.is_some() {
            return Err("projected identity lambda has different semantics".into());
        }
        if self.term_contains(recipe.array, recipe.bound)? {
            return Err("identity lambda captures its lexical binder".into());
        }
        self.functional_snapshot(recipe.array, depth + 1).map(Some)
    }

    fn authenticate_range_grammar(
        &self,
        root: TermId,
        recipe: &crate::RangeLambda,
    ) -> EvalResult<()> {
        let captures = [
            recipe.destination,
            recipe.source,
            recipe.lo,
            recipe.hi,
            recipe.bound,
        ];
        let mut pending = vec![root];
        let mut seen = HashSet::new();
        while let Some(term) = pending.pop() {
            self.charge_functional_work(1)?;
            if !seen.insert(term) || captures.contains(&term) || recipe.source_lo == Some(term) {
                continue;
            }
            if (term.0 as usize) >= self.terms.len() {
                return Err("invalid range grammar term".into());
            }
            if let TermData::App(_, args) = self.terms.get(term) {
                if let Some(index) = self
                    .model
                    .projection_argument(term)
                    .map_err(|error| error.to_string())?
                {
                    let selected = args
                        .get(index)
                        .copied()
                        .ok_or("range projection selects an absent argument")?;
                    if self.terms.sort(selected) != self.terms.sort(term) {
                        return Err("range projection changes the result sort".into());
                    }
                    // This program was recognized as literal range grammar.
                    // A projected inner operator denotes a different program.
                    return Err("projected range grammar requires a different interpreter".into());
                }
            }
            let children = self.terms.children(term);
            self.charge_functional_work(children.len())?;
            pending
                .try_reserve(children.len())
                .map_err(|_| "range grammar allocation refused")?;
            pending.extend(children);
        }
        Ok(())
    }

    pub(super) fn functional_array_equality(
        &self,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<Option<bool>> {
        if args.is_empty()
            || args
                .iter()
                .any(|term| (term.0 as usize) >= self.terms.len())
        {
            return Err("invalid functional equality operands".into());
        }
        if !matches!(self.terms.sort(args[0]), Sort::Array(_)) {
            return Ok(None);
        }
        if args
            .iter()
            .any(|term| self.terms.sort(*term) != self.terms.sort(args[0]))
        {
            return Err("functional equality operand sorts differ".into());
        }
        // This new route requires explicitly installed snapshot data. Merely
        // seeing a lambda never authorizes a different old model assignment.
        let mut owned = false;
        for &term in args {
            owned |= self.checked_array_snapshot(term)?.is_some();
        }
        if !owned {
            return Ok(None);
        }
        let first = self.functional_snapshot(args[0], depth + 1)?;
        for &term in &args[1..] {
            let other = self.functional_snapshot(term, depth + 1)?;
            match self.snapshot_work(|work| {
                first.equality_with_stop(&other, work, &mut || {
                    self.model.functional_array_interrupted()
                })
            })? {
                Some(true) => {}
                Some(false) => return Ok(Some(false)),
                None => {
                    return Err("functional array equality not independently established".into())
                }
            }
        }
        Ok(Some(true))
    }
}

struct CaptureGuard<'a>(&'a Cell<usize>);
impl Drop for CaptureGuard<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get().saturating_sub(1));
    }
}

#[cfg(test)]
mod tests;
