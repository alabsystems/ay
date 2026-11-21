// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A structural periodicity proof and exhaustive interpretation of its quotient.
//! Recognizing a header supplies no interpretation or model-validation result.

use num_traits::ToPrimitive;

use super::*;
use crate::recognize_int_scalar_lambda;

impl Evaluator<'_> {
    pub(super) fn periodic_lambda_snapshot(
        &self,
        term: TermId,
        depth: usize,
    ) -> EvalResult<Option<Arc<ArraySnapshot>>> {
        self.charge_functional_work(1)?;
        let Some(recipe) = recognize_int_scalar_lambda(self.terms, term) else {
            return Ok(None);
        };
        if self.term_depends_on_local_binding(term)? {
            return Err("periodic array captures an active lexical environment".into());
        }
        self.functional_capture_depth
            .set(self.functional_capture_depth.get() + 1);
        let _guard = CaptureGuard(&self.functional_capture_depth);
        let period = self.periodic_grammar(recipe.bound, recipe.body, depth)?;
        let bytes = period
            .checked_mul(std::mem::size_of::<ModelValue>())
            .ok_or("periodic residue allocation overflow")?;
        self.charge_functional_work(
            bytes
                .checked_add(period)
                .ok_or("periodic residue work overflow")?,
        )?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(period)
            .map_err(|_| "periodic residue allocation refused")?;
        for residue in 0..period {
            self.charge_functional_work(1)?;
            let value = self.eval_with_binding(
                recipe.bound,
                ModelValue::Int(BigInt::from(residue)),
                recipe.body,
                depth + 1,
            )?;
            self.ensure_value_inhabits_sort(&value, self.terms.sort(recipe.body))?;
            if !matches!(&value, ModelValue::Bool(_) | ModelValue::Int(_)) {
                return Err("periodic cell is not a closed scalar value".into());
            }
            self.admit_value(&value)?;
            values.push(value);
        }
        let captured = self
            .snapshot_work(|work| ArraySnapshot::periodic(&values, self.terms.sort(term), work))?;
        self.charge_functional_work(0)?;
        Ok(Some(captured))
    }

    fn periodic_grammar(&self, bound: TermId, body: TermId, depth: usize) -> EvalResult<usize> {
        self.charge_functional_work(std::mem::size_of::<(TermId, usize)>())?;
        let mut pending = vec![(body, 0usize)];
        let mut period = 1usize;
        while let Some((term, local_depth)) = pending.pop() {
            self.charge_functional_work(1)?;
            if local_depth > 64 || self.terms.entry_stamp(term).is_none() {
                return Err("periodic grammar depth or live term admission refused".into());
            }
            if !matches!(self.terms.sort(term), Sort::Bool | Sort::Int) {
                return Err("periodic grammar contains a nonscalar operand".into());
            }
            if !self.term_contains(term, bound)? {
                let value = self.eval_operand(term, depth + local_depth + 1)?;
                self.ensure_value_inhabits_sort(&value, self.terms.sort(term))?;
                if !matches!(&value, ModelValue::Bool(_) | ModelValue::Int(_)) {
                    return Err(
                        "periodic ground capture has no closed scalar interpretation".into(),
                    );
                }
                continue;
            }
            if term == bound {
                return Err("periodic body uses its binder outside a residue operation".into());
            }
            let conditional;
            let negated;
            let children: &[TermId] = match self.terms.get(term) {
                TermData::App(_, args) => args,
                TermData::Not(inner) => {
                    negated = [*inner];
                    &negated
                }
                TermData::Ite(condition, positive, negative) => {
                    conditional = [*condition, *positive, *negative];
                    &conditional
                }
                _ => return Err("periodic grammar contains an unsupported binder or node".into()),
            };
            self.charge_functional_work(children.len())?;
            if children
                .iter()
                .any(|child| self.terms.entry_stamp(*child).is_none())
            {
                return Err("periodic grammar contains an invalid child".into());
            }
            if let TermData::App(Symbol::Named(symbol), args) = self.terms.get(term) {
                if self
                    .model
                    .projection_argument(term)
                    .map_err(|error| error.to_string())?
                    .is_some()
                {
                    return Err(
                        "periodic source operator has a different projection interpretation".into(),
                    );
                }
                if symbol.as_str() == "mod"
                    && args.len() == 2
                    && args[0] == bound
                    && self.terms.sort(term) == &Sort::Int
                {
                    let modulus =
                        self.periodic_positive_modulus(args[1], bound, depth + local_depth)?;
                    period = self.snapshot_work(|work| {
                        crate::functional_array::periodic::common_period(period, modulus, work)
                    })?;
                    continue;
                }
                if !self.periodic_operator_typed(term, symbol.as_str(), args) {
                    return Err("unsupported or ill-sorted periodic scalar operator".into());
                }
                if matches!(symbol.as_str(), "div" | "mod") {
                    self.periodic_positive_modulus(args[1], bound, depth + local_depth)?;
                }
            } else if let TermData::Ite(condition, positive, negative) = self.terms.get(term) {
                if self.terms.sort(*condition) != &Sort::Bool
                    || self.terms.sort(*positive) != self.terms.sort(term)
                    || self.terms.sort(*negative) != self.terms.sort(term)
                {
                    return Err("periodic conditional has inconsistent sorts".into());
                }
            } else if let TermData::Not(inner) = self.terms.get(term) {
                if self.terms.sort(term) != &Sort::Bool || self.terms.sort(*inner) != &Sort::Bool {
                    return Err("periodic negation has inconsistent sorts".into());
                }
            } else {
                return Err("periodic grammar contains an unsupported binder or node".into());
            }
            let capacity = pending
                .len()
                .checked_add(children.len())
                .ok_or("periodic pending overflow")?;
            self.charge_functional_work(
                capacity
                    .checked_mul(std::mem::size_of::<(TermId, usize)>())
                    .ok_or("periodic pending allocation overflow")?,
            )?;
            pending
                .try_reserve_exact(children.len())
                .map_err(|_| "periodic pending allocation refused")?;
            pending.extend(children.iter().map(|&child| (child, local_depth + 1)));
        }
        Ok(period)
    }

    fn periodic_positive_modulus(
        &self,
        term: TermId,
        bound: TermId,
        depth: usize,
    ) -> EvalResult<usize> {
        if self.terms.sort(term) != &Sort::Int || self.term_contains(term, bound)? {
            return Err("periodic modulus depends on its binder or has the wrong sort".into());
        }
        let ModelValue::Int(value) = self.eval_operand(term, depth + 1)? else {
            return Err("periodic modulus lacks an integer interpretation".into());
        };
        self.charge_functional_work(128)?;
        value
            .to_usize()
            .filter(|period| *period > 0)
            .ok_or_else(|| "periodic modulus must be a positive bounded integer".into())
    }

    fn periodic_operator_typed(&self, term: TermId, name: &str, args: &[TermId]) -> bool {
        let ints = || args.iter().all(|arg| self.terms.sort(*arg) == &Sort::Int);
        let bools = || args.iter().all(|arg| self.terms.sort(*arg) == &Sort::Bool);
        let result = self.terms.sort(term);
        match name {
            "+" | "*" => args.len() >= 2 && result == &Sort::Int && ints(),
            "-" => (1..=2).contains(&args.len()) && result == &Sort::Int && ints(),
            "div" | "mod" => args.len() == 2 && result == &Sort::Int && ints(),
            "<" | "<=" | ">" | ">=" => args.len() == 2 && result == &Sort::Bool && ints(),
            "=" | "distinct" => {
                args.len() >= 2
                    && result == &Sort::Bool
                    && args
                        .iter()
                        .all(|arg| self.terms.sort(*arg) == self.terms.sort(args[0]))
            }
            "and" | "or" => result == &Sort::Bool && bools(),
            "not" => args.len() == 1 && result == &Sort::Bool && bools(),
            "=>" | "xor" => args.len() == 2 && result == &Sort::Bool && bools(),
            "ite" => {
                args.len() == 3
                    && self.terms.sort(args[0]) == &Sort::Bool
                    && self.terms.sort(args[1]) == result
                    && self.terms.sort(args[2]) == result
            }
            _ => false,
        }
    }
}
