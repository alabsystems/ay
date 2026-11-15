// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ABVFP lane's use of the unread-array elimination: solve the rewritten
//! window, then give every eliminated array the value of its definition.
//!
//! The rewrite and its equivalence argument live in `flatten_reads::unread`.
//! This module owns the model half: a `sat` from the rewritten window is
//! published only after each eliminated `X` of `(= X t)` holds `M(t)`, read
//! back in reverse elimination order. Anything it cannot evaluate drops the
//! model and answers `unknown` with a reason naming the gap; the independent
//! gate still re-checks every authored assertion afterwards.

use ay_arrays::{ArrayInterpretation, ArrayModel};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::flatten_reads::eliminate_unread_array_equalities;
use crate::executor::model::{EvalValue, Model};
use crate::executor::Executor;
use crate::executor_format::format_bitvec;
use crate::executor_types::{Result, SolveResult, UnknownReason};

const RECONSTRUCTION_REFUSED: &str =
    "ABVFP unread-array elimination: an eliminated array definition could not be evaluated \
     under the model of the rewritten window, so its sat is withheld; unsat stays valid";

impl Executor {
    /// Solve the ABVFP window after dropping the definitions of arrays that
    /// occur nowhere else (see `flatten_reads::unread`).
    pub(super) fn solve_abvfp_eliminating_unread_arrays(&mut self) -> Result<SolveResult> {
        let Some(elimination) =
            eliminate_unread_array_equalities(&mut self.ctx.terms, &self.ctx.assertions)
        else {
            return self.solve_abvfp_window();
        };
        self.last_statistics.set_int(
            "abvfp_unread_arrays.eliminated",
            elimination.definitions.len() as u64,
        );
        let authored = std::mem::replace(&mut self.ctx.assertions, elimination.assertions);
        let result = self.solve_abvfp_window();
        let window = std::mem::replace(&mut self.ctx.assertions, authored);
        match result {
            Ok(SolveResult::Sat) => {
                if self.attach_unread_array_definitions(&elimination.definitions, &window) {
                    Ok(SolveResult::Sat)
                } else {
                    self.last_model = None;
                    self.last_model_validated = false;
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    self.record_unknown_diagnostic(
                        UnknownReason::Incomplete,
                        RECONSTRUCTION_REFUSED,
                    );
                    Ok(SolveResult::Unknown)
                }
            }
            other => other,
        }
    }

    /// Give each eliminated array the value of its definition, latest
    /// elimination first. Returns `false` (fail closed) when any definition
    /// cannot be evaluated.
    ///
    /// A scalar constant that only an eliminated definition mentions is
    /// unconstrained by the rewritten window, so it has no value yet; it is
    /// completed first with its sort's canonical default, through the model's
    /// fill-only completion slot, so the definitions, the printer and the gate
    /// all read one value.
    fn attach_unread_array_definitions(
        &mut self,
        definitions: &[(TermId, TermId)],
        window: &[TermId],
    ) -> bool {
        let window_vars = self.window_variables(window);
        let free = self.unconstrained_scalars(definitions, &window_vars);
        let Some(model) = self.last_model.as_mut() else {
            return false;
        };
        for (var, value) in free {
            model.completed_values.entry(var).or_insert(value);
        }
        crate::executor::model::eval_memo_clear();
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        let mut values: HashMap<TermId, ArrayInterpretation> = model
            .array_model
            .as_ref()
            .map(|arrays| arrays.array_values.clone())
            .unwrap_or_default();
        for &(array, definition) in definitions.iter().rev() {
            let Some(value) = self.eval_unread_array(model, definition, &window_vars, &mut values)
            else {
                return false;
            };
            values.insert(array, value);
        }
        let Some(model) = self.last_model.as_mut() else {
            return false;
        };
        match model.array_model.as_mut() {
            Some(arrays) => arrays.array_values = values,
            None => {
                model.array_model = Some(ArrayModel {
                    array_values: values,
                    ..Default::default()
                });
            }
        }
        crate::executor::model::eval_memo_clear();
        true
    }

    /// The non-array constants the definitions mention but the rewritten
    /// window does not, each with the canonical default of its sort (a
    /// bit-vector zero, `false`, a floating-point `+zero`, `RNE`, ...). An
    /// array is completed by `eval_unread_array`; a sort without a canonical
    /// default stays unvalued, so its definition fails closed.
    fn unconstrained_scalars(
        &self,
        definitions: &[(TermId, TermId)],
        window_vars: &HashSet<TermId>,
    ) -> Vec<(TermId, EvalValue)> {
        let roots: Vec<TermId> = definitions
            .iter()
            .map(|&(_, definition)| definition)
            .collect();
        let mut free: Vec<(TermId, EvalValue)> = Vec::new();
        for var in self.window_variables(&roots) {
            if window_vars.contains(&var) {
                continue;
            }
            if let Some(value) = self.unconstrained_default_value(self.ctx.terms.sort(var)) {
                free.push((var, value));
            }
        }
        free.sort_unstable_by_key(|&(var, _)| var);
        free
    }

    /// Every declared constant reachable from `window`.
    fn window_variables(&self, window: &[TermId]) -> HashSet<TermId> {
        let mut vars = HashSet::default();
        let mut seen = HashSet::default();
        let mut stack = window.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Var(..) => {
                    vars.insert(term);
                }
                TermData::App(_, args) => stack.extend_from_slice(args),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                _ => {}
            }
        }
        vars
    }

    /// The value of an array-sorted definition under `model`: a declared
    /// array, a constant array, a `store` over one, or an `ite` between such
    /// terms.
    ///
    /// An array the rewritten window no longer mentions is unconstrained by
    /// it, so it is completed with the zero array and recorded in `values`
    /// for every later reader. One the window still mentions must already
    /// carry a value; one whose extraction dropped a conflicting cell never
    /// does (`read_conflicted`).
    fn eval_unread_array(
        &self,
        model: &Model,
        term: TermId,
        window_vars: &HashSet<TermId>,
        values: &mut HashMap<TermId, ArrayInterpretation>,
    ) -> Option<ArrayInterpretation> {
        let Sort::Array(arr) = self.ctx.terms.sort(term).clone() else {
            return None;
        };
        let (Sort::BitVec(index), Sort::BitVec(element)) = (&arr.index_sort, &arr.element_sort)
        else {
            return None;
        };
        match self.ctx.terms.get(term).clone() {
            TermData::Var(..) => {
                if model
                    .array_model
                    .as_ref()
                    .is_some_and(|arrays| arrays.is_withheld(&term))
                {
                    return None;
                }
                if let Some(value) = values.get(&term) {
                    return Some(value.clone());
                }
                if window_vars.contains(&term) {
                    return None;
                }
                let zero = ArrayInterpretation {
                    default: Some(format_bitvec(&BigInt::from(0u32), element.width)),
                    stores: Vec::new(),
                    index_sort: Some(arr.index_sort.clone()),
                    element_sort: Some(arr.element_sort.clone()),
                };
                values.insert(term, zero.clone());
                Some(zero)
            }
            TermData::App(sym, args) if sym.name() == "const-array" && args.len() == 1 => {
                let EvalValue::BitVec { value, .. } = self.evaluate_term(model, args[0]) else {
                    return None;
                };
                Some(ArrayInterpretation {
                    default: Some(format_bitvec(&value, element.width)),
                    stores: Vec::new(),
                    index_sort: Some(arr.index_sort.clone()),
                    element_sort: Some(arr.element_sort.clone()),
                })
            }
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                let mut base = self.eval_unread_array(model, args[0], window_vars, values)?;
                let EvalValue::BitVec { value: at, .. } = self.evaluate_term(model, args[1]) else {
                    return None;
                };
                let EvalValue::BitVec { value: stored, .. } = self.evaluate_term(model, args[2])
                else {
                    return None;
                };
                // Newest entry first: a direct lookup takes the first match.
                base.stores.insert(
                    0,
                    (
                        format_bitvec(&at, index.width),
                        format_bitvec(&stored, element.width),
                    ),
                );
                Some(base)
            }
            TermData::Ite(c, t, e) => match self.evaluate_term(model, c) {
                EvalValue::Bool(true) => self.eval_unread_array(model, t, window_vars, values),
                EvalValue::Bool(false) => self.eval_unread_array(model, e, window_vars, values),
                _ => None,
            },
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests;
