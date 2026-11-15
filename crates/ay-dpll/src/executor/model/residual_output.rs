// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read retained residual completions through the independent typed evaluator.

use std::cell::Cell;

use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use ay_model_check::ModelValue;

use super::{dt_construct, eval_value_has_exact_sort, EvalValue, Executor, HashSet, Model};

const MAX_QUERY_EDGES: usize = 262_144;

thread_local! {
    // Independent UF callbacks may consult the legacy evaluator. They must not
    // recursively start another completed-model evaluation of the same term.
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
}

struct EvaluationScope;

impl EvaluationScope {
    fn enter() -> Self {
        ACTIVE.with(|active| active.set(true));
        Self
    }
}

impl Drop for EvaluationScope {
    fn drop(&mut self) {
        ACTIVE.with(|active| active.set(false));
    }
}

impl Executor {
    /// `None` preserves the legacy lane only when it does not own this read.
    /// A stale package, resource stop or unevaluable dependent term is terminal.
    pub(super) fn completed_model_value(
        &self,
        model: &Model,
        term: TermId,
    ) -> Result<Option<ModelValue>, ()> {
        if !model.has_residual_arrays() {
            return Ok(None);
        }
        if !model.residual_arrays_are_current(&self.ctx)
            || self.external_stop_reason().is_some()
            || self.w4_budget_exhausted()
        {
            return Err(());
        }
        if ACTIVE.with(Cell::get) {
            return Ok(None);
        }
        if !self.depends_on_residual_array(model, term)? {
            return Ok(None);
        }
        // The independent evaluator owns lexical bindings. Do not replace a
        // materializer's contextual term evaluation with a fresh empty scope.
        if super::scoped_term_evaluation_override_active() {
            return Err(());
        }
        let scope = EvaluationScope::enter();
        let result = self.independent_completed_model_value(model, term);
        drop(scope);
        if self.external_stop_reason().is_some()
            || self.w4_budget_exhausted()
            || !model.residual_arrays_are_current(&self.ctx)
        {
            return Err(());
        }
        result.map(Some).ok_or(())
    }

    /// Memoized across one evaluation-memo session.
    ///
    /// The uncached walk is O(subtree). It runs from `completed_model_value`,
    /// which sits at the TOP of the recursive `evaluate_term_unstopped` — ahead
    /// of the result memo, deliberately, so a typed residual completion beats
    /// every stale scalar pin. That ordering means a term tree of N nodes asks
    /// this predicate N times, once per subterm, and without a cache the pass
    /// is O(N^2) with a fresh Vec and HashSet per call. Every model carrying
    /// residual arrays paid that, and since `install_and_replay` runs
    /// unconditionally in the independent model gate, that is most of them.
    ///
    /// Caching is sound for exactly the session's lifetime: the answer is a
    /// function of the term graph and the installed residual-array batch, the
    /// caller has already checked `residual_arrays_are_current`, and
    /// `install_residual_arrays` clears this memo.
    fn depends_on_residual_array(&self, model: &Model, root: TermId) -> Result<bool, ()> {
        if let Some(hit) = super::eval_memo::residual_dep_get(root) {
            return Ok(hit);
        }
        let mut visited = HashSet::default();
        let answer = self.walk_residual_array_dependency(model, root, &mut visited)?;
        if answer {
            // Only the root is decided. An early `true` leaves the other
            // visited nodes genuinely unknown, so they must not be recorded.
            super::eval_memo::residual_dep_put([root], true);
        } else {
            // The walk exhausted its frontier without finding a residual array
            // or an aggregate node, so EVERY node it visited is independently
            // free of one too. Recording the whole set is what makes the
            // enclosing evaluation linear rather than quadratic.
            super::eval_memo::residual_dep_put(visited.iter().copied(), false);
        }
        Ok(answer)
    }

    fn walk_residual_array_dependency(
        &self,
        model: &Model,
        root: TermId,
        visited: &mut HashSet<TermId>,
    ) -> Result<bool, ()> {
        if !super::evaluation_copies::pay(1, 4 * std::mem::size_of::<TermId>()) {
            return Err(());
        }
        let mut pending = vec![root];
        let mut remaining = MAX_QUERY_EDGES;
        while let Some(term) = pending.pop() {
            remaining = remaining.checked_sub(1).ok_or(())?;
            if remaining % 64 == 0 && self.external_stop_reason().is_some() {
                return Err(());
            }
            if self.ctx.terms.entry_stamp(term).is_none() {
                return Err(());
            }
            if !super::evaluation_copies::pay(1, 4 * std::mem::size_of::<TermId>()) {
                return Err(());
            }
            if !visited.insert(term) {
                continue;
            }
            if model.residual_array_value(&self.ctx, term)?.is_some()
                || model.constant_array_value(self, term)?.is_some()
            {
                return Ok(true);
            }
            let sort = self.ctx.terms.sort(term);
            // An alias/constructor can depend on a completed array through an
            // asserted definition rather than its syntactic children. Treat
            // aggregate nodes conservatively; the independent view resolves
            // those exact definitions and never invents a missing value.
            if matches!(sort, Sort::Array(_) | Sort::Datatype(_))
                || self.datatype_sort_name(sort).is_some()
            {
                return Ok(true);
            }
            let children = match self.ctx.terms.get(term) {
                TermData::Const(_) | TermData::Var(_, _) => continue,
                TermData::App(_, args) => args.as_slice(),
                TermData::Not(child) => std::slice::from_ref(child),
                TermData::Ite(condition, then_value, else_value) => {
                    if !super::evaluation_copies::pay(3, 6 * std::mem::size_of::<TermId>()) {
                        return Err(());
                    }
                    if pending.len().checked_add(3).is_none_or(|n| n > remaining) {
                        return Err(());
                    }
                    pending.extend([*condition, *then_value, *else_value]);
                    continue;
                }
                TermData::Let(bindings, body) => {
                    let count = bindings.len().checked_add(1).ok_or(())?;
                    if !count
                        .checked_mul(2 * std::mem::size_of::<TermId>())
                        .is_some_and(|bytes| super::evaluation_copies::pay(count, bytes))
                    {
                        return Err(());
                    }
                    if pending
                        .len()
                        .checked_add(count)
                        .is_none_or(|n| n > remaining)
                    {
                        return Err(());
                    }
                    pending.push(*body);
                    pending.extend(bindings.iter().map(|(_, value)| *value));
                    continue;
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    // Triggers do not contribute values to the formula.
                    std::slice::from_ref(body)
                }
                _ => return Err(()),
            };
            if !children
                .len()
                .checked_mul(2 * std::mem::size_of::<TermId>())
                .is_some_and(|bytes| super::evaluation_copies::pay(children.len(), bytes))
            {
                return Err(());
            }
            if pending
                .len()
                .checked_add(children.len())
                .is_none_or(|n| n > remaining)
            {
                return Err(());
            }
            pending.extend_from_slice(children);
        }
        Ok(false)
    }

    /// The old value carrier has no aggregate variant. Only exact supported
    /// scalar conversions may enter it; arrays/records remain typed above.
    pub(super) fn completed_scalar_value(&self, value: &ModelValue, sort: &Sort) -> EvalValue {
        if !matches!(
            value,
            ModelValue::Bool(_)
                | ModelValue::Int(_)
                | ModelValue::Real(_)
                | ModelValue::BitVec { .. }
                | ModelValue::Str(_)
        ) {
            return EvalValue::Unknown;
        }
        if !super::evaluation_copies::model_value(value) {
            return EvalValue::Unknown;
        }
        let value = dt_construct::mv_to_eval(value);
        if eval_value_has_exact_sort(&value, sort) {
            value
        } else {
            EvalValue::Unknown
        }
    }
}

#[cfg(test)]
mod tests;
