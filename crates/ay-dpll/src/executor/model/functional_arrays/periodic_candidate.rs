// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One bounded model proposal after an incomplete ordinary search. Every
//! original root must independently hold before the ordinary SAT funnel runs.

use ay_core::term::TermData;
use ay_model_check::{confirm_completed_model, recognize_int_scalar_lambda, GateVerdict};

use super::*;
use crate::executor::model::{
    independent_gate::IndependentModelView,
    recovery_admission::{pay_current, pay_eval_value_copy, RecoveryScope},
    EvalValue,
};
use crate::executor_types::UnknownReason;

fn reserve<T>(values: &mut Vec<T>, extra: usize) -> Option<()> {
    let capacity = values.len().checked_add(extra)?;
    let bytes = capacity
        .checked_add(values.len())?
        .checked_mul(std::mem::size_of::<T>())?;
    pay_current(extra.checked_add(bytes)?, bytes).then_some(())?;
    values.try_reserve_exact(extra).ok()
}

/// Enumerate typed scalar identities from the full source graph. A lambda's
/// binder is excluded even when it also occurs free; that conservative case
/// can lose a model proposal but cannot grant a false interpretation.
fn source_scalars(exec: &Executor, roots: &[TermId]) -> Option<Vec<TermId>> {
    let mut pending = Vec::new();
    reserve(&mut pending, roots.len())?;
    pending.extend_from_slice(roots);
    let mut variables = Vec::new();
    let mut bound = Vec::new();
    let mut periodic = false;
    while let Some(term) = pending.pop() {
        pay_current(1, 0).then_some(())?;
        exec.ctx.terms.entry_stamp(term)?;
        if let Some(recipe) = recognize_int_scalar_lambda(&exec.ctx.terms, term) {
            periodic = true;
            reserve(&mut bound, 1)?;
            bound.push(recipe.bound);
        }
        let fixed;
        let negated;
        let children: &[TermId] = match exec.ctx.terms.get(term) {
            TermData::Var(..) => {
                if matches!(exec.ctx.terms.sort(term), Sort::Bool | Sort::Int) {
                    pay_current(variables.len() + 1, 0).then_some(())?;
                    if !variables.contains(&term) {
                        reserve(&mut variables, 1)?;
                        variables.push(term);
                    }
                }
                &[]
            }
            TermData::Const(..) => &[],
            TermData::App(ay_core::Symbol::Named(name), args)
                if ay_frontend::is_canonical_theory_operator_identity(name) =>
            {
                args
            }
            // This completion owns no missing UF/function interpretation.
            // Ordinary search models with those carriers keep their own lane.
            TermData::App(..) => return None,
            TermData::Not(inner) => {
                negated = [*inner];
                &negated
            }
            TermData::Ite(condition, positive, negative) => {
                fixed = [*condition, *positive, *negative];
                &fixed
            }
            // A separate quantified interpretation checker owns those roots.
            // This ground model-completion proposal never narrows their scope.
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return None,
            _ => return None,
        };
        reserve(&mut pending, children.len())?;
        pending.extend_from_slice(children);
    }
    if !periodic {
        return None;
    }
    pay_current(variables.len().checked_mul(bound.len().checked_add(1)?)?, 0).then_some(())?;
    variables.retain(|term| !bound.contains(term));
    Some(variables)
}

fn reserve_scalar(model: &mut Model, sort: &Sort) -> Option<()> {
    // Reserve the real destination before the shared typed insertion routine
    // clones a value. Sparse-table probe/copy work is charged by capacity.
    match sort {
        Sort::Bool => {
            let capacity = model
                .bool_overrides
                .capacity()
                .checked_add(1)?
                .checked_mul(4)?;
            let bytes = capacity.checked_mul(std::mem::size_of::<(TermId, bool)>() + 1)?;
            pay_current(bytes, bytes).then_some(())?;
            model.bool_overrides.try_reserve(1).ok()
        }
        Sort::Int => {
            if let Some(model) = model.lia_model.as_mut() {
                let capacity = model.values.capacity().checked_add(1)?.checked_mul(4)?;
                let bytes = capacity
                    .checked_mul(std::mem::size_of::<(TermId, num_bigint::BigInt)>() + 1)?;
                pay_current(bytes, bytes).then_some(())?;
                model.values.try_reserve(1).ok()
            } else if let Some(model) = model.lra_model.as_mut() {
                let capacity = model.values.capacity().checked_add(1)?.checked_mul(4)?;
                let bytes = capacity
                    .checked_mul(std::mem::size_of::<(TermId, num_rational::BigRational)>() + 1)?;
                pay_current(bytes, bytes).then_some(())?;
                model.values.try_reserve(1).ok()
            } else {
                let capacity = model
                    .completed_values
                    .capacity()
                    .checked_add(1)?
                    .checked_mul(4)?;
                let bytes = capacity.checked_mul(std::mem::size_of::<(TermId, EvalValue)>() + 1)?;
                pay_current(bytes, bytes).then_some(())?;
                model.completed_values.try_reserve(1).ok()
            }
        }
        _ => None,
    }
}

pub(super) fn scalar_value(
    exec: &Executor,
    model: &Model,
    variable: TermId,
    roots: &[TermId],
) -> Option<EvalValue> {
    let view = IndependentModelView::new(exec, model);
    let evaluator = Evaluator::new(&exec.ctx.terms, &view);
    let mut work = MAX_FUNCTIONAL_WORK.saturating_sub(
        exec.evaluation_attempt()
            .functional_work_counter()
            .load(Ordering::Acquire),
    );
    let mut evaluate = |term| match evaluator.evaluate_with_functional_work(term, &mut work) {
        EvalOutcome::Value(ModelValue::Bool(value)) => Some(EvalValue::Bool(value)),
        EvalOutcome::Value(ModelValue::Int(value)) => Some(EvalValue::Rational(
            num_rational::BigRational::from_integer(value),
        )),
        _ => None,
    };
    // Integer evaluation has a legacy implicit-zero fallback. Only an
    // actual stored assignment may precede authored equality proposals.
    let lookup_work = model
        .lia_model
        .as_ref()
        .map_or(0, |model| model.values.capacity())
        .checked_add(
            model
                .lra_model
                .as_ref()
                .map_or(0, |model| model.values.capacity()),
        )?
        .checked_add(model.euf_model.as_ref().map_or(0, |model| {
            model
                .term_values
                .capacity()
                .saturating_add(model.int_values.capacity())
        }))?
        .checked_add(model.completed_values.capacity())?
        .checked_add(exec.recorded_var_substitutions.capacity())?
        .checked_mul(2)?
        .checked_add(8)?;
    pay_current(lookup_work, 0).then_some(())?;
    let assigned =
        exec.ctx.terms.sort(variable) != &Sort::Int || Executor::model_assigns_int(model, variable);
    if assigned {
        if let Some(value) = evaluate(variable) {
            return Some(value);
        }
    }
    if let Some(&replacement) = exec.recorded_var_substitutions.get(&variable) {
        if replacement != variable {
            if let Some(value) = evaluate(replacement) {
                return Some(value);
            }
        }
    }
    for &root in roots {
        pay_current(1, 0).then_some(())?;
        let TermData::App(ay_core::Symbol::Named(name), args) = exec.ctx.terms.get(root) else {
            continue;
        };
        if name.as_str() != "=" || args.len() != 2 {
            continue;
        }
        let other = if args[0] == variable {
            args[1]
        } else if args[1] == variable {
            args[0]
        } else {
            continue;
        };
        if let Some(value) = evaluate(other) {
            return Some(value);
        }
    }
    None
}

impl Executor {
    pub(in crate::executor) fn try_periodic_array_model_completion(&mut self) -> bool {
        if self.publish_evaluation_stop()
            || self.external_stop_reason().is_some()
            || !matches!(
                self.last_unknown_reason,
                None | Some(
                    UnknownReason::Unknown
                        | UnknownReason::Incomplete
                        | UnknownReason::Unsupported
                        | UnknownReason::UnsupportedArithmetic
                )
            )
            || self.solve_deadline.expired()
            || !self.ctx.objectives().is_empty()
            || !self.ctx.soft_constraints().is_empty()
            || self
                .last_assumptions
                .as_ref()
                .is_some_and(|roots| !roots.is_empty())
        {
            return false;
        }
        let used = self.evaluation_attempt().functional_work_counter();
        let remaining = MAX_FUNCTIONAL_WORK.saturating_sub(used.load(Ordering::Acquire));
        let shared = Arc::clone(&used);
        let Some(_scope) = RecoveryScope::enter_with_work_owner(
            self,
            remaining,
            remaining,
            Box::new(move |work, bytes| {
                work.checked_add(bytes)
                    .is_some_and(|amount| work_counter::debit(&shared, amount))
            }),
        ) else {
            return false;
        };
        let source = self.ctx.source_context_stamp();
        let epoch = self.query_authority_epoch.clone();
        let Ok(roots) = self.independent_gate_query_roots() else {
            return false;
        };
        let Some(variables) = source_scalars(self, &roots) else {
            return false;
        };
        let mut model = self.last_model.take().unwrap_or_else(Model::empty);
        // Re-derive complete data in this decision. An old snapshot cannot be
        // carried into a new source/epoch by ordinary model completion.
        model.functional_arrays = None;
        let complete = (|| -> Option<()> {
            for variable in variables {
                pay_current(1, 0).then_some(())?;
                // The independent evaluator admits scalar payload before
                // copying it, sharing this recovery owner and source work.
                // Existing values precede authored equality proposals and
                // ordinary scalar defaults. Every choice remains model data.
                let value = scalar_value(self, &model, variable, &roots)
                    .or_else(|| self.unconstrained_default_value(self.ctx.terms.sort(variable)))?;
                if !pay_eval_value_copy(&value) || !pay_eval_value_copy(&value) {
                    return None;
                }
                reserve_scalar(&mut model, self.ctx.terms.sort(variable))?;
                Self::insert_completed_value(&self.ctx.terms, &mut model, variable, &value)
                    .then_some(())?;
            }
            self.install_functional_array_candidate(&mut model);
            model.functional_arrays.as_ref()?;
            let view = IndependentModelView::new(self, &model);
            matches!(
                confirm_completed_model(&self.ctx.terms, &view, &roots),
                GateVerdict::ConfirmedSat
            )
            .then_some(())?;
            model.validate_functional_array_source(self).ok()?;
            (source == self.ctx.source_context_stamp()
                && epoch.is_same_epoch(&self.query_authority_epoch)
                && roots == self.independent_gate_query_roots().ok()?
                && pay_current(0, 0))
            .then_some(())
        })()
        .is_some();
        self.last_model = Some(model);
        self.last_model_validated = false;
        if !complete || self.publish_evaluation_stop() || self.solve_deadline.expired() {
            return false;
        }
        self.last_statistics
            .set_int("model_completion.periodic_checked_proposal", 1);
        // This is a proposed verdict. The unchanged primary emission caller
        // still runs every strict/independent gate and mints the SAT certificate.
        true
    }
}
