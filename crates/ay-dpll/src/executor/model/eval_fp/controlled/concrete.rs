// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Preserve lexical overrides, model pins and rounding-mode authority while cloning.

use ay_core::TermData;

use super::super::EvalValue;
use super::*;
use crate::executor::model::{dt_model, eval_guard};

impl Executor {
    pub(super) fn concretize_term_for_fp_eval_controlled(
        &self,
        model: &Model,
        term_id: TermId,
        terms: &mut TermStore,
        cache: &mut HashMap<TermId, TermId>,
        control: &Control<'_>,
    ) -> Result<Option<TermId>, UnknownOrigin> {
        control.phase(Some(terms), FpEvalPhase::Concretize)?;
        let result = (|| {
            if let Some(&cached) = cache.get(&term_id) {
                return Ok(Some(cached));
            }
            let sort = self.ctx.terms.sort(term_id).clone();
            control.poll(Some(terms))?;
            // Exact lexical bindings precede ambient model values, including
            // when the ambient result pin depends on the active binder.
            let override_value = dt_model::active_term_override_lookup(&self.ctx.terms, term_id);
            control.poll(Some(terms))?;
            if let Some(value) = override_value {
                let cloned = self.clone_eval_value_term(terms, &sort, &value, control)?;
                control.poll(Some(terms))?;
                if let Some(concrete) = cloned {
                    cache.insert(term_id, concrete);
                }
                return Ok(cloned);
            }
            if !matches!(sort, Sort::FloatingPoint(..)) {
                let work_before = eval_guard::work_budget_poison();
                let value = self.evaluate_term(model, term_id);
                control.poll(Some(terms))?;
                if eval_guard::work_budget_poison() != work_before {
                    return Err(control.record(UnknownOrigin::DeterministicResourceBudget));
                }
                if !matches!(value, EvalValue::Unknown) {
                    let cloned = self.clone_eval_value_term(terms, &sort, &value, control)?;
                    control.poll(Some(terms))?;
                    if let Some(concrete) = cloned {
                        cache.insert(term_id, concrete);
                    }
                    return Ok(cloned);
                }
            } else {
                let depends = dt_model::term_depends_on_scoped_binding(&self.ctx.terms, term_id);
                control.poll(Some(terms))?;
                if !depends {
                    if let Some(value) = model
                        .fp_model
                        .as_ref()
                        .and_then(|fp| fp.values.get(&term_id))
                    {
                        let cloned = self.clone_fp_value_term(terms, &sort, value, control)?;
                        control.poll(Some(terms))?;
                        if let Some(concrete) = cloned {
                            cache.insert(term_id, concrete);
                        }
                        return Ok(cloned);
                    }
                }
            }
            // An unpinned symbolic mode must not reach FpSolver's legacy RNE
            // fallback. Model-pinned modes were cloned as exact literals above.
            if matches!(&sort, Sort::Uninterpreted(name) if name == "RoundingMode")
                && !crate::executor::rm_domain::is_rm_literal(&self.ctx.terms, term_id)
            {
                return Ok(None);
            }
            control.poll(Some(terms))?;
            let concrete = match self.ctx.terms.get(term_id) {
                TermData::Const(value) => self.clone_constant_term(terms, value),
                // Preserve the inherited unpinned-leaf behavior; this is not
                // a new claim that such a leaf is independently model-pinned.
                TermData::Var(name, _) => Some(terms.mk_var(name.clone(), sort.clone())),
                TermData::App(symbol, args) => {
                    let mut children = Vec::new();
                    for &arg in args {
                        control.poll(Some(terms))?;
                        let Some(child) = self.concretize_term_for_fp_eval_controlled(
                            model, arg, terms, cache, control,
                        )?
                        else {
                            return Ok(None);
                        };
                        children.push(child);
                    }
                    control.poll(Some(terms))?;
                    Some(terms.mk_app(symbol.clone(), children, sort.clone()))
                }
                TermData::Not(arg) => {
                    let Some(child) = self.concretize_term_for_fp_eval_controlled(
                        model, *arg, terms, cache, control,
                    )?
                    else {
                        return Ok(None);
                    };
                    Some(terms.mk_not(child))
                }
                TermData::Ite(condition, then_term, else_term) => {
                    let mut children = Vec::new();
                    for arg in [condition, then_term, else_term] {
                        let Some(child) = self.concretize_term_for_fp_eval_controlled(
                            model, *arg, terms, cache, control,
                        )?
                        else {
                            return Ok(None);
                        };
                        children.push(child);
                    }
                    Some(terms.mk_ite(children[0], children[1], children[2]))
                }
                _ => None,
            };
            control.poll(Some(terms))?;
            if let Some(concrete) = concrete {
                cache.insert(term_id, concrete);
            }
            Ok(concrete)
        })();
        control.poll(Some(terms))?;
        result
    }
}
