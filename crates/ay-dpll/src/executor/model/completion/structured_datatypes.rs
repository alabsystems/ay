// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Install one coherent assignment already present in structured EUF values.
//! Values, observed selector projections and tester results are staged together;
//! the ordinary strict and independent model gates still decide acceptance.

use super::super::eval_dt_constructor::ConstructorBudget;
use super::*;
use ay_core::{Symbol, TermData, TermId};
use ay_frontend::DeclarationKind;
use ay_model_check::ModelValue;

const MAX_SCOPE: usize = 16_384;
const MAX_ARENA: usize = 65_536;
const MAX_ROUNDS: usize = 64;
const MAX_STEPS: usize = 262_144;
const MAX_RAW_BYTES: usize = 1_048_576;

type StagedValue = (TermId, ModelValue, EvalValue);

impl Executor {
    pub(in crate::executor::model) fn complete_structured_datatype_values(
        &self,
        model: &mut Model,
        extra_roots: &[TermId],
    ) -> usize {
        if self.ctx.terms.len() > MAX_ARENA
            || self.dt_theory_model.is_some()
            || self.dt_lazy_splits.is_some()
            || self.dt_egraph_available(model)
            || super::super::scoped_term_evaluation_override_active()
            || model.residual_arrays.is_some()
            || !model.certified_const_interp_entries().is_empty()
            || !model.certified_total_ufs.by_symbol.is_empty()
            || !model.certified_total_ufs.ground_pins.is_empty()
            || model.projection_ufs.has_interpretations()
            || !model.formula_neutral_function_default_entries().is_empty()
        {
            return 0;
        }
        let Some(scope) = self.structured_datatype_scope(extra_roots) else {
            return 0;
        };
        let mut datatypes = HashSet::default();
        for (name, _) in self.ctx.datatype_iter() {
            if name.len() > 256 || datatypes.len() >= MAX_SCOPE {
                return 0;
            }
            datatypes.insert(name);
        }
        let mut budget = ConstructorBudget::default();
        let mut values = HashMap::default();
        for &term in &scope {
            let TermData::Var(name, _) = self.ctx.terms.get(term) else {
                continue;
            };
            if self.ctx.is_constructor(name).is_some() {
                continue;
            }
            let sort = self.ctx.terms.sort(term);
            let Sort::Uninterpreted(name) = sort else {
                continue;
            };
            if !datatypes.contains(name.as_str()) {
                continue;
            }
            let value = match self.structured_datatype_seed(model, term, sort, &mut budget) {
                Ok(Some(value)) => value,
                Ok(None) => continue,
                Err(()) => return 0,
            };
            values.insert(term, value);
        }
        if values.is_empty() {
            return 0;
        }
        if !self.close_structured_datatype_observations(&scope, &mut values, &mut budget) {
            return 0;
        }
        let Some(staged) = self.stage_structured_datatype_values(model, values, &mut budget) else {
            return 0;
        };
        if staged.is_empty() || self.poll_evaluation_stop().is_err() {
            return 0;
        }
        model.revoke_all_quantified_model_seals();
        super::super::eval_memo_clear();
        let count = staged.len();
        for (term, value, pin) in staged {
            if matches!(&value, ModelValue::Datatype { .. }) {
                model.dt_ground.entry(term).or_insert(value);
            }
            model.dt_pins.entry(term).or_insert(pin);
        }
        count
    }

    /// Prefer this variable's structured raw value. A committed typed ground
    /// value may complete its projections when raw text is absent or opaque.
    /// Invalid structured raw text still refuses instead of hiding a conflict.
    fn structured_datatype_seed(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
        budget: &mut ConstructorBudget,
    ) -> Result<Option<ModelValue>, ()> {
        if let Some(text) = model
            .euf_model
            .as_ref()
            .and_then(|euf| euf.term_values.get(&term))
        {
            if text.len() > MAX_RAW_BYTES {
                return Err(());
            }
            if text.trim_start().starts_with('(') {
                return self
                    .read_structured_euf_datatype_value(model, term, sort, 0, budget)
                    .map(Some)
                    .ok_or(());
            }
        }
        let Some(value) = model.dt_ground.get(&term) else {
            return Ok(None);
        };
        self.check_constructor_value(value, sort, 0, budget)
            .ok_or(())?;
        Ok(Some(value.clone()))
    }

    /// Include current generated observations as well as authored roots. The
    /// term arena itself is not a root: stale popped applications stay out.
    fn structured_datatype_scope(&self, extra_roots: &[TermId]) -> Option<Vec<TermId>> {
        // This is the common authored/current/assumption/pin root union,
        // bounded before allocation. Generated current assertions contribute
        // observations even when full datatype construction excludes them.
        let authored = self
            .independent_gate_authored_assertions
            .as_deref()
            .unwrap_or(self.ctx.assertions.as_slice());
        let assumptions = self.last_assumptions.as_deref().unwrap_or(&[]);
        let root_slices = [
            authored,
            assumptions,
            self.ctx.assertions.as_slice(),
            extra_roots,
            self.lane_model_pin_roots.as_slice(),
        ];
        let count = root_slices
            .iter()
            .try_fold(0usize, |count, roots| count.checked_add(roots.len()))?;
        if count > MAX_SCOPE {
            return None;
        }
        let mut stack = Vec::with_capacity(count);
        for roots in root_slices {
            stack.extend_from_slice(roots);
        }
        let mut seen = HashSet::default();
        while let Some(term) = stack.pop() {
            self.ctx.terms.entry_stamp(term)?;
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_SCOPE || self.evaluation_stop_origin().is_some() {
                return None;
            }
            if matches!(
                self.ctx.terms.get(term),
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
            ) {
                continue;
            }
            let children = self.ctx.terms.children(term);
            if stack.len().checked_add(children.len())? > MAX_SCOPE {
                return None;
            }
            stack.extend(children);
        }
        let mut scope: Vec<_> = seen.into_iter().collect();
        scope.sort_by_key(|term| term.index());
        Some(scope)
    }

    fn close_structured_datatype_observations(
        &self,
        scope: &[TermId],
        values: &mut HashMap<TermId, ModelValue>,
        budget: &mut ConstructorBudget,
    ) -> bool {
        let mut steps = 0usize;
        for _ in 0..MAX_ROUNDS {
            let mut changed = false;
            for &term in scope {
                steps += 1;
                if steps > MAX_STEPS || self.evaluation_stop_origin().is_some() {
                    return false;
                }
                if values.contains_key(&term) {
                    continue;
                }
                if let Some(value) = self.structured_datatype_observation(term, values, budget) {
                    values.insert(term, value);
                    changed = true;
                }
                if budget.exhausted() {
                    return false;
                }
            }
            if !changed {
                return true;
            }
        }
        false
    }

    /// Only exact observed selectors/testers of an owned value are projected.
    /// A selector of a different constructor remains unspecified and untouched.
    fn structured_datatype_observation(
        &self,
        term: TermId,
        values: &HashMap<TermId, ModelValue>,
        budget: &mut ConstructorBudget,
    ) -> Option<ModelValue> {
        let TermData::App(Symbol::Named(name), arguments) = self.ctx.terms.get(term) else {
            return None;
        };
        if arguments.len() != 1
            || name.len() > 256
            || !self.ctx.is_live_datatype_member_identity(name)
        {
            return None;
        }
        let argument = arguments[0];
        let ModelValue::Datatype { ctor, args } = values.get(&argument)? else {
            return None;
        };
        let info = self.ctx.exact_datatype_member_info(name)?;
        if info.arg_sorts.len() != 1
            || info.arg_sorts.first() != Some(self.ctx.terms.sort(argument))
            || &info.sort != self.ctx.terms.sort(term)
        {
            return None;
        }
        let value = match info.declaration_kind() {
            DeclarationKind::DatatypeSelector => {
                let fields = self.ctx.constructor_selector_info(ctor)?;
                let index = fields.iter().position(|(field, _)| field == name)?;
                let value = args.get(index)?;
                self.check_constructor_value(value, self.ctx.terms.sort(term), 0, budget)?;
                value.clone()
            }
            DeclarationKind::DatatypeTester => {
                let tested = name.strip_prefix("is-")?;
                let (tested_sort, _) = self.ctx.is_constructor(tested)?;
                let (assigned_sort, _) = self.ctx.is_constructor(ctor)?;
                if tested_sort != assigned_sort {
                    return None;
                }
                budget.charge(5, 0)?;
                ModelValue::Bool(tested == ctor)
            }
            _ => return None,
        };
        Some(value)
    }

    fn stage_structured_datatype_values(
        &self,
        model: &Model,
        values: HashMap<TermId, ModelValue>,
        budget: &mut ConstructorBudget,
    ) -> Option<Vec<StagedValue>> {
        let mut staged = Vec::new();
        for (term, value) in values {
            let sort = self.ctx.terms.sort(term);
            self.check_constructor_value(&value, sort, 0, budget)?;
            let pin = super::super::dt_construct::mv_to_eval(&value);
            if let Some(old) = model.dt_ground.get(&term) {
                self.check_constructor_value(old, sort, 0, budget)?;
                if super::super::dt_construct::mv_to_eval(old) != pin {
                    return None;
                }
            }
            for old in model
                .dt_pins
                .get(&term)
                .into_iter()
                .chain(model.completed_values.get(&term))
            {
                if old != &pin {
                    return None;
                }
            }
            if !model.dt_pins.contains_key(&term)
                || (matches!(&value, ModelValue::Datatype { .. })
                    && !model.dt_ground.contains_key(&term))
            {
                staged.push((term, value, pin));
            }
        }
        staged.sort_by_key(|(term, _, _)| term.index());
        Some(staged)
    }
}
