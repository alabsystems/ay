// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Selector observations and extracted array-field interpretations.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{ArraySort, Sort, TermId};
use ay_model_check::ModelValue;

use super::super::dt_construct::eval_to_mv;
use super::{
    charge_work, normalize_array_value, typed_array_value, ArrayAccumulator, ExactClass, Model,
    SemanticNormalizationBudget, TypedArrayParseBudget, MAX_EXACT_ARRAY_FIELD_TERMS,
};
use crate::executor::Executor;

impl Executor {
    pub(super) fn reconstruct_array_field(
        &self,
        model: &Model,
        field_sort: &Sort,
        apps: Vec<TermId>,
        sources: Vec<TermId>,
        required_terms: &HashSet<TermId>,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> Option<ModelValue> {
        let Sort::Array(array_sort) = field_sort else {
            return None;
        };
        if apps.is_empty() && sources.is_empty() {
            return None;
        }
        let mut accumulator = ArrayAccumulator::default();
        if !self.merge_constructor_array_sources(
            model,
            &sources,
            array_sort,
            &mut accumulator,
            work,
            parse_budget,
        ) {
            return None;
        }
        for app in apps {
            if model
                .array_model
                .as_ref()
                .is_some_and(|arrays| arrays.read_conflicted.contains(&app))
                || !self.merge_active_field_reads(
                    model,
                    app,
                    array_sort,
                    &mut accumulator,
                    required_terms,
                    work,
                    parse_budget,
                )
                || !self.merge_extracted_field_interp(
                    model,
                    app,
                    array_sort,
                    &mut accumulator,
                    work,
                    parse_budget,
                )
            {
                return None;
            }
        }
        accumulator.finish(&array_sort.element_sort)
    }

    pub(super) fn validated_unobserved_array_candidate(
        &self,
        candidate: Option<&ModelValue>,
        field_sort: &Sort,
        parse_budget: &mut TypedArrayParseBudget,
        semantic_budget: &mut SemanticNormalizationBudget,
    ) -> Option<ModelValue> {
        let candidate = candidate?;
        let (ModelValue::Array(value), Sort::Array(sort)) = (candidate, field_sort) else {
            return None;
        };
        if !parse_budget.charge_value(candidate)
            || !typed_array_value(value, sort)
            || normalize_array_value(value, semantic_budget).is_none()
        {
            return None;
        }
        Some(candidate.clone())
    }

    pub(super) fn selector_apps(
        &self,
        model: &Model,
        class: &ExactClass,
        selector: &str,
        field_sort: &Sort,
        required_terms: &HashSet<TermId>,
        work: &mut usize,
    ) -> Option<Vec<TermId>> {
        let euf = model.euf_model.as_ref()?;
        if !charge_work(work, required_terms.len()) {
            return None;
        }
        let mut apps: Vec<_> = required_terms
            .iter()
            .copied()
            .filter(|&app| {
                let TermData::App(symbol, args) = self.ctx.terms.get(app) else {
                    return false;
                };
                matches!(symbol, Symbol::Named(_))
                    && symbol.name() == selector
                    && args.len() == 1
                    && required_terms.contains(&app)
                    && self.ctx.terms.sort(app) == field_sort
                    && self.ctx.terms.sort(args[0]) == &class.cell_sort
                    && euf.term_values.get(&args[0]) == Some(&class.carrier)
                    && self.exact_datatype_selector(symbol.name())
            })
            .collect();
        apps.sort_by_key(|term| term.index());
        (apps.len() <= MAX_EXACT_ARRAY_FIELD_TERMS).then_some(apps)
    }

    fn merge_active_field_reads(
        &self,
        model: &Model,
        app: TermId,
        sort: &ArraySort,
        accumulator: &mut ArrayAccumulator,
        required_terms: &HashSet<TermId>,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> bool {
        let reads = self.exact_array_field_reads(app, required_terms);
        if !charge_work(work, reads.len()) {
            return false;
        }
        for read in reads {
            let TermData::App(symbol, args) = self.ctx.terms.get(read) else {
                return false;
            };
            if !matches!(symbol, Symbol::Named(_))
                || symbol.name() != "select"
                || args.len() != 2
                || args[0] != app
                || self.ctx.terms.sort(args[1]) != &sort.index_sort
                || self.ctx.terms.sort(read) != &sort.element_sort
            {
                return false;
            }
            let Some(key) = eval_to_mv(&self.evaluate_term(model, args[1]), &sort.index_sort)
            else {
                return false;
            };
            let Some(value) = eval_to_mv(&self.evaluate_term(model, read), &sort.element_sort)
            else {
                return false;
            };
            if !parse_budget.charge_value(&key)
                || !parse_budget.charge_value(&value)
                || !accumulator.merge_point(key, value)
            {
                return false;
            }
        }
        true
    }

    /// Return only canonical, well-sorted array reads whose array operand is
    /// `app`. In particular, a whole-array equality mentioning `app` is not a
    /// selector observation, regardless of its operand order.
    pub(super) fn exact_array_field_reads(
        &self,
        app: TermId,
        required_terms: &HashSet<TermId>,
    ) -> Vec<TermId> {
        required_terms
            .iter()
            .copied()
            .filter(|&read| {
                self.exact_cegar_select_parts(read)
                    .is_some_and(|(array, _)| array == app)
            })
            .collect()
    }

    fn merge_extracted_field_interp(
        &self,
        model: &Model,
        app: TermId,
        sort: &ArraySort,
        accumulator: &mut ArrayAccumulator,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> bool {
        let Some(interp) = model
            .array_model
            .as_ref()
            .and_then(|arrays| arrays.array_values.get(&app))
        else {
            return true;
        };
        if !charge_work(work, interp.stores.len().saturating_add(1)) {
            return false;
        }
        let default = interp
            .default
            .as_deref()
            .and_then(|text| self.typed_scalar_text(text, &sort.element_sort, parse_budget));
        let mut stores = Vec::with_capacity(interp.stores.len());
        for (key, value) in &interp.stores {
            let (Some(key), Some(value)) = (
                self.typed_scalar_text(key, &sort.index_sort, parse_budget),
                self.typed_scalar_text(value, &sort.element_sort, parse_budget),
            ) else {
                return false;
            };
            stores.push((key, value));
        }
        accumulator.merge_interpretation(default, stores)
    }

    pub(super) fn typed_scalar_text(
        &self,
        text: &str,
        sort: &Sort,
        budget: &mut TypedArrayParseBudget,
    ) -> Option<ModelValue> {
        if !budget.charge_text(text) {
            return None;
        }
        let value = eval_to_mv(
            &self.parse_model_value_string(text, &Some(sort.clone())),
            sort,
        )?;
        budget.charge_value(&value).then_some(value)
    }
}
