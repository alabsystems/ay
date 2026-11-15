// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact constructor-argument producers for array-valued fields.

mod model_leaf;
mod value;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{ArraySort, Sort, TermId};
use ay_frontend::DeclarationKind;
use ay_model_check::ModelValue;

use super::super::rendered_dt_guard::RenderedDatatypeGuard;
use super::super::rendered_dt_limits::SchemaSourceBudget;
use super::{
    charge_work, normalize_array_value, ArrayAccumulator, ExactClass, Model, NormalizedArrayValue,
    SemanticNormalizationBudget, TypedArrayParseBudget, MAX_EXACT_ARRAY_FIELD_TERMS,
};
use crate::executor::Executor;

impl Executor {
    /// Find exact argument sources carried by this stamped datatype class.
    /// Admission uses the same typed materializer as construction and replay;
    /// recognizing a shape alone cannot authorize an unsupported cell value.
    pub(super) fn constructor_array_field_sources(
        &self,
        model: &Model,
        class: &ExactClass,
        ctor: &str,
        field_index: usize,
        field_sort: &Sort,
        authorized_constructor_members: &HashSet<TermId>,
        work: &mut usize,
    ) -> Option<super::ConstructorArrayFieldSources> {
        self.poll_evaluation_stop().ok()?;
        if !charge_work(work, class.members.len()) {
            return None;
        }
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return None;
        }
        let mut parse_budget = TypedArrayParseBudget::new();
        let mut seen = HashSet::default();
        let mut sources = Vec::new();
        let mut unresolved = false;
        for &member in &class.members {
            self.poll_evaluation_stop().ok()?;
            self.ctx.terms.entry_stamp(member)?;
            let TermData::App(symbol @ Symbol::Named(_), args) = self.ctx.terms.get(member) else {
                continue;
            };
            if symbol.name() != ctor {
                continue;
            }
            if self
                .ctx
                .exact_datatype_member_info(symbol.name())
                .map(|info| info.declaration_kind())
                != Some(DeclarationKind::DatatypeConstructor)
            {
                return None;
            }
            let fields = self.ctx.constructor_selector_info(ctor)?;
            if args.len() != fields.len()
                || fields.get(field_index).map(|(_, sort)| sort) != Some(field_sort)
            {
                return None;
            }
            let source = *args.get(field_index)?;
            if self.ctx.terms.entry_stamp(source).is_none()
                || self.ctx.terms.sort(source) != field_sort
            {
                return None;
            }
            // Generated characterization terms are not source constraints.
            // Keep the exact authored/direct-declaration census as authority;
            // merely reaching an argument never promotes its constructor.
            if !authorized_constructor_members.contains(&member) {
                continue;
            }
            if seen.insert(source) {
                if value::materialize(
                    self,
                    model,
                    source,
                    field_sort,
                    &guard,
                    work,
                    &mut parse_budget,
                )
                .is_some()
                {
                    sources.push(source);
                } else {
                    unresolved = true;
                }
                if sources.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                    return None;
                }
            }
        }
        self.poll_evaluation_stop().ok()?;
        sources.sort_unstable_by_key(|term| term.index());
        Some(super::ConstructorArrayFieldSources {
            exact: sources,
            unresolved,
        })
    }

    pub(super) fn merge_constructor_array_sources(
        &self,
        model: &Model,
        sources: &[TermId],
        sort: &ArraySort,
        accumulator: &mut ArrayAccumulator,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> bool {
        for &source in sources {
            let Some(ModelValue::Array(value)) =
                self.exact_constructor_array_source(model, source, sort, work, parse_budget)
            else {
                return false;
            };
            // ModelValue stores are oldest-first; the accumulator consumes
            // authoritative newest-first rows. Move, rather than clone, them.
            let ay_model_check::ArrayValue { default, mut store } = *value;
            store.reverse();
            if !accumulator.merge_interpretation(Some(default), store) {
                return false;
            }
        }
        self.poll_evaluation_stop().is_ok()
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn installed_constructor_array_sources_match(
        &self,
        model: &Model,
        sources: &[TermId],
        sort: &ArraySort,
        installed: &NormalizedArrayValue,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
        semantic_budget: &mut SemanticNormalizationBudget,
    ) -> bool {
        for &source in sources {
            let Some(ModelValue::Array(value)) =
                self.exact_constructor_array_source(model, source, sort, work, parse_budget)
            else {
                return false;
            };
            if normalize_array_value(&value, semantic_budget).as_ref() != Some(installed) {
                return false;
            }
        }
        self.poll_evaluation_stop().is_ok()
    }

    pub(super) fn exact_constructor_array_source(
        &self,
        model: &Model,
        source: TermId,
        sort: &ArraySort,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> Option<ModelValue> {
        self.poll_evaluation_stop().ok()?;
        // The borrowed descriptor must be bounded before its recursive clone
        // and the source interpreter's recursive sort comparisons.
        if !SchemaSourceBudget::new().charge_array_sort(&sort.index_sort, &sort.element_sort) {
            return None;
        }
        self.exact_constructor_source_value(
            model,
            source,
            &Sort::Array(Box::new(sort.clone())),
            work,
            parse_budget,
        )
    }

    pub(in crate::executor::model::datatype_array_fields) fn exact_constructor_source_value(
        &self,
        model: &Model,
        source: TermId,
        sort: &Sort,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> Option<ModelValue> {
        self.poll_evaluation_stop().ok()?;
        let guard = RenderedDatatypeGuard::new(self);
        value::materialize(self, model, source, sort, &guard, work, parse_budget)
    }

    pub(super) fn canonical_array_source_symbol(&self, name: &str) -> bool {
        self.ctx.symbol_info_by_identity(name).is_none_or(|info| {
            self.ctx.effective_declaration_kind(info.declaration_id())
                == Some(DeclarationKind::Theory)
        })
    }
}

#[cfg(test)]
mod tests;
