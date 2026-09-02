// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact constructor-argument producers for array-valued fields.

mod model_leaf;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{ArraySort, Sort, TermId};
use ay_frontend::DeclarationKind;
use ay_model_check::{ArrayValue, ModelValue};

use super::super::dt_construct::eval_to_mv;
use super::{
    charge_work, normalize_array_value, typed_array_value, ArrayAccumulator, ExactClass, Model,
    NormalizedArrayValue, SemanticNormalizationBudget, TypedArrayParseBudget,
    MAX_EXACT_ARRAY_FIELD_TERMS, MAX_TYPED_ARRAY_DEPTH,
};
use crate::executor::Executor;

impl Executor {
    /// Find exact constructor argument terms carried by members of this same
    /// stamped datatype class. Unlike retained selector syntax, a constructor
    /// member semantically fixes every argument, so each matching source must
    /// be reconciled even when no authored selector read exists.
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
        if !charge_work(work, class.members.len()) {
            return None;
        }
        let mut seen = HashSet::default();
        let mut sources = Vec::new();
        let mut unresolved = false;
        for &member in &class.members {
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
            // Constructor applications introduced only by the datatype/array
            // bridge are completion machinery, not source constraints. The
            // exact authored-query/direct-declaration constructor census is
            // the shared producer/reauth boundary. Argument reachability alone
            // is not authority: bridge machinery can generate a constructor
            // around a queried selector application.
            if !authorized_constructor_members.contains(&member) {
                continue;
            }
            if seen.insert(source) {
                if self.exact_constructor_array_source_shape(model, source, field_sort, 0, work) {
                    sources.push(source);
                } else {
                    unresolved = true;
                }
                if sources.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                    return None;
                }
            }
        }
        sources.sort_unstable_by_key(|term| term.index());
        Some(super::ConstructorArrayFieldSources {
            exact: sources,
            unresolved,
        })
    }

    fn exact_constructor_array_source_shape(
        &self,
        model: &Model,
        source: TermId,
        sort: &Sort,
        depth: u32,
        work: &mut usize,
    ) -> bool {
        let mut visited = HashSet::default();
        self.exact_constructor_array_source_shape_inner(
            model,
            source,
            sort,
            depth,
            work,
            &mut visited,
        )
    }

    fn exact_constructor_array_source_shape_inner(
        &self,
        model: &Model,
        source: TermId,
        sort: &Sort,
        depth: u32,
        work: &mut usize,
        visited: &mut HashSet<TermId>,
    ) -> bool {
        if depth > MAX_TYPED_ARRAY_DEPTH
            || self.ctx.terms.entry_stamp(source).is_none()
            || self.ctx.terms.sort(source) != sort
            || !charge_work(work, 1)
            || !visited.insert(source)
        {
            return false;
        }
        let result = match self.ctx.terms.get(source) {
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "const-array"
                    && args.len() == 1
                    && self.canonical_array_source_symbol("const-array") =>
            {
                matches!(sort, Sort::Array(array)
                    if self.ctx.terms.sort(args[0]) == &array.element_sort
                        && eval_to_mv(
                            &self.evaluate_term(model, args[0]),
                            &array.element_sort,
                        ).is_some())
            }
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "store"
                    && args.len() == 3
                    && self.canonical_array_source_symbol("store") =>
            {
                let Sort::Array(array) = sort else {
                    return false;
                };
                self.ctx.terms.sort(args[1]) == &array.index_sort
                    && self.ctx.terms.sort(args[2]) == &array.element_sort
                    && eval_to_mv(&self.evaluate_term(model, args[1]), &array.index_sort).is_some()
                    && eval_to_mv(&self.evaluate_term(model, args[2]), &array.element_sort)
                        .is_some()
                    && self.exact_constructor_array_source_shape_inner(
                        model,
                        args[0],
                        sort,
                        depth + 1,
                        work,
                        visited,
                    )
            }
            TermData::Let(bindings, body) if bindings.is_empty() => self
                .exact_constructor_array_source_shape_inner(
                    model,
                    *body,
                    sort,
                    depth + 1,
                    work,
                    visited,
                ),
            TermData::Ite(condition, then_term, else_term) => {
                let branch = match self.evaluate_term(model, *condition) {
                    super::super::EvalValue::Bool(true) => *then_term,
                    super::super::EvalValue::Bool(false) => *else_term,
                    _ => return false,
                };
                self.exact_constructor_array_source_shape_inner(
                    model,
                    branch,
                    sort,
                    depth + 1,
                    work,
                    visited,
                )
            }
            TermData::Var(_, _) => {
                match self.authored_array_definition(source, sort, visited, work) {
                    super::AuthoredArrayDefinition::Exact { value, .. } => self
                        .exact_constructor_array_source_shape_inner(
                            model,
                            value,
                            sort,
                            depth + 1,
                            work,
                            visited,
                        ),
                    super::AuthoredArrayDefinition::Rejected => false,
                    super::AuthoredArrayDefinition::Absent => {
                        let has_row = self.complete_array_model_leaf_shape(model, source, sort);
                        let definition = if has_row {
                            self.unique_array_constructor_definition_excluding(source, visited)
                        } else {
                            self.array_variable_definition_excluding(source, visited)
                        };
                        definition.map_or(has_row, |definition| {
                            self.exact_constructor_array_source_shape_inner(
                                model,
                                definition,
                                sort,
                                depth + 1,
                                work,
                                visited,
                            )
                        })
                    }
                }
            }
            _ => self.complete_array_model_leaf_shape(model, source, sort),
        };
        visited.remove(&source);
        result
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
            let Some(value) =
                self.exact_constructor_array_source(model, source, sort, work, parse_budget)
            else {
                return false;
            };
            let ModelValue::Array(value) = value else {
                return false;
            };
            // ModelValue stores are oldest-first; ArrayAccumulator consumes an
            // authoritative newest-first row sequence.
            let stores = value.store.iter().rev().cloned().collect();
            if !accumulator.merge_interpretation(Some(value.default.clone()), stores) {
                return false;
            }
        }
        true
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
        true
    }

    pub(super) fn exact_constructor_array_source(
        &self,
        model: &Model,
        source: TermId,
        sort: &ArraySort,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> Option<ModelValue> {
        let mut visited = HashSet::default();
        let value = self.exact_constructor_array_source_inner(
            model,
            source,
            sort,
            0,
            work,
            parse_budget,
            &mut visited,
        )?;
        let ModelValue::Array(array) = &value else {
            return None;
        };
        (typed_array_value(array, sort) && parse_budget.charge_value(&value)).then_some(value)
    }

    fn exact_constructor_array_source_inner(
        &self,
        model: &Model,
        source: TermId,
        sort: &ArraySort,
        depth: u32,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
        visited: &mut HashSet<TermId>,
    ) -> Option<ModelValue> {
        if depth > MAX_TYPED_ARRAY_DEPTH
            || self.ctx.terms.entry_stamp(source).is_none()
            || self.ctx.terms.sort(source) != &Sort::Array(Box::new(sort.clone()))
            || !charge_work(work, 1)
            || !visited.insert(source)
        {
            return None;
        }
        enum SourceNode {
            Store(TermId, TermId, TermId),
            Const(TermId),
            Alias(TermId),
            Ite(TermId, TermId, TermId),
            ModelLeaf,
        }
        let node = match self.ctx.terms.get(source) {
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "store"
                    && args.len() == 3
                    && self.canonical_array_source_symbol("store") =>
            {
                SourceNode::Store(args[0], args[1], args[2])
            }
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "const-array"
                    && args.len() == 1
                    && self.canonical_array_source_symbol("const-array") =>
            {
                SourceNode::Const(args[0])
            }
            TermData::Let(bindings, body) if bindings.is_empty() => SourceNode::Alias(*body),
            TermData::Ite(condition, then_term, else_term) => {
                SourceNode::Ite(*condition, *then_term, *else_term)
            }
            TermData::Var(_, _) => {
                let declared = Sort::Array(Box::new(sort.clone()));
                match self.authored_array_definition(source, &declared, visited, work) {
                    super::AuthoredArrayDefinition::Exact { value, .. } => SourceNode::Alias(value),
                    super::AuthoredArrayDefinition::Rejected => return None,
                    super::AuthoredArrayDefinition::Absent => {
                        let has_row =
                            self.complete_array_model_leaf_shape(model, source, &declared);
                        let definition = if has_row {
                            self.unique_array_constructor_definition_excluding(source, visited)
                        } else {
                            self.array_variable_definition_excluding(source, visited)
                        };
                        match definition {
                            Some(definition) => SourceNode::Alias(definition),
                            None if has_row => SourceNode::ModelLeaf,
                            None => return None,
                        }
                    }
                }
            }
            _ if self.complete_array_model_leaf_shape(
                model,
                source,
                &Sort::Array(Box::new(sort.clone())),
            ) =>
            {
                SourceNode::ModelLeaf
            }
            _ => return None,
        };
        let result = match node {
            SourceNode::Store(base, key, cell) => {
                if self.ctx.terms.sort(key) != &sort.index_sort
                    || self.ctx.terms.sort(cell) != &sort.element_sort
                {
                    return None;
                }
                let ModelValue::Array(mut value) = self.exact_constructor_array_source_inner(
                    model,
                    base,
                    sort,
                    depth + 1,
                    work,
                    parse_budget,
                    visited,
                )?
                else {
                    return None;
                };
                let key = eval_to_mv(&self.evaluate_term(model, key), &sort.index_sort)?;
                let cell = eval_to_mv(&self.evaluate_term(model, cell), &sort.element_sort)?;
                if !parse_budget.charge_value(&key) || !parse_budget.charge_value(&cell) {
                    return None;
                }
                value.store.push((key, cell));
                Some(ModelValue::Array(value))
            }
            SourceNode::Const(default) => {
                if self.ctx.terms.sort(default) != &sort.element_sort {
                    return None;
                }
                let default = eval_to_mv(&self.evaluate_term(model, default), &sort.element_sort)?;
                parse_budget
                    .charge_value(&default)
                    .then_some(ModelValue::Array(Box::new(ArrayValue {
                        default,
                        store: Vec::new(),
                    })))
            }
            SourceNode::Alias(body) => self.exact_constructor_array_source_inner(
                model,
                body,
                sort,
                depth + 1,
                work,
                parse_budget,
                visited,
            ),
            SourceNode::Ite(condition, then_term, else_term) => {
                let branch = match self.evaluate_term(model, condition) {
                    super::super::EvalValue::Bool(true) => then_term,
                    super::super::EvalValue::Bool(false) => else_term,
                    _ => return None,
                };
                self.exact_constructor_array_source_inner(
                    model,
                    branch,
                    sort,
                    depth + 1,
                    work,
                    parse_budget,
                    visited,
                )
            }
            SourceNode::ModelLeaf => {
                self.exact_array_model_leaf_value(model, source, sort, work, parse_budget)
            }
        };
        visited.remove(&source);
        result
    }

    pub(super) fn canonical_array_source_symbol(&self, name: &str) -> bool {
        self.ctx.symbol_info_by_identity(name).is_none_or(|info| {
            self.ctx.effective_declaration_kind(info.declaration_id())
                == Some(DeclarationKind::Theory)
        })
    }
}
