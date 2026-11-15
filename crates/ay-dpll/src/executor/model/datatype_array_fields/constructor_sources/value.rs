// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One typed source interpreter for admission, construction, and reauthentication.
//! Datatype values come from exact constructor syntax, never completion pins or
//! printed opaque values. Every recursive aggregate shares the same limits.

use super::super::super::dt_construct::eval_to_mv;
use super::super::super::rendered_dt_limits::SchemaSourceBudget;
use super::super::MAX_TYPED_ARRAY_DEPTH;
use super::*;
use ay_model_check::ArrayValue;

pub(super) fn materialize(
    exec: &Executor,
    model: &Model,
    source: TermId,
    sort: &Sort,
    guard: &RenderedDatatypeGuard,
    work: &mut usize,
    parse_budget: &mut TypedArrayParseBudget,
) -> Option<ModelValue> {
    exec.poll_evaluation_stop().ok()?;
    if !guard.is_bounded() || !SchemaSourceBudget::new().charge_sort(sort) {
        return None;
    }
    let value = SourceValue {
        exec,
        model,
        guard,
        work,
        parse_budget,
        visited: HashSet::default(),
    }
    .eval(source, sort, 0)?;
    if !super::super::typed_datatype_array_value(&value, sort, guard) {
        return None;
    }
    exec.poll_evaluation_stop().ok()?;
    Some(value)
}

struct SourceValue<'a, 'b> {
    exec: &'a Executor,
    model: &'a Model,
    guard: &'a RenderedDatatypeGuard,
    work: &'b mut usize,
    parse_budget: &'b mut TypedArrayParseBudget,
    visited: HashSet<TermId>,
}

impl SourceValue<'_, '_> {
    fn eval(&mut self, source: TermId, sort: &Sort, depth: u32) -> Option<ModelValue> {
        self.exec.poll_evaluation_stop().ok()?;
        if depth > MAX_TYPED_ARRAY_DEPTH
            || !charge_work(self.work, 1)
            || self.exec.ctx.terms.entry_stamp(source).is_none()
            || self.exec.ctx.terms.sort(source) != sort
            || !self.visited.insert(source)
        {
            return None;
        }
        let value = self.node(source, sort, depth);
        self.visited.remove(&source);
        self.exec.poll_evaluation_stop().ok()?;
        let value = value?;
        // Validate scalar leaves before they can participate in a select-key
        // comparison. In particular malformed rational denominators must not
        // reach Ratio equality ahead of the final aggregate type check.
        if !matches!(value, ModelValue::Array(_) | ModelValue::Datatype { .. })
            && !super::super::typed_datatype_array_value(&value, sort, self.guard)
        {
            return None;
        }
        self.parse_budget.charge_value(&value).then_some(value)
    }

    fn node(&mut self, source: TermId, sort: &Sort, depth: u32) -> Option<ModelValue> {
        let exec = self.exec;
        // Keep aggregate wrappers structural and typed. An unselected branch
        // supplies no value; a missing condition never authorizes a default.
        if matches!(sort, Sort::Array(_)) || self.guard.is_registered(sort) {
            if let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(source) {
                if name == "select" {
                    return self.select(args, sort, depth);
                }
            }
            match exec.ctx.terms.get(source) {
                TermData::Let(bindings, body) if bindings.is_empty() => {
                    return self.eval(*body, sort, depth + 1);
                }
                TermData::Ite(condition, yes, no) => {
                    if !self.typed(*condition, &Sort::Bool)
                        || !self.typed(*yes, sort)
                        || !self.typed(*no, sort)
                    {
                        return None;
                    }
                    let branch = match exec.evaluate_term(self.model, *condition) {
                        super::super::super::EvalValue::Bool(true) => *yes,
                        super::super::super::EvalValue::Bool(false) => *no,
                        _ => return None,
                    };
                    return self.eval(branch, sort, depth + 1);
                }
                _ => {}
            }
        }
        match sort {
            Sort::Array(array) => self.array(source, array, depth),
            _ if self.guard.is_registered(sort) => self.constructor(source, sort, depth),
            _ => eval_to_mv(&exec.evaluate_term(self.model, source), sort),
        }
    }

    fn typed(&self, term: TermId, sort: &Sort) -> bool {
        self.exec.ctx.terms.entry_stamp(term).is_some() && self.exec.ctx.terms.sort(term) == sort
    }

    fn select(&mut self, args: &[TermId], sort: &Sort, depth: u32) -> Option<ModelValue> {
        let exec = self.exec;
        let [base, index] = args else {
            return None;
        };
        if !exec.canonical_array_source_symbol("select") {
            return None;
        }
        exec.ctx.terms.entry_stamp(*base)?;
        let base_sort = exec.ctx.terms.sort(*base);
        let Sort::Array(array_sort) = base_sort else {
            return None;
        };
        if &array_sort.element_sort != sort || !self.typed(*index, &array_sort.index_sort) {
            return None;
        }
        let key = self.eval(*index, &array_sort.index_sort, depth + 1)?;
        // W6 admits scalar keys. Structural equality is exact on this fragment;
        // never use representation equality for an array/datatype key.
        if !matches!(
            key,
            ModelValue::Bool(_)
                | ModelValue::Int(_)
                | ModelValue::Real(_)
                | ModelValue::BitVec { .. }
                | ModelValue::Str(_)
        ) {
            return None;
        }
        let ModelValue::Array(array) = self.eval(*base, base_sort, depth + 1)? else {
            return None;
        };
        if !charge_work(self.work, array.store.len()) {
            return None;
        }
        let ArrayValue { default, store } = *array;
        Some(
            store
                .into_iter()
                .rev()
                .find_map(|(candidate, value)| same_scalar(&candidate, &key).then_some(value))
                .unwrap_or(default),
        )
    }

    fn constructor(&mut self, source: TermId, sort: &Sort, depth: u32) -> Option<ModelValue> {
        let exec = self.exec;
        let guard = self.guard;
        let (name, args) = match exec.ctx.terms.get(source) {
            TermData::App(Symbol::Named(name), args) => (name.as_str(), args.as_slice()),
            TermData::Var(name, _) => (name.as_str(), &[][..]),
            _ => return None,
        };
        let (identity, fields) = guard.constructor(sort, name)?;
        let info = exec.ctx.exact_datatype_member_info(name)?;
        if identity != name
            || info.declaration_kind() != DeclarationKind::DatatypeConstructor
            || &info.sort != sort
            || info.arg_sorts.as_slice() != fields
            || args.len() != fields.len()
            || !charge_work(self.work, args.len().checked_add(name.len())?)
            || !self.parse_budget.charge_text(name)
        {
            return None;
        }
        let mut values = Vec::new();
        values.try_reserve_exact(args.len()).ok()?;
        for (&arg, field) in args.iter().zip(fields) {
            values.push(self.eval(arg, field, depth + 1)?);
        }
        Some(ModelValue::Datatype {
            ctor: identity.to_string(),
            args: values,
        })
    }

    fn array(&mut self, source: TermId, sort: &ArraySort, depth: u32) -> Option<ModelValue> {
        let exec = self.exec;
        match exec.ctx.terms.get(source) {
            TermData::App(Symbol::Named(name), args)
                if name == "const-array"
                    && args.len() == 1
                    && exec.canonical_array_source_symbol("const-array") =>
            {
                let default = self.eval(args[0], &sort.element_sort, depth + 1)?;
                Some(ModelValue::Array(Box::new(ArrayValue {
                    default,
                    store: Vec::new(),
                })))
            }
            TermData::App(Symbol::Named(name), args)
                if name == "store"
                    && args.len() == 3
                    && exec.canonical_array_source_symbol("store") =>
            {
                let declared = exec.ctx.terms.sort(source);
                let ModelValue::Array(mut value) = self.eval(args[0], declared, depth + 1)? else {
                    return None;
                };
                let key = self.eval(args[1], &sort.index_sort, depth + 1)?;
                let cell = self.eval(args[2], &sort.element_sort, depth + 1)?;
                if !charge_work(self.work, 1) {
                    return None;
                }
                value.store.try_reserve(1).ok()?;
                value.store.push((key, cell));
                Some(ModelValue::Array(value))
            }
            TermData::Var(_, _) => self.array_variable(source, sort, depth),
            _ => self.model_array(source, sort),
        }
    }

    fn array_variable(
        &mut self,
        source: TermId,
        sort: &ArraySort,
        depth: u32,
    ) -> Option<ModelValue> {
        let exec = self.exec;
        let declared = exec.ctx.terms.sort(source);
        let definition =
            match exec.authored_array_definition(source, declared, &self.visited, self.work) {
                super::super::AuthoredArrayDefinition::Exact { value, .. } => Some(value),
                super::super::AuthoredArrayDefinition::Rejected => return None,
                super::super::AuthoredArrayDefinition::Absent => {
                    if exec.complete_array_model_leaf_shape(self.model, source, declared) {
                        exec.unique_array_constructor_definition_excluding(source, &self.visited)
                    } else {
                        exec.array_variable_definition_excluding(source, &self.visited)
                    }
                }
            };
        match definition {
            Some(definition) => self.eval(definition, declared, depth + 1),
            None => self.model_array(source, sort),
        }
    }

    fn model_array(&mut self, source: TermId, sort: &ArraySort) -> Option<ModelValue> {
        // Retain the complete typed model-leaf route. It parses only bounded,
        // sort-checked concrete values, never opaque datatype carrier tokens.
        self.exec.exact_array_model_leaf_value(
            self.model,
            source,
            sort,
            self.guard,
            self.work,
            self.parse_budget,
        )
    }
}

fn same_scalar(left: &ModelValue, right: &ModelValue) -> bool {
    match (left, right) {
        (ModelValue::Bool(left), ModelValue::Bool(right)) => left == right,
        (ModelValue::Int(left), ModelValue::Int(right)) => left == right,
        (ModelValue::Real(left), ModelValue::Real(right)) => left == right,
        (ModelValue::Str(left), ModelValue::Str(right)) => left == right,
        (
            ModelValue::BitVec {
                value: left,
                width: lw,
            },
            ModelValue::BitVec {
                value: right,
                width: rw,
            },
        ) => lw == rw && left == right,
        _ => false,
    }
}
