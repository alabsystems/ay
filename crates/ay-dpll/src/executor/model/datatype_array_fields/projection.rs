// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only projection of exact, otherwise-unobserved array fields.

use std::cell::Cell;

use ay_core::term::{Symbol, TermData};
use ay_core::{ArraySort, Sort, TermId};
use ay_model_check::{ArrayValue, ModelValue};

use super::super::dt_construct::{dt_canonical_string, mv_to_eval};
use super::super::rendered_dt_guard::RenderedDatatypeGuard;
use super::super::{EvalValue, Model};
use super::{normalize_datatype_array_value, SemanticNormalizationBudget};
use crate::executor::Executor;

thread_local! {
    /// Certificate reauthentication may itself evaluate observed array reads.
    /// A nested projection therefore declines instead of recursively trying to
    /// authenticate the same inventory.
    static PROJECTING_UNOBSERVED_FIELD: Cell<bool> = const { Cell::new(false) };
}

struct ProjectionGuard;

impl ProjectionGuard {
    fn enter() -> Option<Self> {
        PROJECTING_UNOBSERVED_FIELD.with(|active| {
            if active.replace(true) {
                None
            } else {
                Some(Self)
            }
        })
    }
}

impl Drop for ProjectionGuard {
    fn drop(&mut self) {
        PROJECTING_UNOBSERVED_FIELD.with(|active| active.set(false));
    }
}

impl Executor {
    /// Whether raw result-local provenance claims this exact selector field was
    /// unobserved. This never grants a value; it only prevents a stale
    /// ArrayModel row from bypassing failed certificate reauthentication.
    pub(in crate::executor::model) fn unobserved_array_field_authority_claim(
        &self,
        model: &Model,
        field_app: TermId,
    ) -> bool {
        let TermData::App(field_symbol @ Symbol::Named(_), field_args) =
            self.ctx.terms.get(field_app)
        else {
            return false;
        };
        if field_args.len() != 1 || !self.exact_datatype_selector(field_symbol.name()) {
            return false;
        }
        let cell = field_args[0];
        let cell_sort = self.ctx.terms.sort(cell);
        let field_sort = self.ctx.terms.sort(field_app);
        let guard = RenderedDatatypeGuard::new(self);
        let Some(name) = guard.datatype_name(cell_sort) else {
            return false;
        };
        let Some(constructors) = self.ctx.datatype_constructors(name) else {
            return false;
        };
        let [ctor] = constructors else {
            return false;
        };
        let Some(fields) = self.ctx.constructor_selector_info(ctor) else {
            return false;
        };
        let mut matching = fields
            .iter()
            .enumerate()
            .filter(|(_, (selector, sort))| selector == field_symbol.name() && sort == field_sort);
        let Some((index, _)) = matching.next() else {
            return false;
        };
        if matching.next().is_some() {
            return false;
        }
        // A newly materialized select of an outer array is not necessarily a
        // stamped member of the producer-time class. Projection can still
        // resolve it through the class carrier below. Treat the same narrow
        // shape as a raw authority claim here: if reauthentication is stale,
        // a retained ArrayModel row must not bypass the failed certificate.
        // This predicate grants no value, so conservatively matching another
        // class of the same exact datatype sort can only fail closed.
        let fresh_outer_select = self.datatype_array_outer_select_cell(cell, cell_sort);
        model.dt_array_field_classes.iter().any(|authority| {
            authority.cell_sort == *cell_sort
                && (authority.members.contains_key(&cell) || fresh_outer_select)
                && authority.unobserved_fields.contains(&index)
        })
    }

    /// Return an exact array field only when the queried selector application
    /// is a stamped member of a fully reauthenticated W6 class and that field
    /// was proved wholly unobserved when the class was constructed. This is a
    /// read-only view over `dt_ground`; it never installs an independent array
    /// interpretation for the selector application.
    pub(in crate::executor::model) fn authenticated_unobserved_array_field(
        &self,
        model: &Model,
        field_app: TermId,
    ) -> Option<(ArraySort, ArrayValue)> {
        let _projection = ProjectionGuard::enter()?;
        self.ctx.terms.entry_stamp(field_app)?;
        let TermData::App(field_symbol @ Symbol::Named(_), field_args) =
            self.ctx.terms.get(field_app)
        else {
            return None;
        };
        if field_args.len() != 1 || !self.exact_datatype_selector(field_symbol.name()) {
            return None;
        }
        let Sort::Array(field_sort) = self.ctx.terms.sort(field_app) else {
            return None;
        };
        let cell = field_args[0];
        let cell_stamp = self.ctx.terms.entry_stamp(cell)?;
        let classes = self.authenticated_datatype_array_field_classes(model)?;
        let cell_sort = self.ctx.terms.sort(cell);
        let direct = classes.iter().filter(|class| {
            class.members.get(&cell) == Some(&cell_stamp) && cell_sort == &class.cell_sort
        });
        let mut direct = direct.peekable();
        let class = if let Some(class) = direct.next() {
            if direct.next().is_some() {
                return None;
            }
            class
        } else {
            self.unique_fresh_outer_select_class(model, cell, cell_sort, &classes)?
        };
        let ModelValue::Datatype { ctor, args } = &class.value else {
            return None;
        };
        let fields = self.ctx.constructor_selector_info(ctor)?;
        if fields.len() != args.len() {
            return None;
        }
        let mut matches = fields.iter().enumerate().filter(|(_, (selector, sort))| {
            selector == field_symbol.name() && sort == self.ctx.terms.sort(field_app)
        });
        let (index, _) = matches.next()?;
        if matches.next().is_some() || !class.unobserved_fields.contains(&index) {
            return None;
        }
        let ModelValue::Array(value) = args.get(index)? else {
            return None;
        };
        Some((field_sort.as_ref().clone(), value.as_ref().clone()))
    }

    fn unique_fresh_outer_select_class<'a>(
        &self,
        model: &Model,
        cell: TermId,
        cell_sort: &Sort,
        classes: &'a [super::AuthenticatedDatatypeArrayClass],
    ) -> Option<&'a super::AuthenticatedDatatypeArrayClass> {
        if !self.datatype_array_outer_select_cell(cell, cell_sort) {
            return None;
        }
        let EvalValue::Element(emitted) = self.evaluate_term(model, cell) else {
            return None;
        };
        let mut exact = classes.iter().filter(|class| {
            class.cell_sort == *cell_sort
                && (class.carrier == emitted || dt_canonical_string(&class.value) == emitted)
        });
        if let Some(class) = exact.next() {
            return exact.next().is_none().then_some(class);
        }
        let guard = RenderedDatatypeGuard::new(self);
        let parsed = self.parse_rendered_dt_value_cached(&emitted, cell_sort, &guard)?;
        let mut budget = SemanticNormalizationBudget::new();
        let parsed = normalize_datatype_array_value(&parsed, &mut budget)?;
        let mut found = None;
        for class in classes {
            if class.cell_sort != *cell_sort
                || normalize_datatype_array_value(&class.value, &mut budget).as_ref()
                    != Some(&parsed)
            {
                continue;
            }
            if found.is_some() {
                return None;
            }
            found = Some(class);
        }
        found
    }

    /// Exact structural lane through which a post-construction outer-array
    /// select may resolve to an authenticated datatype class. This is shared
    /// by projection and its raw no-bypass claim so they cannot disagree about
    /// which retained rows must fail closed after certificate staleness.
    fn datatype_array_outer_select_cell(&self, cell: TermId, cell_sort: &Sort) -> bool {
        matches!(self.ctx.terms.get(cell), TermData::App(select @ Symbol::Named(_), args)
            if select.name() == "select"
                && args.len() == 2
                && self.canonical_select_owner()
                && matches!(self.ctx.terms.sort(args[0]), Sort::Array(outer)
                    if &outer.element_sort == cell_sort))
    }

    /// Evaluate one point of an authenticated unobserved field. Store entries
    /// are oldest-first, so the reverse scan enforces SMT newest-write-wins.
    pub(in crate::executor::model) fn authenticated_unobserved_array_select(
        &self,
        model: &Model,
        field_app: TermId,
        index: &EvalValue,
    ) -> Option<EvalValue> {
        let (_sort, value) = self.authenticated_unobserved_array_field(model, field_app)?;
        for (key, cell) in value.store.iter().rev() {
            match Self::eval_values_equal_exact(index, &mv_to_eval(key)) {
                Some(true) => return Some(mv_to_eval(cell)),
                Some(false) => {}
                None => return Some(EvalValue::Unknown),
            }
        }
        Some(mv_to_eval(&value.default))
    }
}
