// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model completion for uninterpreted functions: one finite table plus an
//! else value per function applied in a quantifier body (see
//! `interpretation.rs` for how the tables are used).
//!
//! The rows are the candidate model's values at the ground applications the
//! problem mentions, keyed by argument VALUES, so two congruent applications
//! share one row and a candidate that is not a function declines the table.
//! The else value is the first row's value (the model-based "projection"
//! heuristic: an unlisted point behaves like a listed one), or the default of
//! the result sort when there is no row. Keep every observed row until the
//! default is chosen; only substitution omits rows equal to that default.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol, TermData, TermId};

use super::interpretation::{
    is_element_sort, is_fixable_sort, scalar_value_term, Interpretation, UfTable, MAX_TABLE_ROWS,
};
use super::{trace, AuthoredUniversal};
use crate::executor::model::{EvalValue, Model};
use crate::executor::Executor;

/// One table row while the table is being built.
struct TableRow {
    key_values: Vec<EvalValue>,
    key_terms: Vec<TermId>,
    value: EvalValue,
    value_term: TermId,
}

#[expect(
    clippy::large_enum_variant,
    reason = "the owned row preserves exact model-construction custody without another allocation"
)]
enum RowOutcome {
    Row(TableRow),
    Skip,
    NotAFunction,
}

impl Executor {
    /// The term denoting `value` of `sort` under the pins: a literal, or the
    /// representative whose model element is `value`.
    fn model_check_value_term(
        &mut self,
        model: &Model,
        sort: &Sort,
        value: &EvalValue,
        interp: &Interpretation,
    ) -> Option<TermId> {
        if !is_element_sort(self, sort) {
            return scalar_value_term(&mut self.ctx.terms, sort, value);
        }
        let EvalValue::Element(element) = value else {
            return None;
        };
        interp.representatives(sort).iter().copied().find(
            |&rep| matches!(self.evaluate_term(model, rep), EvalValue::Element(e) if &e == element),
        )
    }

    /// Default term for a table whose candidate has no row: a literal, or the
    /// first representative of an uninterpreted result sort.
    fn model_check_default_term(&mut self, sort: &Sort, interp: &Interpretation) -> Option<TermId> {
        if is_element_sort(self, sort) {
            return interp.representatives(sort).first().copied();
        }
        let value = self.unconstrained_default_value(sort)?;
        scalar_value_term(&mut self.ctx.terms, sort, &value)
    }

    /// Complete one function into a table plus an else value and register it
    /// for substitution. Declines (leaving `symbol` free) on any doubt.
    pub(super) fn model_check_table(
        &mut self,
        model: &Model,
        symbol: &Symbol,
        applications: &[TermId],
        universals: &[AuthoredUniversal],
        interp: &mut Interpretation,
    ) {
        let Some((arg_sorts, result_sort)) = self.model_check_signature(symbol, universals) else {
            return;
        };
        // Array-valued UFs cannot pass through EvalValue, which deliberately
        // has no array variant. Propose a closed constant-array interpretation
        // instead. This is only a candidate: the ordinary QMC refutations,
        // residual check and independent model gate must all validate it.
        if matches!(result_sort, Sort::Array(_)) {
            if !arg_sorts.iter().all(|sort| is_fixable_sort(self, sort)) {
                return;
            }
            let Some(default) = self.model_check_closed_array_default(&result_sort, 0) else {
                return;
            };
            interp.index.insert(symbol.clone(), interp.tables.len());
            interp.tables.push(UfTable {
                symbol: symbol.clone(),
                arg_sorts,
                result_sort,
                rows: Vec::new(),
                default,
            });
            return;
        }
        if !arg_sorts
            .iter()
            .chain([&result_sort])
            .all(|sort| is_fixable_sort(self, sort))
        {
            trace(|| format!("qmc: table {symbol:?} has an unfixable sort"));
            return;
        }
        let mut rows: Vec<TableRow> = Vec::new();
        for &app in applications.iter().take(MAX_TABLE_ROWS) {
            match self.model_check_row(model, app, &arg_sorts, &result_sort, &rows, interp) {
                RowOutcome::Row(row) => rows.push(row),
                RowOutcome::Skip => {}
                RowOutcome::NotAFunction => {
                    trace(|| format!("qmc: candidate {symbol:?} is not a function"));
                    return;
                }
            }
        }
        let default = match rows.first() {
            Some(row) => row.value_term,
            None => match self.model_check_default_term(&result_sort, interp) {
                Some(term) => term,
                None => return,
            },
        };
        // Retain every observed point. A later candidate may change ELSE;
        // dropping points equal to today's default would silently change
        // those observations along with it. Compact only against the default
        // of the interpretation actually being substituted.
        let rows: Vec<(Vec<TermId>, TermId)> = rows
            .into_iter()
            .map(|row| (row.key_terms, row.value_term))
            .collect();
        interp.index.insert(symbol.clone(), interp.tables.len());
        interp.tables.push(UfTable {
            symbol: symbol.clone(),
            arg_sorts,
            result_sort,
            rows,
            default,
        });
    }

    /// Closed scalar leaves and recursively nested constant arrays only.
    /// Uninterpreted elements have no closed literal, so they decline rather
    /// than inventing an unpinned representative.
    fn model_check_closed_array_default(&mut self, sort: &Sort, depth: usize) -> Option<TermId> {
        if depth > 32 {
            return None;
        }
        if let Sort::Array(array) = sort {
            let element = self.model_check_closed_array_default(&array.element_sort, depth + 1)?;
            return Some(
                self.ctx
                    .terms
                    .mk_const_array(array.index_sort.clone(), element),
            );
        }
        let value = self.unconstrained_default_value(sort)?;
        scalar_value_term(&mut self.ctx.terms, sort, &value)
    }

    /// One candidate row: the model's value at one ground application.
    fn model_check_row(
        &mut self,
        model: &Model,
        app: TermId,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        earlier: &[TableRow],
        interp: &Interpretation,
    ) -> RowOutcome {
        let TermData::App(_, args) = self.ctx.terms.get(app).clone() else {
            return RowOutcome::Skip;
        };
        let key_values: Vec<EvalValue> = args
            .iter()
            .map(|&arg| self.evaluate_term(model, arg))
            .collect();
        let value = self.evaluate_term(model, app);
        if matches!(value, EvalValue::Unknown)
            || key_values.iter().any(|v| matches!(v, EvalValue::Unknown))
        {
            return RowOutcome::Skip;
        }
        if let Some(row) = earlier.iter().find(|row| row.key_values == key_values) {
            return if row.value == value {
                RowOutcome::Skip
            } else {
                RowOutcome::NotAFunction
            };
        }
        let mut key_terms = Vec::with_capacity(args.len());
        for (key, sort) in key_values.iter().zip(arg_sorts) {
            let Some(term) = self.model_check_value_term(model, sort, key, interp) else {
                return RowOutcome::Skip;
            };
            key_terms.push(term);
        }
        let Some(value_term) = self.model_check_value_term(model, result_sort, &value, interp)
        else {
            return RowOutcome::Skip;
        };
        RowOutcome::Row(TableRow {
            key_values,
            key_terms,
            value,
            value_term,
        })
    }

    /// The argument and result sorts of `symbol`, read off one of its
    /// applications in the bodies.
    fn model_check_signature(
        &self,
        symbol: &Symbol,
        universals: &[AuthoredUniversal],
    ) -> Option<(Vec<Sort>, Sort)> {
        let mut pending: Vec<TermId> = universals.iter().map(|leaf| leaf.body).collect();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) if sym == symbol && !args.is_empty() => {
                    let arg_sorts = args
                        .iter()
                        .map(|&a| self.ctx.terms.sort(a).clone())
                        .collect();
                    return Some((arg_sorts, self.ctx.terms.sort(term).clone()));
                }
                TermData::App(_, args) => pending.extend(args.iter().copied()),
                TermData::Not(inner) => pending.push(*inner),
                TermData::Ite(c, t, e) => pending.extend([*c, *t, *e]),
                _ => {}
            }
        }
        None
    }
}
