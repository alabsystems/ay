// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Current-solve array-extensionality roots for total datatype construction.

use super::super::dt_construct_budget::MAX_OPAQUE_DT_COLLECTION_ROOTS;
use super::*;

impl Executor {
    /// Recover only direct, generation-site-authenticated outer-array witness
    /// literals whose cells are exact single-constructor datatypes carrying an
    /// array field. These roots preserve the committed cell disequality while
    /// total datatype construction chooses concrete field-array candidates.
    pub(in crate::executor::model) fn authenticated_datatype_array_extensionality_roots(
        &self,
        model: &Model,
    ) -> Option<Vec<TermId>> {
        self.authenticated_datatype_array_extensionality(model)
            .map(|evidence| evidence.roots)
    }

    /// The same generation-site proof as
    /// [`Self::authenticated_datatype_array_extensionality_roots`], retaining
    /// the exact stamped cell operands that may authorize total-DT
    /// construction. A root without its validated cells is never an override
    /// capability.
    pub(in crate::executor::model) fn authenticated_datatype_array_extensionality(
        &self,
        model: &Model,
    ) -> Option<AuthenticatedDatatypeArrayExtensionality> {
        if self.array_ext_shadow.emitted.len() > MAX_OPAQUE_DT_COLLECTION_ROOTS {
            return None;
        }
        // Every inspected term is named by the bounded, birth-stamped shadow
        // ledger. Unrelated entries in the append-only term arena must not
        // consume this capability's resource budget.
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return None;
        }
        let mut roots = Vec::new();
        let mut cells = Vec::new();
        for entry in &self.array_ext_shadow.emitted {
            if !entry.is_current(&self.ctx.terms) {
                return None;
            }
            let cell_equality = match self.direct_datatype_cell_witness_equality(entry, &guard) {
                Ok(Some(cell_equality)) => cell_equality,
                Ok(None) => continue,
                Err(()) => return None,
            };
            if self.committed_sat_bool(model, entry.eq_term) != Some(false)
                || self.committed_sat_bool(model, entry.not_sel_eq) != Some(true)
                || self.committed_sat_bool(model, cell_equality) != Some(false)
            {
                return None;
            }
            let TermData::App(_, cell_args) = self.ctx.terms.get(cell_equality) else {
                return None;
            };
            for &cell in cell_args {
                cells.push(AuthorizedDatatypeArrayCell {
                    term: cell,
                    stamp: self.ctx.terms.entry_stamp(cell)?,
                    cell_sort: self.ctx.terms.sort(cell).clone(),
                });
            }
            roots.push(entry.not_sel_eq);
            if roots.len() > MAX_OPAQUE_DT_COLLECTION_ROOTS {
                return None;
            }
        }
        roots.sort_by_key(|term| term.index());
        roots.dedup();
        cells.sort_by_key(|cell| cell.term.index());
        cells.dedup_by_key(|cell| cell.term);
        Some(AuthenticatedDatatypeArrayExtensionality { roots, cells })
    }

    fn direct_datatype_cell_witness_equality(
        &self,
        entry: &crate::executor::array_ext_shadow::ArrayExtShadowEntry,
        guard: &RenderedDatatypeGuard,
    ) -> Result<Option<TermId>, ()> {
        let TermData::App(eq_symbol, eq_args) = self.ctx.terms.get(entry.eq_term) else {
            return Err(());
        };
        if !matches!(eq_symbol, Symbol::Named(_))
            || eq_symbol.name() != "="
            || eq_args.len() != 2
            || !same_pair(eq_args[0], eq_args[1], entry.lhs, entry.rhs)
        {
            return Err(());
        }
        let Sort::Array(outer_sort) = self.ctx.terms.sort(entry.lhs) else {
            return Err(());
        };
        if self.ctx.terms.sort(entry.rhs) != self.ctx.terms.sort(entry.lhs) {
            return Err(());
        }
        if !guard.is_exact_array_cell(&outer_sort.element_sort)
            || !self.datatype_sort_carries_array_field(&outer_sort.element_sort)
        {
            return Ok(None);
        }
        let datatype_name = guard.datatype_name(&outer_sort.element_sort).ok_or(())?;
        if self
            .ctx
            .datatype_constructors(datatype_name)
            .ok_or(())?
            .len()
            != 1
        {
            return Ok(None);
        }
        let TermData::App(or_symbol, clause_args) = self.ctx.terms.get(entry.ext_clause) else {
            return Err(());
        };
        if !matches!(or_symbol, Symbol::Named(_))
            || or_symbol.name() != "or"
            || clause_args.as_slice() != [entry.eq_term, entry.not_sel_eq]
        {
            return Err(());
        }
        let TermData::Not(cell_equality) = self.ctx.terms.get(entry.not_sel_eq) else {
            return Err(());
        };
        let TermData::App(cell_eq_symbol, cell_eq_args) = self.ctx.terms.get(*cell_equality) else {
            return Err(());
        };
        if !matches!(cell_eq_symbol, Symbol::Named(_))
            || cell_eq_symbol.name() != "="
            || cell_eq_args.len() != 2
            || self.ctx.terms.sort(*cell_equality) != &Sort::Bool
        {
            return Err(());
        }
        let (left_base, left_index) = self.direct_select(cell_eq_args[0], outer_sort).ok_or(())?;
        let (right_base, right_index) = self.direct_select(cell_eq_args[1], outer_sort).ok_or(())?;
        if left_index != right_index
            || !same_pair(left_base, right_base, entry.lhs, entry.rhs)
            || self.ctx.terms.sort(cell_eq_args[0]) != &outer_sort.element_sort
            || self.ctx.terms.sort(cell_eq_args[1]) != &outer_sort.element_sort
        {
            return Err(());
        }
        let [binding] = self
            .array_ext_witness_cache
            .generated_clause_bindings(&self.ctx.terms, entry.ext_clause)
            .ok_or(())?
        else {
            return Err(());
        };
        if binding.witness != left_index
            || !same_pair(binding.array_a, binding.array_b, entry.lhs, entry.rhs)
            || self
                .array_ext_witness_cache
                .pair_witness(&self.ctx.terms, entry.lhs, entry.rhs)
                != Some(left_index)
        {
            return Err(());
        }
        Ok(Some(*cell_equality))
    }

    fn direct_select(&self, term: TermId, sort: &ArraySort) -> Option<(TermId, TermId)> {
        let TermData::App(symbol, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if !matches!(symbol, Symbol::Named(_))
            || symbol.name() != "select"
            || args.len() != 2
            || !matches!(self.ctx.terms.sort(args[0]), Sort::Array(candidate)
                if candidate.as_ref() == sort)
            || self.ctx.terms.sort(args[1]) != &sort.index_sort
        {
            return None;
        }
        Some((args[0], args[1]))
    }

    fn committed_sat_bool(&self, model: &Model, term: TermId) -> Option<bool> {
        self.term_value(&model.sat_model, &model.term_to_var, term)
            .or_else(|| match self.ctx.terms.get(term) {
                TermData::Not(inner) => self
                    .term_value(&model.sat_model, &model.term_to_var, *inner)
                    .map(|value| !value),
                _ => None,
            })
    }
}

fn same_pair(left: TermId, right: TermId, expected_left: TermId, expected_right: TermId) -> bool {
    (left == expected_left && right == expected_right)
        || (left == expected_right && right == expected_left)
}
