// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-query reachability for W6 observations.

use super::*;

impl Executor {
    /// Ground-term reachability for the exact authored query that the final
    /// independent gate replays. Preprocessing may replace `ctx.assertions`,
    /// so the ordinary completion cache is not sufficient authority here.
    pub(in crate::executor::model) fn datatype_array_field_required_terms(
        &self,
    ) -> Option<HashSet<TermId>> {
        // Budget the authored reachability closure below, not the append-only
        // global term arena. Datatype deepening and CEGAR can retain thousands
        // of unrelated generated terms after a small public query has reached
        // a model; letting those terms exhaust this certificate would make its
        // authority depend on solver history rather than on the obligation it
        // authenticates.
        let mut stack = self.independent_gate_query_roots();
        if stack.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
            return None;
        }
        let mut seen = HashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => {
                    if stack
                        .len()
                        .checked_add(args.len())
                        .is_none_or(|amount| amount > MAX_EXACT_ARRAY_FIELD_TERMS)
                    {
                        return None;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    if stack.len() > MAX_EXACT_ARRAY_FIELD_TERMS.saturating_sub(3) {
                        return None;
                    }
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Let(bindings, body) if bindings.is_empty() => stack.push(*body),
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    return None;
                }
                _ => {}
            }
        }
        Some(seen)
    }

    /// Exact current authored datatype cells that may authorize W6 total-DT
    /// construction despite an exported e-graph/lazy assignment.
    ///
    /// A constructible datatype term qualifies only when its OWN bounded
    /// singleton schema has a direct array field. This includes a canonical
    /// outer-array `select` of that exact cell sort. In particular, an
    /// `Array<_, D>` container is not an owner, and a transitive wrapper whose
    /// own constructor has no array field is not promoted.
    pub(in crate::executor::model) fn authored_datatype_array_construction_cells(
        &self,
    ) -> Option<Vec<AuthorizedDatatypeArrayCell>> {
        let required = self.datatype_array_field_required_terms()?;
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return None;
        }
        let mut cells = Vec::new();
        for term in required {
            let sort = self.ctx.terms.sort(term);
            let exact_direct_owner = self.own_singleton_array_field_schema(sort, &guard)
                && self.constructible_datatype_array_owner(term, &guard);
            if !exact_direct_owner {
                continue;
            }
            cells.push(AuthorizedDatatypeArrayCell {
                term,
                stamp: self.ctx.terms.entry_stamp(term)?,
                cell_sort: sort.clone(),
            });
        }
        cells.sort_by_key(|cell| cell.term.index());
        Some(cells)
    }

    fn own_singleton_array_field_schema(&self, sort: &Sort, guard: &RenderedDatatypeGuard) -> bool {
        if !guard.is_exact_array_cell(sort) {
            return false;
        }
        let Some(name) = guard.datatype_name(sort) else {
            return false;
        };
        let Some([constructor]) = self.ctx.datatype_constructors(name) else {
            return false;
        };
        self.ctx
            .constructor_selector_info(constructor)
            .is_some_and(|fields| {
                fields
                    .iter()
                    .any(|(_, field_sort)| matches!(field_sort, Sort::Array(_)))
            })
    }

    fn constructible_datatype_array_owner(
        &self,
        term: TermId,
        guard: &RenderedDatatypeGuard,
    ) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(_, _) => true,
            TermData::App(symbol, args) => {
                if !matches!(symbol, Symbol::Named(_)) {
                    return false;
                }
                let exact_datatype_application =
                    self.ctx
                        .exact_datatype_member_info(symbol.name())
                        .is_some_and(|info| {
                            info.arg_sorts.len() == args.len()
                                && info.arg_sorts.iter().zip(args).all(|(expected, &actual)| {
                                    expected == self.ctx.terms.sort(actual)
                                })
                                && &info.sort == self.ctx.terms.sort(term)
                                && (info.declaration_kind()
                                    == ay_frontend::DeclarationKind::DatatypeConstructor
                                    || (args.len() == 1
                                        && info.declaration_kind()
                                            == ay_frontend::DeclarationKind::DatatypeSelector))
                        });
                exact_datatype_application
                    || self.dt_completion_ordinary_uf_application_guarded(guard, symbol, args, term)
                    || self
                        .dt_completion_array_select_application_guarded(guard, symbol, args, term)
            }
            _ => false,
        }
    }
}
