// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fully reauthenticated capability for hazardous outer-array completion.

use super::*;

impl Executor {
    /// Authenticate the hazardous outer-array census and return the exact
    /// current datatype-cell terms that its completion pass may observe.
    pub(in crate::executor::model) fn authenticated_datatype_array_completion_members(
        &self,
        model: &Model,
        outer_sort: &ArraySort,
    ) -> Option<AuthenticatedDatatypeArrayMembers> {
        if !self.datatype_sort_carries_array_field(&outer_sort.element_sort)
            || !self.datatype_array_cells_relevant(model, outer_sort)?
        {
            return Some(AuthenticatedDatatypeArrayMembers::from_members(
                HashSet::default(),
            ));
        }
        let classes = self.authenticated_datatype_array_field_classes(model)?;
        if !self.observed_datatype_array_fields_complete_from_classes(model, outer_sort, &classes) {
            return None;
        }
        let members = classes
            .iter()
            .filter(|class| &class.cell_sort == &outer_sort.element_sort)
            .flat_map(|class| class.members.keys().copied())
            .collect();
        Some(AuthenticatedDatatypeArrayMembers::from_members(members))
    }

    /// Whether this exact hazardous outer sort has a current/query-owned cell
    /// that completion must preserve. A generated extensionality witness cell
    /// is relevant through its generation-site-authenticated root even when no
    /// authored selector opens the datatype's array field.
    fn datatype_array_cells_relevant(&self, model: &Model, outer_sort: &ArraySort) -> Option<bool> {
        let candidates = self.datatype_array_completion_candidates(model, outer_sort)?;
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return None;
        }
        for candidate in candidates {
            if self.is_outer_array_datatype_cell(candidate, outer_sort, &guard)
                || self
                    .outer_array_field_cell(candidate, outer_sort, &guard)
                    .is_some()
            {
                return Some(true);
            }
        }
        Some(false)
    }

    /// Bounded provenance census for hazardous outer-array cells. The global
    /// term arena and EUF table retain unrelated deepening/CEGAR rows, so they
    /// are neither scanned nor allowed to consume this capability. Candidates
    /// come only from the authored query, current stamped W6 inventory, and the
    /// generation-site-authenticated extensionality roots whose witness cells
    /// completion must preserve.
    fn datatype_array_completion_candidates(
        &self,
        model: &Model,
        outer_sort: &ArraySort,
    ) -> Option<HashSet<TermId>> {
        if model.dt_array_field_classes.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
            return None;
        }
        let mut candidates = self.datatype_array_field_required_terms()?;
        for authority in &model.dt_array_field_classes {
            if authority.cell_sort != outer_sort.element_sort {
                continue;
            }
            if authority.members.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
            for (&member, &stamp) in &authority.members {
                if self.ctx.terms.entry_stamp(member) != Some(stamp) {
                    return None;
                }
                candidates.insert(member);
                if candidates.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                    return None;
                }
            }
        }

        let mut stack = self.authenticated_datatype_array_extensionality_roots(model)?;
        while let Some(term) = stack.pop() {
            if !candidates.insert(term) {
                continue;
            }
            if candidates.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    return None;
                }
                _ => {}
            }
            if stack
                .len()
                .checked_add(candidates.len())
                .is_none_or(|total| total > MAX_EXACT_ARRAY_FIELD_TERMS)
            {
                return None;
            }
        }
        Some(candidates)
    }

    #[cfg(test)]
    pub(in crate::executor::model) fn observed_datatype_array_fields_complete(
        &self,
        model: &Model,
        outer_sort: &ArraySort,
    ) -> bool {
        let Some(classes) = self.authenticated_datatype_array_field_classes(model) else {
            return false;
        };
        self.observed_datatype_array_fields_complete_from_classes(model, outer_sort, &classes)
    }

    fn observed_datatype_array_fields_complete_from_classes(
        &self,
        model: &Model,
        outer_sort: &ArraySort,
        classes: &[AuthenticatedDatatypeArrayClass],
    ) -> bool {
        let Some(candidates) = self.datatype_array_completion_candidates(model, outer_sort) else {
            return false;
        };
        let mut member_owner = HashMap::default();
        for (index, class) in classes.iter().enumerate() {
            for &member in class.members.keys() {
                member_owner.insert(member, index);
            }
        }
        let guard = RenderedDatatypeGuard::new(self);
        let mut required_hit = false;
        for candidate in candidates {
            let cell = if self.is_outer_array_datatype_cell(candidate, outer_sort, &guard) {
                candidate
            } else if let Some(cell) = self.outer_array_field_cell(candidate, outer_sort, &guard) {
                cell
            } else {
                continue;
            };
            required_hit = true;
            if !member_owner.contains_key(&cell) {
                return false;
            }
        }
        required_hit
    }

    fn is_outer_array_datatype_cell(
        &self,
        cell: TermId,
        outer_sort: &ArraySort,
        guard: &RenderedDatatypeGuard,
    ) -> bool {
        let TermData::App(select_symbol, select_args) = self.ctx.terms.get(cell) else {
            return false;
        };
        select_args.len() == 2
            && self.dt_completion_array_select_application_guarded(
                guard,
                select_symbol,
                select_args,
                cell,
            )
            && matches!(self.ctx.terms.sort(select_args[0]), Sort::Array(candidate)
                if candidate.as_ref() == outer_sort)
    }

    pub(super) fn outer_array_field_cell(
        &self,
        field_app: TermId,
        outer_sort: &ArraySort,
        guard: &RenderedDatatypeGuard,
    ) -> Option<TermId> {
        let TermData::App(field_symbol, field_args) = self.ctx.terms.get(field_app) else {
            return None;
        };
        if field_args.len() != 1
            || !matches!(field_symbol, Symbol::Named(_))
            || !matches!(self.ctx.terms.sort(field_app), Sort::Array(_))
            || !self.exact_datatype_selector(field_symbol.name())
        {
            return None;
        }
        let cell = field_args[0];
        self.is_outer_array_datatype_cell(cell, outer_sort, guard)
            .then_some(cell)
    }
}
