// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent current-query member closure for durable W6 certificates.

use ay_core::term::TermEntryStamp;
use ay_frontend::DeclarationKind;

use super::*;

pub(super) struct CertificateMemberCensus {
    by_class: HashMap<(Sort, String), HashMap<TermId, TermEntryStamp>>,
    constructor_source_members: HashSet<TermId>,
}

impl CertificateMemberCensus {
    pub(super) fn constructor_source_members(&self) -> &HashSet<TermId> {
        &self.constructor_source_members
    }

    pub(super) fn close(
        &self,
        authority: &ExactDatatypeArrayClassAuthority,
    ) -> Option<HashMap<TermId, TermEntryStamp>> {
        let mut members = authority.members.clone();
        if let Some(required) = self
            .by_class
            .get(&(authority.cell_sort.clone(), authority.carrier.clone()))
        {
            for (&term, &stamp) in required {
                if members.insert(term, stamp).is_some_and(|old| old != stamp) {
                    return None;
                }
            }
        }
        (members.len() <= MAX_EXACT_ARRAY_FIELD_TERMS).then_some(members)
    }
}

impl Executor {
    /// Census only independently query-owned constructor syntax plus the
    /// frontend's narrowly authenticated eager declaration bindings. Retained
    /// bridge terms outside those two provenance channels cannot enlarge a
    /// certificate class.
    pub(super) fn certificate_datatype_array_member_census(
        &self,
        model: &Model,
        required_terms: &HashSet<TermId>,
        guard: &RenderedDatatypeGuard,
        work: &mut usize,
        source_budget: &mut SchemaSourceBudget,
    ) -> Option<CertificateMemberCensus> {
        let euf = model.euf_model.as_ref()?;
        let constructor_source_members = self.datatype_array_constructor_source_members(
            required_terms,
            guard,
            work,
            source_budget,
        )?;
        let mut candidates: Vec<_> = constructor_source_members.iter().copied().collect();
        candidates.sort_unstable_by_key(|term| term.index());

        let mut by_class: HashMap<_, HashMap<_, _>> = HashMap::default();
        for term in candidates {
            if !charge_work(work, 1) {
                return None;
            }
            let Some(carrier) = euf.term_values.get(&term) else {
                continue;
            };
            let TermData::App(symbol @ Symbol::Named(_), args) = self.ctx.terms.get(term) else {
                continue;
            };
            if self
                .ctx
                .exact_datatype_member_info(symbol.name())
                .map(|info| info.declaration_kind())
                != Some(DeclarationKind::DatatypeConstructor)
            {
                continue;
            }
            let Some(fields) = self.ctx.constructor_selector_info(symbol.name()) else {
                return None;
            };
            if args.len() != fields.len()
                || !fields
                    .iter()
                    .any(|(_, sort)| matches!(sort, Sort::Array(_)))
            {
                continue;
            }
            let cell_sort = self.ctx.terms.sort(term);
            if !source_budget.charge_sort(cell_sort)
                || !source_budget.charge_name(symbol.name().len())
                || !source_budget.charge_name(carrier.len())
                || fields.iter().any(|(selector, sort)| {
                    !source_budget.charge_name(selector.len()) || !source_budget.charge_sort(sort)
                })
            {
                return None;
            }
            if self
                .exact_forced_constructor_array_sources(term, term, guard)
                .is_none()
            {
                continue;
            }
            let stamp = self.ctx.terms.entry_stamp(term)?;
            let members = by_class
                .entry((cell_sort.clone(), carrier.clone()))
                .or_default();
            if members.insert(term, stamp).is_some_and(|old| old != stamp)
                || members.len() > MAX_EXACT_ARRAY_FIELD_TERMS
            {
                return None;
            }
        }
        Some(CertificateMemberCensus {
            by_class,
            constructor_source_members,
        })
    }

    /// Constructor syntax can constrain an array field only when the
    /// constructor application itself is owned by the authored query, or is a
    /// directly declared eager constructor reconnected to a live hard array
    /// definition. Reachability of an argument alone is insufficient: bridge
    /// machinery may generate `(mk (g cell))`, and that term must not certify
    /// its own field merely because `(g cell)` is queried.
    pub(super) fn datatype_array_constructor_source_members(
        &self,
        required_terms: &HashSet<TermId>,
        guard: &RenderedDatatypeGuard,
        work: &mut usize,
        source_budget: &mut SchemaSourceBudget,
    ) -> Option<HashSet<TermId>> {
        if required_terms.len() > MAX_EXACT_ARRAY_FIELD_TERMS
            || !charge_work(work, required_terms.len())
        {
            return None;
        }
        let equalities = self.datatype_array_hard_equalities()?;
        let declared =
            self.declared_datatype_array_support(&equalities, guard, work, source_budget)?;
        let mut members = required_terms.clone();
        for (term, _) in declared {
            members.insert(term);
            if members.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
        }
        Some(members)
    }
}
