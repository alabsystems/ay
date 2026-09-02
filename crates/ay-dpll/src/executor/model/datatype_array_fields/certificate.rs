// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Durable validation of installed datatype array-field certificates.

use super::*;

impl Executor {
    /// Datatype values of this sort contain an array-valued constructor field
    /// and therefore may be normalized only through the stamped W6 inventory.
    pub(in crate::executor::model) fn datatype_sort_carries_array_field(
        &self,
        sort: &Sort,
    ) -> bool {
        self.sort_carries_array_field_datatype(sort)
    }

    /// Revalidate the entire result-local inventory without relying on a
    /// previously computed verdict. The returned values are safe producer
    /// normalizations for this immutable model; the consuming gate must still
    /// evaluate every authored assertion itself.
    pub(in crate::executor::model) fn authenticated_datatype_array_field_classes(
        &self,
        model: &Model,
    ) -> Option<Vec<AuthenticatedDatatypeArrayClass>> {
        if model.euf_model.is_none() {
            return None;
        }
        if model.dt_array_field_classes.is_empty()
            || model.dt_array_field_classes.len() > MAX_EXACT_ARRAY_FIELD_TERMS
        {
            return None;
        }
        // Resource limits below are charged to the authored reachability set,
        // inventoried classes, and values actually revalidated. The global term
        // arena and EUF table also retain solver-generated deepening/CEGAR rows;
        // their unrelated size is neither evidence nor work for this query.
        let mut work = 0;
        let mut members = HashSet::default();
        let mut class_keys = HashSet::default();
        let mut parse_budget = TypedArrayParseBudget::new();
        let mut semantic_budget = SemanticNormalizationBudget::new();
        let mut source_budget = SchemaSourceBudget::new();
        let required_terms = self.datatype_array_field_required_terms()?;
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return None;
        }
        let member_census = self.certificate_datatype_array_member_census(
            model,
            &required_terms,
            &guard,
            &mut work,
            &mut source_budget,
        )?;
        let constructor_source_members = member_census.constructor_source_members();
        let mut authenticated = Vec::with_capacity(model.dt_array_field_classes.len());
        for authority in &model.dt_array_field_classes {
            if !source_budget.charge_sort(&authority.cell_sort)
                || !source_budget.charge_name(authority.carrier.len())
                || !class_keys.insert((authority.cell_sort.clone(), authority.carrier.clone()))
            {
                return None;
            }
            let closed_members = member_census.close(authority)?;
            if !charge_work(&mut work, closed_members.len()) {
                return None;
            }
            for &member in closed_members.keys() {
                if !members.insert(member) {
                    return None;
                }
            }
            let value = self.installed_array_class_value(
                model,
                authority,
                &closed_members,
                &guard,
                &required_terms,
                constructor_source_members,
                &mut work,
                &mut parse_budget,
                &mut semantic_budget,
            )?;
            authenticated.push(AuthenticatedDatatypeArrayClass {
                cell_sort: authority.cell_sort.clone(),
                carrier: authority.carrier.clone(),
                members: closed_members,
                unobserved_fields: authority.unobserved_fields.clone(),
                value,
            });
        }
        Some(authenticated)
    }

    fn installed_array_class_value(
        &self,
        model: &Model,
        authority: &ExactDatatypeArrayClassAuthority,
        closed_members: &HashMap<TermId, ay_core::term::TermEntryStamp>,
        guard: &RenderedDatatypeGuard,
        required_terms: &HashSet<TermId>,
        constructor_source_members: &HashSet<TermId>,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
        semantic_budget: &mut SemanticNormalizationBudget,
    ) -> Option<ModelValue> {
        let Some(euf) = model.euf_model.as_ref() else {
            return None;
        };
        if authority.members.is_empty()
            || authority.members.len() > MAX_EXACT_ARRAY_FIELD_TERMS
            || closed_members.is_empty()
            || closed_members.len() > MAX_EXACT_ARRAY_FIELD_TERMS
            || closed_members.iter().any(|(&member, &stamp)| {
                self.ctx.terms.entry_stamp(member) != Some(stamp)
                    || self.ctx.terms.sort(member) != &authority.cell_sort
                    || euf.term_values.get(&member) != Some(&authority.carrier)
            })
        {
            return None;
        }
        let Some(cell) = authority
            .members
            .keys()
            .min_by_key(|term| term.index())
            .copied()
        else {
            return None;
        };
        let Some(reference) = model.dt_ground.get(&cell) else {
            return None;
        };
        if !parse_budget.charge_value(reference)
            || !typed_datatype_array_value(reference, &authority.cell_sort, guard)
        {
            return None;
        }
        let ModelValue::Datatype { ctor, args } = reference else {
            return None;
        };
        let members: HashSet<_> = closed_members.keys().copied().collect();
        let Ok(Some(class)) = self.exact_array_field_class(model, &members, ctor) else {
            return None;
        };
        if class.cell_sort != authority.cell_sort || class.carrier != authority.carrier {
            return None;
        }
        if authority.unobserved_fields.len() > class.fields.len()
            || authority.unobserved_fields.iter().any(|index| {
                !class
                    .fields
                    .iter()
                    .any(|(field_index, _, _)| field_index == index)
            })
        {
            return None;
        }
        let normalized_reference = normalize_datatype_array_value(reference, semantic_budget)?;
        for member in closed_members.keys() {
            let Some(value) = model.dt_ground.get(member) else {
                return None;
            };
            if !parse_budget.charge_value(value)
                || !typed_datatype_array_value(value, &authority.cell_sort, guard)
                || normalize_datatype_array_value(value, semantic_budget).as_ref()
                    != Some(&normalized_reference)
            {
                return None;
            }
        }
        for (index, selector, sort) in &class.fields {
            let Some(value) = args.get(*index) else {
                return None;
            };
            if !self.installed_field_matches_reads(
                model,
                &class,
                ctor,
                *index,
                selector,
                sort,
                value,
                authority.unobserved_fields.contains(index),
                required_terms,
                constructor_source_members,
                work,
                parse_budget,
                semantic_budget,
            ) {
                return None;
            }
        }
        Some(reference.clone())
    }

    fn installed_field_matches_reads(
        &self,
        model: &Model,
        class: &ExactClass,
        ctor: &str,
        field_index: usize,
        selector: &str,
        sort: &Sort,
        installed: &ModelValue,
        must_remain_unobserved: bool,
        required_terms: &HashSet<TermId>,
        constructor_source_members: &HashSet<TermId>,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
        semantic_budget: &mut SemanticNormalizationBudget,
    ) -> bool {
        let (Sort::Array(array_sort), ModelValue::Array(value)) = (sort, installed) else {
            return false;
        };
        let Some(apps) = self.selector_apps(model, class, selector, sort, required_terms, work)
        else {
            return false;
        };
        let Some(sources) = self.constructor_array_field_sources(
            model,
            class,
            ctor,
            field_index,
            sort,
            constructor_source_members,
            work,
        ) else {
            return false;
        };
        if sources.unresolved {
            return false;
        }
        let sources = sources.exact;
        if !typed_array_value(value, array_sort) {
            return false;
        }
        let Some(normalized) = normalize_array_value(value, semantic_budget) else {
            return false;
        };
        if apps.is_empty() && sources.is_empty() {
            return must_remain_unobserved;
        }
        if !self.installed_constructor_array_sources_match(
            model,
            &sources,
            array_sort,
            &normalized,
            work,
            parse_budget,
            semantic_budget,
        ) {
            return false;
        }
        if must_remain_unobserved {
            // Re-derive selector-observation absence. Exact constructor
            // sources were compared above and do not revoke this projection
            // provenance; a later authored selector app does.
            return apps.is_empty();
        }
        if apps.is_empty() {
            return false;
        }
        if !charge_work(work, apps.len()) {
            return false;
        }
        for app in apps {
            if !self.installed_app_reads_match(
                model,
                app,
                array_sort,
                &normalized,
                required_terms,
                work,
                parse_budget,
                semantic_budget,
            ) {
                return false;
            }
            if !self.installed_app_interpretation_matches(
                model,
                app,
                array_sort,
                &normalized,
                work,
                parse_budget,
                semantic_budget,
            ) {
                return false;
            }
        }
        true
    }

    fn installed_app_reads_match(
        &self,
        model: &Model,
        app: TermId,
        sort: &ArraySort,
        installed: &NormalizedArrayValue,
        required_terms: &HashSet<TermId>,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
        semantic_budget: &mut SemanticNormalizationBudget,
    ) -> bool {
        if model
            .array_model
            .as_ref()
            .is_some_and(|arrays| arrays.read_conflicted.contains(&app))
        {
            return false;
        }
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
            let (Some(key), Some(actual)) = (
                eval_to_mv(&self.evaluate_term(model, args[1]), &sort.index_sort),
                eval_to_mv(&self.evaluate_term(model, read), &sort.element_sort),
            ) else {
                return false;
            };
            if !parse_budget.charge_value(&key) || !parse_budget.charge_value(&actual) {
                return false;
            }
            if !installed.matches_point(&key, &actual, semantic_budget) {
                return false;
            }
        }
        true
    }

    fn installed_app_interpretation_matches(
        &self,
        model: &Model,
        app: TermId,
        sort: &ArraySort,
        installed: &NormalizedArrayValue,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
        semantic_budget: &mut SemanticNormalizationBudget,
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
            .and_then(|value| self.typed_scalar_text(value, &sort.element_sort, parse_budget));
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
        let mut normalized = ArrayAccumulator::default();
        if !normalized.merge_interpretation(default, stores) {
            return false;
        }
        let Some(ModelValue::Array(extracted)) = normalized.finish(&sort.element_sort) else {
            return false;
        };
        normalize_array_value(&extracted, semantic_budget).is_some_and(|value| value == *installed)
    }
}
