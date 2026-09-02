// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recovery of eager single-constructor declaration elaborations.

use super::*;

impl Executor {
    /// Recover the exact constructor application installed as the live core
    /// term of a direct source declaration. The frontend may rewrite
    /// `x = (mk source)` to equality of the generated field term and `source`,
    /// leaving no datatype operand in the authored Boolean roots. The live
    /// declaration binding is the narrow provenance that reconnects that hard
    /// field definition to its constructor term.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn collect_declared_datatype_array_support(
        &self,
        equalities: &[AuthoredHardEquality],
        guard: &RenderedDatatypeGuard,
        roots: &mut Vec<TermId>,
        carrier_terms: &mut HashSet<TermId>,
        definition_roots: &mut HashMap<TermId, ()>,
        work: &mut usize,
    ) -> Option<()> {
        let mut schema_budget = SchemaSourceBudget::new();
        for (term, local_roots) in
            self.declared_datatype_array_support(equalities, guard, work, &mut schema_budget)?
        {
            roots.push(term);
            carrier_terms.insert(term);
            definition_roots.extend(local_roots);
        }
        Some(())
    }

    /// Return the same narrowly authenticated declaration recovery used by
    /// the producer so certificate replay can close an omitted class member
    /// without widening its census to every retained/generated term.
    pub(in crate::executor::model::datatype_array_fields) fn declared_datatype_array_support(
        &self,
        equalities: &[AuthoredHardEquality],
        guard: &RenderedDatatypeGuard,
        work: &mut usize,
        schema_budget: &mut SchemaSourceBudget,
    ) -> Option<Vec<(TermId, HashMap<TermId, ()>)>> {
        let mut seen_terms = HashSet::default();
        let mut support = Vec::new();
        for (surface, info) in self.ctx.symbol_iter() {
            let identity = self.ctx.symbol_identity_name(surface, info);
            if !info.arg_sorts.is_empty()
                || info.declaration_kind() != DeclarationKind::Uninterpreted
                || !info.is_direct_source_declaration()
                || self.ctx.overloaded_surface_name(identity).is_some()
                || self.ctx.is_internal_symbol(surface)
                || self.ctx.is_defined_fun(surface)
                || self.ctx.adopted_macro_interp(surface).is_some()
            {
                continue;
            }
            let Some(term) = info.term else {
                return None;
            };
            if !seen_terms.insert(term) {
                continue;
            }
            if self.ctx.terms.entry_stamp(term).is_none()
                || self.ctx.terms.sort(term) != &info.sort
                || self
                    .ctx
                    .symbol_info_by_identity(identity)
                    .is_none_or(|current| {
                        current.term != Some(term)
                            || current.declaration_id() != info.declaration_id()
                    })
            {
                return None;
            }
            let TermData::App(symbol @ Symbol::Named(_), args) = self.ctx.terms.get(term) else {
                continue;
            };
            if self
                .ctx
                .exact_datatype_member_info(symbol.name())
                .map(|member| member.declaration_kind())
                != Some(DeclarationKind::DatatypeConstructor)
            {
                continue;
            }
            let fields = self.ctx.constructor_selector_info(symbol.name())?;
            if args.len() != fields.len()
                || !schema_budget.charge_name(surface.len())
                || !schema_budget.charge_name(identity.len())
                || !schema_budget.charge_name(symbol.name().len())
                || !schema_budget.charge_sort(&info.sort)
            {
                return None;
            }
            for (selector, sort) in fields {
                if !schema_budget.charge_name(selector.len()) || !schema_budget.charge_sort(sort) {
                    return None;
                }
            }
            // Charge only declarations with an exact array-field constructor
            // shape. The symbol table is append-only across solver activity;
            // unrelated source declarations are not work performed by this
            // authored-query certificate.
            if !charge_work(work, 1) {
                return None;
            }
            let Some(array_sources) =
                self.exact_forced_constructor_array_sources(term, term, guard)
            else {
                continue;
            };
            let mut local_roots = HashMap::default();
            let mut supported = true;
            for (source, sort) in array_sources {
                let mut visiting = HashSet::default();
                let mut source_roots = HashMap::default();
                if !self.collect_authored_array_definition_support(
                    source,
                    &sort,
                    equalities,
                    &mut visiting,
                    &mut source_roots,
                    0,
                    work,
                ) || source_roots.is_empty()
                {
                    supported = false;
                    break;
                }
                local_roots.extend(source_roots);
            }
            // A direct declaration alone leaves its generated fields free. At
            // least one exact hard definition must connect this recovered
            // constructor to the current query before it becomes a root.
            if !supported || local_roots.is_empty() {
                continue;
            }
            support.push((term, local_roots));
            if support.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
        }
        Some(support)
    }
}
