// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded source-query facts used by forced array-field reconstruction.

mod declarations;
mod definitions;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};
use ay_frontend::DeclarationKind;

use super::super::rendered_dt_guard::RenderedDatatypeGuard;
use super::super::rendered_dt_limits::SchemaSourceBudget;
use super::{charge_work, Executor, MAX_EXACT_ARRAY_FIELD_TERMS};

#[derive(Clone, Copy)]
pub(in crate::executor::model) struct AuthoredHardEquality {
    pub(in crate::executor::model) root: TermId,
    pub(in crate::executor::model) lhs: TermId,
    pub(in crate::executor::model) rhs: TermId,
}

pub(in crate::executor::model) struct ForcedDatatypeArraySupport {
    pub(in crate::executor::model) roots: Vec<TermId>,
    pub(in crate::executor::model) carrier_terms: HashSet<TermId>,
}

#[derive(Clone)]
pub(super) enum AuthoredArrayDefinition {
    Absent,
    Exact {
        equalities: Vec<TermId>,
        value: TermId,
    },
    Rejected,
}

impl Executor {
    /// Canonical theory-owned equalities that are themselves hard source-query
    /// facts. Only top-level roots and recursively flattened `and` conjuncts
    /// are admitted; every other Boolean connective remains opaque.
    pub(in crate::executor::model) fn datatype_array_hard_equalities(
        &self,
    ) -> Option<Vec<AuthoredHardEquality>> {
        let mut stack = self.independent_gate_query_roots();
        if stack.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
            return None;
        }
        let mut seen = HashSet::default();
        let mut equalities = Vec::new();
        while let Some(root) = stack.pop() {
            self.ctx.terms.entry_stamp(root)?;
            if !seen.insert(root) {
                continue;
            }
            if seen.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
            let TermData::App(symbol @ Symbol::Named(_), args) = self.ctx.terms.get(root) else {
                continue;
            };
            if symbol.name() == "and" {
                if !self.canonical_hard_boolean_head("and")
                    || self.ctx.terms.sort(root) != &Sort::Bool
                    || args
                        .iter()
                        .any(|&arg| self.ctx.terms.sort(arg) != &Sort::Bool)
                    || stack
                        .len()
                        .checked_add(args.len())
                        .is_none_or(|total| total > MAX_EXACT_ARRAY_FIELD_TERMS)
                {
                    return None;
                }
                stack.extend(args.iter().copied());
                continue;
            }
            if symbol.name() != "=" {
                continue;
            }
            if !self.canonical_hard_boolean_head("=")
                || self.ctx.terms.sort(root) != &Sort::Bool
                || args.len() != 2
                || self.ctx.terms.entry_stamp(args[0]).is_none()
                || self.ctx.terms.entry_stamp(args[1]).is_none()
                || self.ctx.terms.sort(args[0]) != self.ctx.terms.sort(args[1])
            {
                return None;
            }
            equalities.push(AuthoredHardEquality {
                root,
                lhs: args[0],
                rhs: args[1],
            });
            if equalities.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
        }
        equalities.sort_by_key(|equality| equality.root.index());
        equalities.dedup_by_key(|equality| equality.root);
        Some(equalities)
    }

    /// Exact forced datatype constructor facts and their uniquely selected
    /// hard array-definition support. This slice is safe to replay through
    /// carrier, datatype, and array completion; malformed or ambiguous source
    /// facts fail closed by contributing no forced authority.
    pub(in crate::executor::model) fn forced_datatype_array_support(
        &self,
    ) -> Option<ForcedDatatypeArraySupport> {
        let equalities = self.datatype_array_hard_equalities()?;
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return None;
        }
        let mut roots = Vec::new();
        let mut carrier_terms = HashSet::default();
        let mut definition_roots = HashMap::default();
        let mut alias_index: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        let mut alias_edges = 0usize;
        for equality in &equalities {
            if matches!(self.ctx.terms.get(equality.lhs), TermData::Var(_, _))
                && matches!(self.ctx.terms.get(equality.rhs), TermData::Var(_, _))
            {
                alias_edges = alias_edges.checked_add(2)?;
                if alias_edges > MAX_EXACT_ARRAY_FIELD_TERMS {
                    return None;
                }
                alias_index
                    .entry(equality.lhs)
                    .or_default()
                    .push((equality.rhs, equality.root));
                alias_index
                    .entry(equality.rhs)
                    .or_default()
                    .push((equality.lhs, equality.root));
            }
        }
        let mut support_work = 0usize;
        for equality in &equalities {
            for (owner, constructor) in [(equality.lhs, equality.rhs), (equality.rhs, equality.lhs)]
            {
                let recognition_work = match self.ctx.terms.get(constructor) {
                    TermData::App(_, args) => args.len().saturating_add(1),
                    _ => 1,
                };
                if !charge_work(&mut support_work, recognition_work) {
                    return None;
                }
                let Some(array_sources) =
                    self.exact_forced_constructor_array_sources(constructor, owner, &guard)
                else {
                    continue;
                };
                roots.push(equality.root);
                carrier_terms.insert(owner);
                carrier_terms.insert(constructor);
                for (source, sort) in array_sources {
                    let mut visiting = HashSet::default();
                    if !self.collect_authored_array_definition_support(
                        source,
                        &sort,
                        &equalities,
                        &mut visiting,
                        &mut definition_roots,
                        0,
                        &mut support_work,
                    ) {
                        return None;
                    }
                }
            }
        }
        self.collect_declared_datatype_array_support(
            &equalities,
            &guard,
            &mut roots,
            &mut carrier_terms,
            &mut definition_roots,
            &mut support_work,
        )?;
        let mut alias_stack: Vec<TermId> = carrier_terms
            .iter()
            .copied()
            .filter(|term| matches!(self.ctx.terms.get(*term), TermData::Var(_, _)))
            .collect();
        while let Some(member) = alias_stack.pop() {
            let Some(aliases) = alias_index.get(&member) else {
                continue;
            };
            support_work = support_work.checked_add(aliases.len())?;
            if support_work > MAX_EXACT_ARRAY_FIELD_TERMS {
                return None;
            }
            for &(alias, equality) in aliases {
                if self.ctx.terms.sort(alias) != self.ctx.terms.sort(member) {
                    return None;
                }
                definition_roots.insert(equality, ());
                if carrier_terms.insert(alias) {
                    alias_stack.push(alias);
                }
            }
        }
        roots.extend(definition_roots.into_keys());
        roots.sort_by_key(|term| term.index());
        roots.dedup();
        if roots.len() > MAX_EXACT_ARRAY_FIELD_TERMS
            || carrier_terms.len() > MAX_EXACT_ARRAY_FIELD_TERMS
        {
            return None;
        }
        Some(ForcedDatatypeArraySupport {
            roots,
            carrier_terms,
        })
    }

    pub(super) fn exact_forced_constructor_array_sources(
        &self,
        constructor: TermId,
        owner: TermId,
        guard: &RenderedDatatypeGuard,
    ) -> Option<Vec<(TermId, Sort)>> {
        let TermData::App(symbol @ Symbol::Named(_), args) = self.ctx.terms.get(constructor) else {
            return None;
        };
        if self
            .ctx
            .exact_datatype_member_info(symbol.name())
            .map(|info| info.declaration_kind())
            != Some(DeclarationKind::DatatypeConstructor)
            || self.ctx.terms.sort(constructor) != self.ctx.terms.sort(owner)
        {
            return None;
        }
        let (datatype_name, ctor) = self.ctx.is_constructor(symbol.name())?;
        let cell_sort = self.ctx.terms.sort(owner);
        let constructors = self.ctx.datatype_constructors(&datatype_name)?;
        if guard.datatype_name(cell_sort)? != datatype_name
            || constructors.len() != 1
            || constructors[0] != ctor
        {
            return None;
        }
        let fields = self.ctx.constructor_selector_info(&ctor)?;
        if fields.len() != args.len() || fields.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
            return None;
        }
        let mut budget = SchemaSourceBudget::new();
        if !budget.charge_sort(cell_sort) || !budget.charge_name(ctor.len()) {
            return None;
        }
        let mut sources = Vec::new();
        for (arg, (selector, sort)) in args.iter().copied().zip(fields) {
            if !budget.charge_name(selector.len())
                || !budget.charge_sort(sort)
                || self.ctx.terms.entry_stamp(arg).is_none()
                || self.ctx.terms.sort(arg) != sort
            {
                return None;
            }
            if matches!(sort, Sort::Array(_)) {
                sources.push((arg, sort.clone()));
            }
        }
        (!sources.is_empty()).then_some(sources)
    }

    fn collect_authored_array_definition_support(
        &self,
        source: TermId,
        sort: &Sort,
        equalities: &[AuthoredHardEquality],
        visiting: &mut HashSet<TermId>,
        roots: &mut HashMap<TermId, ()>,
        depth: u32,
        work: &mut usize,
    ) -> bool {
        let Some(next_work) = work.checked_add(1) else {
            return false;
        };
        *work = next_work;
        if depth > super::MAX_TYPED_ARRAY_DEPTH
            || *work > MAX_EXACT_ARRAY_FIELD_TERMS
            || !visiting.insert(source)
            || self.ctx.terms.entry_stamp(source).is_none()
            || self.ctx.terms.sort(source) != sort
        {
            return false;
        }
        let result = if matches!(self.ctx.terms.get(source), TermData::Var(_, _)) {
            match self.authored_array_definition_from(source, sort, equalities, visiting, work) {
                AuthoredArrayDefinition::Rejected => false,
                AuthoredArrayDefinition::Absent => true,
                AuthoredArrayDefinition::Exact {
                    equalities: support,
                    value,
                } => {
                    roots.extend(support.into_iter().map(|equality| (equality, ())));
                    self.collect_array_source_alias_support(
                        value,
                        sort,
                        equalities,
                        visiting,
                        roots,
                        depth + 1,
                        work,
                    )
                }
            }
        } else {
            self.collect_array_source_alias_support(
                source, sort, equalities, visiting, roots, depth, work,
            )
        };
        visiting.remove(&source);
        result
    }

    fn collect_array_source_alias_support(
        &self,
        value: TermId,
        sort: &Sort,
        equalities: &[AuthoredHardEquality],
        visiting: &mut HashSet<TermId>,
        roots: &mut HashMap<TermId, ()>,
        depth: u32,
        work: &mut usize,
    ) -> bool {
        if depth > super::MAX_TYPED_ARRAY_DEPTH {
            return false;
        }
        match self.ctx.terms.get(value) {
            TermData::Var(_, _) => self.collect_authored_array_definition_support(
                value,
                sort,
                equalities,
                visiting,
                roots,
                depth + 1,
                work,
            ),
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "store" && args.len() == 3 =>
            {
                let Sort::Array(array) = sort else {
                    return false;
                };
                self.canonical_array_source_symbol("store")
                    && self.ctx.terms.sort(args[0]) == sort
                    && self.ctx.terms.sort(args[1]) == &array.index_sort
                    && self.ctx.terms.sort(args[2]) == &array.element_sort
                    && self.ctx.terms.entry_stamp(args[1]).is_some()
                    && self.ctx.terms.entry_stamp(args[2]).is_some()
                    && self.collect_authored_array_definition_support(
                        args[0],
                        sort,
                        equalities,
                        visiting,
                        roots,
                        depth + 1,
                        work,
                    )
            }
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "const-array" && args.len() == 1 =>
            {
                let Sort::Array(array) = sort else {
                    return false;
                };
                self.canonical_array_source_symbol("const-array")
                    && self.ctx.terms.entry_stamp(args[0]).is_some()
                    && self.ctx.terms.sort(args[0]) == &array.element_sort
            }
            TermData::Let(bindings, body) if bindings.is_empty() => {
                self.ctx.terms.sort(*body) == sort
                    && self.collect_authored_array_definition_support(
                        *body,
                        sort,
                        equalities,
                        visiting,
                        roots,
                        depth + 1,
                        work,
                    )
            }
            TermData::Ite(condition, then_term, else_term) => {
                self.ctx.terms.entry_stamp(*condition).is_some()
                    && self.ctx.terms.sort(*condition) == &Sort::Bool
                    && self.ctx.terms.sort(*then_term) == sort
                    && self.ctx.terms.sort(*else_term) == sort
                    && self.collect_authored_array_definition_support(
                        *then_term,
                        sort,
                        equalities,
                        visiting,
                        roots,
                        depth + 1,
                        work,
                    )
                    && self.collect_authored_array_definition_support(
                        *else_term,
                        sort,
                        equalities,
                        visiting,
                        roots,
                        depth + 1,
                        work,
                    )
            }
            _ => false,
        }
    }

    fn authored_array_definition_value_shape(&self, value: TermId, sort: &Sort) -> bool {
        if self.ctx.terms.entry_stamp(value).is_none() || self.ctx.terms.sort(value) != sort {
            return false;
        }
        match self.ctx.terms.get(value) {
            TermData::Var(_, _) => true,
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "const-array" && args.len() == 1 =>
            {
                matches!(sort, Sort::Array(array)
                    if self.canonical_array_source_symbol("const-array")
                        && self.ctx.terms.entry_stamp(args[0]).is_some()
                        && self.ctx.terms.sort(args[0]) == &array.element_sort)
            }
            TermData::App(symbol @ Symbol::Named(_), args)
                if symbol.name() == "store" && args.len() == 3 =>
            {
                matches!(sort, Sort::Array(array)
                    if self.canonical_array_source_symbol("store")
                        && self.ctx.terms.sort(args[0]) == sort
                        && self.ctx.terms.entry_stamp(args[1]).is_some()
                        && self.ctx.terms.entry_stamp(args[2]).is_some()
                        && self.ctx.terms.sort(args[1]) == &array.index_sort
                        && self.ctx.terms.sort(args[2]) == &array.element_sort)
            }
            TermData::Let(bindings, body) => {
                bindings.is_empty() && self.ctx.terms.sort(*body) == sort
            }
            TermData::Ite(condition, then_term, else_term) => {
                self.ctx.terms.sort(*condition) == &Sort::Bool
                    && self.ctx.terms.sort(*then_term) == sort
                    && self.ctx.terms.sort(*else_term) == sort
            }
            _ => false,
        }
    }

    fn canonical_hard_boolean_head(&self, name: &str) -> bool {
        self.ctx.symbol_info_by_identity(name).is_none_or(|info| {
            self.ctx.effective_declaration_kind(info.declaration_id())
                == Some(DeclarationKind::Theory)
        })
    }
}
