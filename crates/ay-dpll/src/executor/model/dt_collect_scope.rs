// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation/work preflight for opaque-aware datatype collection.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};
use ay_frontend::DeclarationKind;

use super::dt_construct_budget::{OpaqueDtCollectionBudget, OpaqueDtCollectionScope};
use super::rendered_dt_guard::RenderedDatatypeGuard;
use crate::executor::Executor;

pub(super) struct OpaqueDtCollectionPreflight {
    strict: bool,
    scope: Option<OpaqueDtCollectionScope>,
    guard: Option<RenderedDatatypeGuard>,
    opaque_apps: HashSet<TermId>,
    datatype_names: HashSet<String>,
    datatype_members: HashMap<String, DeclarationKind>,
}

impl OpaqueDtCollectionPreflight {
    pub(super) fn into_parts(
        self,
    ) -> (
        Option<OpaqueDtCollectionScope>,
        Option<RenderedDatatypeGuard>,
        HashSet<TermId>,
        HashSet<String>,
        HashMap<String, DeclarationKind>,
        bool,
    ) {
        (
            self.scope,
            self.guard,
            self.opaque_apps,
            self.datatype_names,
            self.datatype_members,
            self.strict,
        )
    }

    #[cfg(test)]
    pub(super) fn is_strict(&self) -> bool {
        self.strict
    }
}

struct CollectionPreflight<'a> {
    exec: &'a Executor,
    budget: OpaqueDtCollectionBudget,
    guard: Option<RenderedDatatypeGuard>,
    opaque_terms: usize,
    datatype_selectors: usize,
    constructors: usize,
    congruence_weight: usize,
    opaque_apps: HashSet<TermId>,
    datatype_terms: Vec<TermId>,
    datatype_names: HashSet<String>,
    datatype_members: HashMap<String, DeclarationKind>,
    declaration_scan_work: usize,
}

impl Executor {
    /// Traverse the exact collection roots without cloning application
    /// payloads. The returned scope proves that all vectors and quadratic
    /// fixpoints materialized by `dt_collect` fit the opaque-lane envelope.
    pub(super) fn preflight_opaque_dt_collection(
        &self,
        extra_roots: &[TermId],
    ) -> Option<OpaqueDtCollectionPreflight> {
        if !self.query_has_opaque_datatype_candidate(extra_roots) {
            return Some(OpaqueDtCollectionPreflight {
                strict: false,
                scope: None,
                guard: None,
                opaque_apps: HashSet::default(),
                datatype_names: HashSet::default(),
                datatype_members: HashMap::default(),
            });
        }
        let root_count = self.ctx.assertions.len().checked_add(extra_roots.len())?;
        let declarations = self.ctx.bounded_projection_declaration_inventory_size()?;
        let declaration_scan_work = declarations.checked_mul(8)?.checked_mul(257)?;
        let mut budget = OpaqueDtCollectionBudget::new();
        if !budget.record_roots(root_count) {
            return None;
        }
        let mut stack: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .chain(extra_roots.iter().copied())
            .collect();
        let mut seen = HashSet::default();
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return None;
        }
        let (datatype_names, datatype_members) = bounded_datatype_inventory(self)?;
        let mut preflight = CollectionPreflight {
            exec: self,
            budget,
            guard: Some(guard),
            opaque_terms: 0,
            datatype_selectors: 0,
            constructors: 0,
            congruence_weight: 1,
            opaque_apps: HashSet::default(),
            datatype_terms: Vec::new(),
            datatype_names,
            datatype_members,
            declaration_scan_work,
        };

        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            preflight.visit(term, &mut stack)?;
        }
        preflight.finish()
    }

    fn query_has_opaque_datatype_candidate(&self, extra_roots: &[TermId]) -> bool {
        const MAX_DISCOVERY_TERMS: usize = 4_096;
        const MAX_DISCOVERY_EDGES: usize = 4_096;
        const MAX_DISCOVERY_ROOTS: usize = 1_024;
        if self.ctx.assertions.len().saturating_add(extra_roots.len()) > MAX_DISCOVERY_ROOTS {
            return false;
        }
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return false;
        }
        let mut stack: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .chain(extra_roots.iter().copied())
            .collect();
        let mut seen = HashSet::default();
        let mut edges = 0usize;
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_DISCOVERY_TERMS {
                return false;
            }
            match self.ctx.terms.get(term) {
                TermData::App(symbol, args) => {
                    edges = match edges.checked_add(args.len()) {
                        Some(total) if total <= MAX_DISCOVERY_EDGES => total,
                        _ => return false,
                    };
                    if symbol.name().len() > 256 {
                        return false;
                    }
                    if guard.datatype_name(self.ctx.terms.sort(term)).is_some() {
                        let kind = self
                            .ctx
                            .exact_datatype_member_info(symbol.name())
                            .map(|info| info.declaration_kind());
                        if kind != Some(DeclarationKind::DatatypeConstructor)
                            && !(args.len() == 1 && kind == Some(DeclarationKind::DatatypeSelector))
                        {
                            return true;
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => {
                    edges += 1;
                    if edges > MAX_DISCOVERY_EDGES {
                        return false;
                    }
                    stack.push(*inner);
                }
                TermData::Ite(condition, then_term, else_term) => {
                    edges += 3;
                    if edges > MAX_DISCOVERY_EDGES {
                        return false;
                    }
                    stack.push(*condition);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                _ => {}
            }
        }
        false
    }
}

fn bounded_datatype_inventory(
    exec: &Executor,
) -> Option<(HashSet<String>, HashMap<String, DeclarationKind>)> {
    let mut names = HashSet::default();
    let mut members = HashMap::default();
    for (name, constructors) in exec.ctx.datatype_iter() {
        names.insert(name.to_string());
        for constructor in constructors {
            let info = exec.ctx.exact_datatype_member_info(constructor)?;
            members.insert(constructor.clone(), info.declaration_kind());
            let tester = format!("is-{constructor}");
            if let Some(info) = exec.ctx.exact_datatype_member_info(&tester) {
                members.insert(tester, info.declaration_kind());
            }
            for (selector, _) in exec.ctx.constructor_selector_info(constructor)? {
                let info = exec.ctx.exact_datatype_member_info(selector)?;
                members.insert(selector.clone(), info.declaration_kind());
            }
        }
    }
    Some((names, members))
}

impl CollectionPreflight<'_> {
    fn visit(&mut self, term: TermId, stack: &mut Vec<TermId>) -> Option<()> {
        self.budget.visit_term().then_some(())?;
        let result_is_dt = self.term_has_datatype_sort(term);
        if result_is_dt {
            self.budget.record_dt_term().then_some(())?;
            self.datatype_terms.push(term);
        }
        match self.exec.ctx.terms.get(term) {
            TermData::Var(name, _) if result_is_dt => self.visit_datatype_var(name),
            TermData::App(symbol, args) => self.visit_app(term, symbol, args, result_is_dt, stack),
            TermData::Not(inner) => {
                self.budget.visit_children(1).then_some(())?;
                stack.push(*inner);
                Some(())
            }
            TermData::Ite(condition, then_term, else_term) => {
                self.budget.visit_children(3).then_some(())?;
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
                Some(())
            }
            _ => Some(()),
        }
    }

    fn visit_datatype_var(&mut self, name: &str) -> Option<()> {
        if self.datatype_member_kind(name) == Some(DeclarationKind::DatatypeConstructor) {
            self.constructors = self.constructors.checked_add(1)?;
            self.budget
                .record_constructor(0, name.len())
                .then_some(())?;
        }
        Some(())
    }

    fn visit_app(
        &mut self,
        term: TermId,
        symbol: &Symbol,
        args: &[TermId],
        result_is_dt: bool,
        stack: &mut Vec<TermId>,
    ) -> Option<()> {
        self.budget.visit_app(args.len()).then_some(())?;
        let name = symbol.name();
        if name.len() > 256 {
            return None;
        }
        self.congruence_weight = self
            .congruence_weight
            .max(name.len().saturating_add(args.len()).saturating_add(1));
        let kind = self.datatype_member_kind(name);
        if result_is_dt {
            self.visit_datatype_result(term, symbol, args, kind)?;
        } else if args.len() == 1
            && kind == Some(DeclarationKind::DatatypeSelector)
            && self.term_has_datatype_sort(args[0])
        {
            self.datatype_selectors = self.datatype_selectors.checked_add(1)?;
            self.budget.record_selector(name.len(), 1).then_some(())?;
        }
        self.record_atoms(name, args, kind)?;
        stack.extend(args.iter().copied());
        Some(())
    }

    fn visit_datatype_result(
        &mut self,
        term: TermId,
        symbol: &Symbol,
        args: &[TermId],
        kind: Option<DeclarationKind>,
    ) -> Option<()> {
        let name = symbol.name();
        if kind == Some(DeclarationKind::DatatypeConstructor) {
            self.constructors = self.constructors.checked_add(1)?;
            return self
                .budget
                .record_constructor(args.len(), name.len())
                .then_some(());
        }
        if args.len() == 1 && kind == Some(DeclarationKind::DatatypeSelector) {
            self.datatype_selectors = self.datatype_selectors.checked_add(1)?;
            return self.budget.record_selector(name.len(), 2).then_some(());
        }
        self.budget
            .record_signature_check(self.declaration_scan_work)
            .then_some(())?;
        let Some(signature_work) = self
            .exec
            .opaque_application_signature_work(symbol, args, term)
        else {
            return Some(());
        };
        self.budget
            .record_signature_check(signature_work.checked_mul(4)?)
            .then_some(())?;
        let guard = self
            .guard
            .get_or_insert_with(|| RenderedDatatypeGuard::new(self.exec));
        if self
            .exec
            .dt_completion_ordinary_uf_application_guarded(guard, symbol, args, term)
            || self
                .exec
                .dt_completion_array_select_application_guarded(guard, symbol, args, term)
        {
            self.opaque_terms = self.opaque_terms.checked_add(1)?;
            self.opaque_apps.insert(term);
        }
        Some(())
    }

    fn record_atoms(
        &mut self,
        name: &str,
        args: &[TermId],
        kind: Option<DeclarationKind>,
    ) -> Option<()> {
        if kind == Some(DeclarationKind::DatatypeTester)
            && args.len() == 1
            && self.term_has_datatype_sort(args[0])
        {
            self.budget.record_tester(name.len()).then_some(())?;
        }
        if name == "="
            && args.len() == 2
            && self.term_has_datatype_sort(args[0])
            && self.term_has_datatype_sort(args[1])
        {
            self.budget.record_equality().then_some(())?;
        }
        if name == "distinct" && args.iter().all(|&arg| self.term_has_datatype_sort(arg)) {
            self.budget.record_distinct(args.len()).then_some(())?;
        }
        Some(())
    }

    fn finish(mut self) -> Option<OpaqueDtCollectionPreflight> {
        let scope = if self.opaque_terms == 0 {
            None
        } else {
            let guard = self.guard.as_ref()?;
            // Registered bounded schemas are the construction bar; the exact
            // rendered fragment is only required by the rendering-dependent
            // consumers, which re-check `is_exact` per value themselves (see
            // `RenderedDatatypeGuard::is_registered`). This also keeps the
            // `Sort::Datatype` inline-schema representation fail-closed: the
            // guard recognizes only registry-backed carrier names.
            if self
                .datatype_terms
                .iter()
                .any(|&term| !guard.is_registered(self.exec.ctx.terms.sort(term)))
            {
                return None;
            }
            Some(self.budget.finish(
                self.opaque_terms,
                self.datatype_selectors,
                self.constructors,
                self.congruence_weight,
            )?)
        };
        Some(OpaqueDtCollectionPreflight {
            strict: true,
            scope,
            guard: self.guard,
            opaque_apps: self.opaque_apps,
            datatype_names: self.datatype_names,
            datatype_members: self.datatype_members,
        })
    }

    fn term_has_datatype_sort(&self, term: TermId) -> bool {
        match self.exec.ctx.terms.sort(term) {
            Sort::Datatype(datatype) if datatype.name.len() <= 256 => {
                self.datatype_names.contains(&datatype.name)
            }
            Sort::Uninterpreted(name) if name.len() <= 256 => self.datatype_names.contains(name),
            _ => false,
        }
    }

    fn datatype_member_kind(&self, identity: &str) -> Option<DeclarationKind> {
        self.datatype_members.get(identity).copied()
    }
}
