// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Faithful full-scope transport for unambiguous monomorphic datatypes.
//!
//! Datatype members are declarations of an interpreted theory, not free UFs.
//! Reconstruct their complete definition from sticky exact carrier metadata,
//! validate the same typed heads used by the roots, then use the SAME Alethe
//! term printer/override table as the paired proof. No premise is selected or
//! added here. This optional transport grants no solver/proof authority.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ay_core::kani_compat::DetHashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{quote_symbol, Sort, Symbol, TermId};
use ay_frontend::{DeclarationKind, PublicSort, SymbolInfo};

use super::{is_builtin_operator, Executor};

const MAX_NODES: usize = 262_144;
const MAX_WORK: usize = 16 * 1024 * 1024;
const MAX_DEPTH: usize = 128;
const MAX_BYTES: usize = 4 * 1024 * 1024;
const MAX_LITERAL_BITS: u64 = 1_048_576;

#[derive(Default)]
struct Budget {
    visits: usize,
    work: usize,
    bytes: usize,
}

impl Budget {
    fn charge(&mut self, bytes: usize) -> Option<()> {
        self.visits = self.visits.checked_add(1)?;
        self.charge_work(bytes.checked_add(1)?)?;
        self.bytes = self.bytes.checked_add(bytes)?;
        (self.visits <= MAX_NODES && self.work <= MAX_WORK && self.bytes <= MAX_BYTES).then_some(())
    }

    fn charge_work(&mut self, work: usize) -> Option<()> {
        self.work = self.work.checked_add(work)?;
        (self.work <= MAX_WORK).then_some(())
    }

    fn constant(&mut self, value: &Constant) -> Option<()> {
        let bits = match value {
            Constant::Bool(_) => 1,
            Constant::Int(value) => value.bits(),
            Constant::Rational(value) => {
                value.0.numer().bits().checked_add(value.0.denom().bits())?
            }
            Constant::BitVec { value, width } => value.bits().max(u64::from(*width)),
            _ => return None,
        };
        if bits > MAX_LITERAL_BITS {
            return None;
        }
        let bits = usize::try_from(bits).ok()?;
        // Admit repeated multi-limb decimal conversion before Display runs.
        // This is arithmetic work admission, not an integer width policy.
        self.work = self
            .work
            .checked_add(bits.checked_mul(bits)?.checked_mul(2)?.checked_add(1)?)?;
        self.charge(bits.checked_add(64)?)
    }

    fn name(&mut self, name: &str) -> Option<()> {
        self.charge(name.len().checked_mul(2)?.checked_add(64)?)?;
        // SMT-LIB quoted symbols have no escaping convention for these bytes.
        (!name.is_empty()
            && !name
                .chars()
                .any(|c| c == '|' || c == '\\' || c.is_control()))
        .then_some(())
    }

    fn sort<'a>(&mut self, sort: &'a Sort, names: &mut BTreeSet<&'a str>) -> Option<()> {
        let mut pending = vec![(sort, 0usize)];
        while let Some((sort, depth)) = pending.pop() {
            self.charge(64)?;
            if depth > MAX_DEPTH {
                return None;
            }
            match sort {
                Sort::Bool | Sort::Int | Sort::Real => {}
                Sort::BitVec(bits)
                    if bits.width > 0 && u64::from(bits.width) <= MAX_LITERAL_BITS => {}
                Sort::Array(array) => {
                    pending.push((&array.index_sort, depth + 1));
                    pending.push((&array.element_sort, depth + 1));
                }
                Sort::Uninterpreted(name) => {
                    if matches!(
                        name.as_str(),
                        "Bool"
                            | "Int"
                            | "Real"
                            | "String"
                            | "Array"
                            | "Seq"
                            | "BitVec"
                            | "RoundingMode"
                            | "RegLan"
                    ) {
                        return None;
                    }
                    self.name(name)?;
                    names.insert(name);
                }
                _ => return None,
            }
        }
        Some(())
    }

    fn public_sort<'a>(
        &mut self,
        sort: &'a PublicSort,
        names: &mut BTreeSet<&'a str>,
    ) -> Option<()> {
        let mut pending = vec![(sort, 0usize)];
        while let Some((sort, depth)) = pending.pop() {
            self.charge(64)?;
            if depth > MAX_DEPTH {
                return None;
            }
            match sort {
                PublicSort::Core(sort) => self.sort(sort, names)?,
                PublicSort::Array(index, element) => {
                    pending.push((index, depth + 1));
                    pending.push((element, depth + 1));
                }
                // Public finite-set/character lowering must never be erased.
                _ => return None,
            }
        }
        Some(())
    }
}

struct Head<'a> {
    arguments: Vec<&'a Sort>,
    result: &'a Sort,
    info: Option<&'a SymbolInfo>,
    constant: Option<TermId>,
    datatype: bool,
}

struct Plan<'a> {
    budget: Budget,
    sorts: BTreeSet<&'a str>,
    datatypes: BTreeMap<&'a str, &'a [String]>,
    heads: BTreeMap<&'a str, Head<'a>>,
}

impl<'a> Plan<'a> {
    fn head(
        &mut self,
        name: &'a str,
        arguments: impl ExactSizeIterator<Item = &'a Sort>,
        result: &'a Sort,
        info: Option<&'a SymbolInfo>,
        constant: Option<TermId>,
        datatype: bool,
    ) -> Option<()> {
        self.budget.name(name)?;
        self.budget
            .charge(arguments.len().checked_mul(size_of::<&Sort>())?)?;
        let arguments: Vec<_> = arguments.collect();
        for sort in arguments.iter().copied().chain(std::iter::once(result)) {
            self.budget.sort(sort, &mut self.sorts)?;
        }
        if let Some(previous) = self.heads.get(name) {
            if previous.arguments != arguments
                || previous.result != result
                || previous.datatype != datatype
                || previous.constant != constant
                || match (previous.info, info) {
                    (Some(a), Some(b)) => a.declaration_identity() != b.declaration_identity(),
                    (None, None) => false,
                    _ => true,
                }
            {
                return None;
            }
        } else {
            self.heads.insert(
                name,
                Head {
                    arguments,
                    result,
                    info,
                    constant,
                    datatype,
                },
            );
        }
        Some(())
    }

    fn signature(&mut self, name: &'a str, info: &'a SymbolInfo, datatype: bool) -> Option<()> {
        if info.public_arg_sorts.len() != info.arg_sorts.len() {
            return None;
        }
        for sort in info
            .public_arg_sorts
            .iter()
            .chain(std::iter::once(&info.public_sort))
        {
            self.budget.public_sort(sort, &mut self.sorts)?;
        }
        self.head(
            name,
            info.arg_sorts.iter(),
            &info.sort,
            Some(info),
            info.term,
            datatype,
        )
    }
    fn exact_member(
        &self,
        name: &str,
        info: &SymbolInfo,
        kind: DeclarationKind,
    ) -> Option<&'a str> {
        let (&identity, declared) = self.heads.get_key_value(name)?;
        if !declared.datatype
            || declared.info?.declaration_identity() != info.declaration_identity()
            || declared.constant != info.term
            || declared.result != &info.sort
            || !declared.arguments.iter().copied().eq(info.arg_sorts.iter())
            || info.declaration_kind() != kind
        {
            return None;
        }
        Some(identity)
    }
}

type Bound<'a> = Arc<BTreeMap<&'a str, &'a Sort>>;

fn enqueue<'a>(
    pending: &mut Vec<(TermId, Bound<'a>, usize)>,
    budget: &mut Budget,
    term: TermId,
    bound: Bound<'a>,
    depth: usize,
) -> Option<()> {
    budget.charge(size_of::<(TermId, Bound<'_>, usize)>())?;
    pending.push((term, bound, depth));
    Some(())
}

fn enqueue_print(
    pending: &mut Vec<(TermId, usize)>,
    budget: &mut Budget,
    term: TermId,
    depth: usize,
) -> Option<()> {
    budget.charge(64)?;
    pending.push((term, depth));
    Some(())
}

fn push(out: &mut String, text: &str) -> Option<()> {
    (out.len().checked_add(text.len())? <= MAX_BYTES).then_some(())?;
    out.push_str(text);
    Some(())
}

fn write_sort(out: &mut String, sort: &Sort) -> Option<()> {
    match sort {
        Sort::Bool => push(out, "Bool"),
        Sort::Int => push(out, "Int"),
        Sort::Real => push(out, "Real"),
        Sort::BitVec(bits) => push(out, &format!("(_ BitVec {})", bits.width)),
        Sort::Uninterpreted(name) => push(out, &quote_symbol(name)),
        Sort::Array(array) => {
            push(out, "(Array ")?;
            write_sort(out, &array.index_sort)?;
            push(out, " ")?;
            write_sort(out, &array.element_sort)?;
            push(out, ")")
        }
        _ => None,
    }
}

impl Executor {
    fn datatype_transport_context_footprint(&self, budget: &mut Budget) -> Option<()> {
        let stop = self.make_strict_check_stop();
        let capacity = self.ctx.proof_transport_datatype_capacity()?;
        budget.charge_work(capacity)?;
        let start = budget.bytes;
        let mut names = BTreeSet::new();
        // Raw iterators do not hash names or clone metadata first. Include
        // sparse buckets and sticky/popped members before semantic lookups.
        for (name, info) in self.ctx.native_input_symbol_storage_iter() {
            if stop() {
                return None;
            }
            budget.name(name)?;
            if let Some(core) = &info.internal_name {
                budget.name(core)?;
            }
            for sort in info.arg_sorts.iter().chain(std::iter::once(&info.sort)) {
                budget.sort(sort, &mut names)?;
            }
            for sort in info
                .public_arg_sorts
                .iter()
                .chain(std::iter::once(&info.public_sort))
            {
                budget.public_sort(sort, &mut names)?;
            }
        }
        for (name, sort) in self.ctx.native_input_sort_storage_iter() {
            if stop() {
                return None;
            }
            budget.name(name)?;
            budget.sort(sort, &mut names)?;
        }
        for (name, selectors) in self.ctx.ctor_selectors_iter() {
            if stop() {
                return None;
            }
            budget.name(name)?;
            for selector in selectors {
                budget.name(selector)?;
            }
        }
        // Cover worst-case probe work for the same bounded raw declaration
        // payload across the subsequent identity/signature lookup passes.
        let raw = budget.bytes.checked_sub(start)?.checked_add(1)?;
        budget.charge_work(capacity.checked_mul(raw)?.checked_mul(4)?)
    }

    /// Canonical SMT-LIB tester spelling derived from exact registered native
    /// member identities. This is a presentation map, never proof authority.
    /// An opaque authored parent spelling that would hide a required rewrite
    /// declines instead of being silently replaced.
    pub(in crate::executor) fn datatype_problem_spelling_overrides(
        &self,
        source: Option<&DetHashMap<TermId, String>>,
    ) -> Option<DetHashMap<TermId, String>> {
        let stop = self.make_strict_check_stop();
        let count = self.ctx.terms.len();
        let mut budget = Budget::default();
        self.datatype_transport_context_footprint(&mut budget)?;
        budget.charge(count.checked_mul(64)?)?;
        if let Some(source) = source {
            budget.charge(source.capacity().checked_mul(64)?)?;
            for (term, text) in source {
                budget.charge(text.len().checked_add(64)?)?;
                if usize::try_from(term.0).ok()? >= count {
                    return None;
                }
                self.ctx.terms.entry_stamp(*term)?;
            }
        }
        let mut raw_sorts = BTreeSet::new();
        let mut affected = vec![false; count];
        let mut result = DetHashMap::default();
        for index in 0..count {
            if stop() {
                return None;
            }
            let term = TermId(u32::try_from(index).ok()?);
            self.ctx.terms.entry_stamp(term)?;
            let data = self.ctx.terms.get(term);
            budget.sort(self.ctx.terms.sort(term), &mut raw_sorts)?;
            match data {
                TermData::Const(value) => budget.constant(value)?,
                TermData::Var(name, _) => budget.name(name)?,
                TermData::App(Symbol::Named(name), _) => budget.name(name.as_str())?,
                TermData::App(_, _) => return None,
                TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => {
                    for (name, sort) in vars {
                        budget.name(name)?;
                        budget.sort(sort, &mut raw_sorts)?;
                    }
                }
                TermData::Let(bindings, _) => {
                    for (name, _) in bindings {
                        budget.name(name)?;
                    }
                }
                TermData::Not(_) | TermData::Ite(..) => {}
                _ => return None,
            }
            let mut nested = false;
            let mut child = |term: TermId| {
                budget.charge(64)?;
                let child = usize::try_from(term.0).ok()?;
                // Constructors append after their children. Refuse malformed
                // cyclic/future handles before any recursive term rendering.
                if child >= index {
                    return None;
                }
                nested |= affected[child];
                Some(())
            };
            match data {
                TermData::App(_, args) => {
                    for &term in args {
                        child(term)?;
                    }
                }
                TermData::Not(term) => child(*term)?,
                TermData::Ite(c, t, e) => {
                    for term in [*c, *t, *e] {
                        child(term)?;
                    }
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    child(*body)?;
                    for &term in triggers.iter().flatten() {
                        child(term)?;
                    }
                }
                TermData::Let(bindings, body) => {
                    for (_, term) in bindings {
                        child(*term)?;
                    }
                    child(*body)?;
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return None,
            }
            let mut canonical = None;
            if let TermData::App(Symbol::Named(name), arguments) = data {
                budget.name(name.as_str())?;
                if let Some(constructor) = name.as_str().strip_prefix("is-") {
                    if let Some(info) = self.ctx.exact_datatype_member_info(name.as_str()) {
                        if info.declaration_kind() == DeclarationKind::DatatypeTester {
                            let (carrier, exact_constructor) =
                                self.ctx.constructor_metadata(constructor)?;
                            if self.ctx.is_parametric_datatype_instance(carrier)
                                || !self.ctx.is_live_datatype_carrier(carrier)
                                || self.ctx.sort_surface_name(carrier) != carrier
                                || self
                                    .ctx
                                    .dt_surface_name(exact_constructor)
                                    .unwrap_or(exact_constructor)
                                    != exact_constructor
                                || arguments.len() != 1
                                || self.ctx.terms.sort(term) != &Sort::Bool
                                || info.sort != Sort::Bool
                                || info.arg_sorts.len() != 1
                                || self.ctx.terms.sort(arguments[0]) != &info.arg_sorts[0]
                                || !matches!(&info.arg_sorts[0], Sort::Uninterpreted(name) if name == carrier)
                            {
                                return None;
                            }
                            self.datatype_transport_print_footprint(
                                arguments[0],
                                &result,
                                &mut budget,
                            )?;
                            let argument = ay_proof::format_term_alethe_with_overrides(
                                &self.ctx.terms,
                                arguments[0],
                                &result,
                            );
                            budget.charge(
                                argument
                                    .len()
                                    .checked_add(exact_constructor.len())
                                    .and_then(|n| n.checked_add(64))?,
                            )?;
                            canonical = Some(format!(
                                "((_ is {}) {argument})",
                                quote_symbol(exact_constructor)
                            ));
                            nested = true;
                        }
                    }
                }
            }
            affected[index] = nested;
            if let Some(source) = source {
                budget.charge(source.capacity().checked_mul(2)?.checked_add(8)?)?;
            }
            let old = source.and_then(|source| source.get(&term));
            if nested && canonical.is_none() && old.is_some() {
                self.datatype_transport_print_footprint(term, &result, &mut budget)?;
                canonical = Some(ay_proof::format_term_alethe_with_overrides(
                    &self.ctx.terms,
                    term,
                    &result,
                ));
            }
            if let Some(canonical) = canonical {
                budget.charge(canonical.len().checked_add(64)?)?;
                if old.is_some_and(|old| old != &canonical) {
                    return None;
                }
                result.insert(term, canonical);
            } else if let Some(old) = old {
                budget.charge(old.len().checked_add(64)?)?;
                result.insert(term, old.clone());
            }
        }
        (!stop()).then_some(result)
    }

    fn datatype_transport_print_footprint(
        &self,
        root: TermId,
        overrides: &DetHashMap<TermId, String>,
        budget: &mut Budget,
    ) -> Option<()> {
        let stop = self.make_strict_check_stop();
        let mut pending = vec![(root, 0usize)];
        let mut sorts = BTreeSet::new();
        while let Some((term, depth)) = pending.pop() {
            budget.charge(64)?;
            if depth > MAX_DEPTH || stop() {
                return None;
            }
            self.ctx.terms.entry_stamp(term)?;
            budget.sort(self.ctx.terms.sort(term), &mut sorts)?;
            budget.charge(overrides.capacity().checked_mul(2)?.checked_add(8)?)?;
            if let Some(text) = overrides.get(&term) {
                // Count every expanded occurrence, including a shared term or
                // repeated root. Also retain the native walk: bound-name
                // protection may make the printer decline an override.
                budget.charge(text.len().checked_add(64)?)?;
            }
            match self.ctx.terms.get(term) {
                TermData::Var(name, _) => budget.name(name)?,
                TermData::Const(value) => budget.constant(value)?,
                TermData::App(Symbol::Named(name), args) => {
                    budget.name(name.as_str())?;
                    for &term in args {
                        enqueue_print(&mut pending, budget, term, depth + 1)?;
                    }
                }
                TermData::App(_, _) => return None,
                TermData::Not(term) => enqueue_print(&mut pending, budget, *term, depth + 1)?,
                TermData::Ite(c, t, e) => {
                    for term in [*c, *t, *e] {
                        enqueue_print(&mut pending, budget, term, depth + 1)?;
                    }
                }
                TermData::Forall(variables, body, triggers)
                | TermData::Exists(variables, body, triggers) => {
                    for (name, sort) in variables {
                        budget.name(name)?;
                        budget.sort(sort, &mut sorts)?;
                    }
                    enqueue_print(&mut pending, budget, *body, depth + 1)?;
                    for &term in triggers.iter().flatten() {
                        enqueue_print(&mut pending, budget, term, depth + 1)?;
                    }
                }
                TermData::Let(bindings, body) => {
                    for (name, term) in bindings {
                        budget.name(name)?;
                        enqueue_print(&mut pending, budget, *term, depth + 1)?;
                    }
                    enqueue_print(&mut pending, budget, *body, depth + 1)?;
                }
                _ => return None,
            }
        }
        Some(())
    }

    pub(in crate::executor) fn alethe_datatype_problem_smt2_for(
        &self,
        assertions: &[TermId],
        overrides: Option<&DetHashMap<TermId, String>>,
    ) -> Option<String> {
        self.alethe_datatype_problem_with_constructors(assertions, overrides)
            .map(|(problem, _)| problem)
    }

    /// Carries exactly the live nullary constructors actually emitted in the
    /// paired problem. The proof's immutable premise scope remains separate.
    pub(in crate::executor) fn alethe_datatype_problem_with_constructors(
        &self,
        assertions: &[TermId],
        overrides: Option<&DetHashMap<TermId, String>>,
    ) -> Option<(String, BTreeMap<&str, TermId>)> {
        let stop = self.make_strict_check_stop();
        let mut declared_constants = BTreeMap::new();
        let mut plan = Plan {
            budget: Budget::default(),
            sorts: BTreeSet::new(),
            datatypes: BTreeMap::new(),
            heads: BTreeMap::new(),
        };
        self.datatype_transport_context_footprint(&mut plan.budget)?;
        for (name, info) in self.ctx.symbols_iter() {
            if stop() {
                return None;
            }
            let core = self.ctx.symbol_identity_name(name, info);
            // Definition overlays have already declined in the context
            // preflight. `symbols_iter` supplies only live bindings.
            match info.declaration_kind() {
                DeclarationKind::Uninterpreted => plan.signature(core, info, false)?,
                DeclarationKind::DatatypeConstructor
                | DeclarationKind::DatatypeSelector
                | DeclarationKind::DatatypeTester => plan.signature(core, info, true)?,
                DeclarationKind::Theory if is_builtin_operator(core) => {}
                _ => return None,
            }
        }
        if let Some(overrides) = overrides {
            plan.budget.charge(overrides.capacity())?;
            for text in overrides.values() {
                plan.budget.charge(text.len().checked_add(64)?)?;
            }
        }
        self.datatype_transport_roots(assertions, &mut plan, &stop)?;
        let canonical = self.datatype_problem_spelling_overrides(overrides)?;
        for (term, text) in &canonical {
            plan.budget.charge(text.len().checked_add(64)?)?;
            if overrides.and_then(|table| table.get(term)) != Some(text) {
                return None;
            }
        }

        // Live constructor signatures above have already inventoried all
        // field sort dependencies. One simultaneous group preserves mutual
        // recursion without inventing a plain carrier or a free member head.
        let mut members = BTreeSet::new();
        for &name in &plan.sorts {
            if stop() || self.ctx.sort_surface_name(name) != name {
                return None;
            }
            let Some(constructors) = self.ctx.datatype_constructors(name) else {
                continue;
            };
            if self.ctx.is_parametric_datatype_instance(name)
                || !self.ctx.is_live_datatype_carrier(name)
                || constructors.is_empty()
            {
                return None;
            }
            plan.budget.charge(constructors.len().checked_mul(64)?)?;
            plan.datatypes.insert(name, constructors);
            for constructor in constructors {
                let info = self.ctx.exact_datatype_member_info(constructor)?;
                if self.ctx.dt_surface_name(constructor).unwrap_or(constructor) != constructor
                    || !matches!(&info.sort, Sort::Uninterpreted(carrier) if carrier == name)
                    || !members.insert(plan.exact_member(
                        constructor,
                        info,
                        DeclarationKind::DatatypeConstructor,
                    )?)
                {
                    return None;
                }
                let fields = self.ctx.constructor_selector_info(constructor)?;
                if fields.len() != info.arg_sorts.len() {
                    return None;
                }
                if let Some(term) = info.term.filter(|&term| {
                    fields.is_empty()
                        && self.ctx.terms.entry_stamp(term).is_some()
                        && self.ctx.terms.sort(term) == &info.sort
                        && matches!(self.ctx.terms.get(term), TermData::Var(identity, _) if identity == constructor)
                }) {
                    plan.budget.charge(64)?;
                    declared_constants.insert(constructor.as_str(), term);
                }
                for ((selector, field_sort), argument_sort) in fields.iter().zip(&info.arg_sorts) {
                    let field = self.ctx.exact_datatype_member_info(selector)?;
                    if self.ctx.dt_surface_name(selector).unwrap_or(selector) != selector
                        || field_sort != argument_sort
                        || &field.sort != field_sort
                        || field.arg_sorts.as_slice() != std::slice::from_ref(&info.sort)
                        || !members.insert(plan.exact_member(
                            selector,
                            field,
                            DeclarationKind::DatatypeSelector,
                        )?)
                    {
                        return None;
                    }
                }
                plan.budget.name(constructor)?;
                let tester = format!("is-{constructor}");
                let tester_info = self.ctx.exact_datatype_member_info(&tester)?;
                if tester_info.sort != Sort::Bool
                    || tester_info.arg_sorts.as_slice() != std::slice::from_ref(&info.sort)
                    || !members.insert(plan.exact_member(
                        &tester,
                        tester_info,
                        DeclarationKind::DatatypeTester,
                    )?)
                {
                    return None;
                }
            }
        }
        if plan
            .heads
            .iter()
            .any(|(name, head)| head.datatype && !members.contains(name))
        {
            return None;
        }
        let mut out = String::from("(set-logic ALL)\n");
        for name in plan
            .sorts
            .iter()
            .filter(|name| !plan.datatypes.contains_key(*name))
        {
            push(
                &mut out,
                &format!("(declare-sort {} 0)\n", quote_symbol(name)),
            )?;
        }
        if !plan.datatypes.is_empty() {
            push(&mut out, "(declare-datatypes (")?;
            for name in plan.datatypes.keys() {
                push(&mut out, &format!("({} 0)", quote_symbol(name)))?;
            }
            push(&mut out, ") (")?;
            for constructors in plan.datatypes.values() {
                push(&mut out, "(")?;
                for constructor in *constructors {
                    push(&mut out, &format!("({}", quote_symbol(constructor)))?;
                    for (selector, sort) in self.ctx.constructor_selector_info(constructor)? {
                        push(&mut out, &format!(" ({} ", quote_symbol(selector)))?;
                        write_sort(&mut out, sort)?;
                        push(&mut out, ")")?;
                    }
                    push(&mut out, ")")?;
                }
                push(&mut out, ")")?;
            }
            push(&mut out, "))\n")?;
        }
        for (name, head) in &plan.heads {
            if head.datatype {
                continue;
            }
            push(&mut out, &format!("(declare-fun {} (", quote_symbol(name)))?;
            for (index, sort) in head.arguments.iter().enumerate() {
                if index != 0 {
                    push(&mut out, " ")?;
                }
                write_sort(&mut out, sort)?;
            }
            push(&mut out, ") ")?;
            write_sort(&mut out, head.result)?;
            push(&mut out, ")\n")?;
        }
        for &assertion in assertions {
            if stop() {
                return None;
            }
            let empty = DetHashMap::default();
            self.datatype_transport_print_footprint(
                assertion,
                overrides.unwrap_or(&empty),
                &mut plan.budget,
            )?;
            let rendered = match overrides {
                Some(overrides) => ay_proof::format_term_alethe_with_overrides(
                    &self.ctx.terms,
                    assertion,
                    overrides,
                ),
                None => ay_proof::format_term_alethe(&self.ctx.terms, assertion),
            };
            push(&mut out, "(assert ")?;
            push(&mut out, &rendered)?;
            push(&mut out, ")\n")?;
        }
        push(&mut out, "(check-sat)\n")?;
        (!stop()).then_some((out, declared_constants))
    }

    fn datatype_transport_roots<'a>(
        &'a self,
        assertions: &[TermId],
        plan: &mut Plan<'a>,
        stop: &dyn Fn() -> bool,
    ) -> Option<()> {
        let empty = Arc::new(BTreeMap::new());
        plan.budget.charge(
            assertions
                .len()
                .checked_mul(size_of::<(TermId, Bound<'_>, usize)>())?,
        )?;
        let mut pending: Vec<_> = assertions
            .iter()
            .map(|&term| (term, Arc::clone(&empty), 0usize))
            .collect();
        while let Some((term, bound, depth)) = pending.pop() {
            plan.budget.charge(64)?;
            if depth > MAX_DEPTH || stop() {
                return None;
            }
            self.ctx.terms.entry_stamp(term)?;
            let sort = self.ctx.terms.sort(term);
            plan.budget.sort(sort, &mut plan.sorts)?;
            match self.ctx.terms.get(term) {
                TermData::Var(name, _) => {
                    plan.budget.name(name)?;
                    if let Some(expected) = bound.get(name.as_str()) {
                        if *expected != sort {
                            return None;
                        }
                    } else if let Some(head) = plan.heads.get(name.as_str()) {
                        if !head.arguments.is_empty()
                            || head.result != sort
                            || head.constant != Some(term)
                        {
                            return None;
                        }
                    } else {
                        plan.head(name, std::iter::empty(), sort, None, Some(term), false)?;
                    }
                }
                TermData::Const(value) => plan.budget.constant(value)?,
                TermData::App(Symbol::Named(name), arguments) => {
                    plan.budget.name(name.as_str())?;
                    plan.budget.charge(arguments.len().checked_mul(64)?)?;
                    for &argument in arguments {
                        self.ctx.terms.entry_stamp(argument)?;
                    }
                    if !is_builtin_operator(name.as_str()) {
                        let args = arguments.iter().map(|&term| self.ctx.terms.sort(term));
                        if let Some(head) = plan.heads.get(name.as_str()) {
                            if head.result != sort || !head.arguments.iter().copied().eq(args) {
                                return None;
                            }
                        } else {
                            plan.head(name.as_str(), args, sort, None, None, false)?;
                        }
                    }
                    for &argument in arguments {
                        enqueue(
                            &mut pending,
                            &mut plan.budget,
                            argument,
                            Arc::clone(&bound),
                            depth + 1,
                        )?;
                    }
                }
                TermData::App(_, _) => return None,
                TermData::Not(inner) => {
                    enqueue(&mut pending, &mut plan.budget, *inner, bound, depth + 1)?
                }
                TermData::Ite(c, t, e) => {
                    for term in [*c, *t, *e] {
                        enqueue(
                            &mut pending,
                            &mut plan.budget,
                            term,
                            Arc::clone(&bound),
                            depth + 1,
                        )?;
                    }
                }
                TermData::Forall(variables, body, triggers)
                | TermData::Exists(variables, body, triggers) => {
                    plan.budget.charge(bound.len().checked_mul(64)?)?;
                    let mut nested = (*bound).clone();
                    let mut names = BTreeSet::new();
                    for (name, sort) in variables {
                        plan.budget.name(name)?;
                        plan.budget.sort(sort, &mut plan.sorts)?;
                        if !names.insert(name) {
                            return None;
                        }
                        nested.insert(name.as_str(), sort);
                    }
                    let nested = Arc::new(nested);
                    enqueue(
                        &mut pending,
                        &mut plan.budget,
                        *body,
                        Arc::clone(&nested),
                        depth + 1,
                    )?;
                    for &term in triggers.iter().flatten() {
                        enqueue(
                            &mut pending,
                            &mut plan.budget,
                            term,
                            Arc::clone(&nested),
                            depth + 1,
                        )?;
                    }
                }
                TermData::Let(bindings, body) => {
                    plan.budget.charge(bound.len().checked_mul(64)?)?;
                    let mut nested = (*bound).clone();
                    let mut names = BTreeSet::new();
                    for (name, value) in bindings {
                        plan.budget.name(name)?;
                        self.ctx.terms.entry_stamp(*value)?;
                        if !names.insert(name) {
                            return None;
                        }
                        nested.insert(name.as_str(), self.ctx.terms.sort(*value));
                        enqueue(
                            &mut pending,
                            &mut plan.budget,
                            *value,
                            Arc::clone(&bound),
                            depth + 1,
                        )?;
                    }
                    enqueue(
                        &mut pending,
                        &mut plan.budget,
                        *body,
                        Arc::new(nested),
                        depth + 1,
                    )?;
                }
                _ => return None,
            }
        }
        Some(())
    }
}

#[cfg(test)]
mod tests;
