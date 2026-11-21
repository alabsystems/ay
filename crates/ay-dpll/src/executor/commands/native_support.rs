// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A typed declaration projection for an independently checked native proof.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ay_core::kani_compat::DetHashMap;
use ay_core::term::{Constant, TermData, TermEntryStamp};
use ay_core::{quote_symbol, Sort, Symbol, TermId};
use ay_frontend::{CheckedProjectionBindings, ProjectionBindingRequest};

use crate::executor::proof::native_source_scope::NativeProofSourceScope;
use crate::executor::Executor;
use crate::executor_format::format_sort_surface;

use super::{collect_uninterpreted_sort_names, is_builtin_operator};

const MAX_OCCURRENCES: usize = 262_144;
const MAX_DEPTH: usize = 128;
const MAX_BYTES: usize = 4 * 1024 * 1024;
const MAX_LITERAL_BITS: u64 = 1_048_576;

/// A rendered problem with its positively checked declaration/term bindings.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExternalSupportProblem {
    text: String,
    bindings: CheckedProjectionBindings,
    roots: Vec<TermId>,
    entries: Vec<(TermId, TermEntryStamp)>,
}

impl CheckedExternalSupportProblem {
    pub(in crate::executor) fn text(&self) -> &str {
        &self.text
    }

    pub(in crate::executor) fn surface(&self) -> ay_proof::CarcaraSurface {
        ay_proof::CarcaraSurface::Supported
    }

    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        let should_stop = executor.make_strict_check_stop();
        !should_stop()
            && executor
                .ctx
                .projection_bindings_still_current(&self.bindings, &self.roots)
            && self.entries.iter().all(|(term, entry)| {
                !should_stop() && executor.ctx.terms.entry_stamp(*term).as_ref() == Some(entry)
            })
    }
}

#[derive(Default)]
struct Footprint {
    variables: BTreeMap<String, (TermId, Sort)>,
    functions: BTreeMap<String, ProjectionBindingRequest>,
    entries: BTreeMap<TermId, TermEntryStamp>,
    occurrences: usize,
    bytes: usize,
}

impl Footprint {
    fn charge(&mut self, bytes: usize) -> Option<()> {
        self.bytes = self.bytes.checked_add(bytes)?;
        (self.bytes <= MAX_BYTES).then_some(())
    }

    fn sort(&mut self, sort: &Sort) -> Option<()> {
        let mut pending = vec![(sort, 0usize)];
        while let Some((sort, depth)) = pending.pop() {
            self.occurrences = self.occurrences.checked_add(1)?;
            if self.occurrences > MAX_OCCURRENCES || depth > MAX_DEPTH {
                return None;
            }
            self.charge(std::mem::size_of::<Sort>())?;
            match sort {
                Sort::Bool | Sort::Int | Sort::Real => {}
                Sort::BitVec(bits)
                    if bits.width > 0 && u64::from(bits.width) <= MAX_LITERAL_BITS => {}
                Sort::Array(array) => {
                    pending.push((&array.index_sort, depth + 1));
                    pending.push((&array.element_sort, depth + 1));
                }
                Sort::Uninterpreted(name) => self.charge(name.len())?,
                _ => return None,
            }
        }
        Some(())
    }

    fn clone_scope(&mut self, bound: &BTreeMap<String, Sort>) -> Option<BTreeMap<String, Sort>> {
        for (name, sort) in bound {
            self.charge(name.len())?;
            self.sort(sort)?;
        }
        Some(bound.clone())
    }
}

impl Executor {
    /// Render only declarations needed by the exact selected original roots
    /// and all proof terms. This method issues no proof or subset authority.
    /// The caller must independently check the unchanged proof against both
    /// its complete native source and this selected premise set.
    pub(in crate::executor) fn render_external_support_problem(
        &self,
        selected_roots: &[TermId],
        proof_terms: &[TermId],
        source: &NativeProofSourceScope,
        overrides: Option<&DetHashMap<TermId, String>>,
    ) -> Option<CheckedExternalSupportProblem> {
        if selected_roots.is_empty()
            || !source.is_current_after_proof_growth(self)
            || selected_roots.len().checked_add(proof_terms.len())? > MAX_OCCURRENCES
        {
            return None;
        }
        // A textual override can change the free symbol surface. The first
        // projection codec requires the canonical typed spelling; callers can
        // retry canonical printing, but must not guess declarations from text.
        if overrides.is_some_and(|overrides| !overrides.is_empty()) {
            return None;
        }
        let should_stop = self.make_strict_check_stop();
        let mut footprint = Footprint::default();
        footprint.charge(
            source
                .free_variables()
                .len()
                .checked_mul(std::mem::size_of::<(
                    TermId,
                    &crate::executor::proof::native_source_scope::NativeFreeVariableBinding,
                )>())?,
        )?;
        let original_free: BTreeMap<_, _> = source
            .free_variables()
            .iter()
            .map(|binding| (binding.term, binding))
            .collect();
        let root_count = selected_roots.len().checked_add(proof_terms.len())?;
        footprint.charge(
            root_count.checked_mul(std::mem::size_of::<TermId>().checked_add(
                std::mem::size_of::<(TermId, Arc<BTreeMap<String, Sort>>, usize)>(),
            )?)?,
        )?;
        let mut roots = Vec::with_capacity(root_count);
        roots.extend_from_slice(selected_roots);
        roots.extend_from_slice(proof_terms);
        let empty = Arc::new(BTreeMap::<String, Sort>::new());
        let mut pending: Vec<_> = roots
            .iter()
            .copied()
            .map(|term| (term, Arc::clone(&empty), 0usize))
            .collect();
        while let Some((term, bound, depth)) = pending.pop() {
            footprint.occurrences = footprint.occurrences.checked_add(1)?;
            if footprint.occurrences > MAX_OCCURRENCES || depth > MAX_DEPTH || should_stop() {
                return None;
            }
            let entry = self.ctx.terms.entry_stamp(term)?;
            footprint.entries.insert(term, entry);
            let sort = self.ctx.terms.sort(term);
            footprint.sort(sort)?;
            let mut push = |child, scope| {
                if pending.len() >= MAX_OCCURRENCES {
                    return None;
                }
                pending.push((child, scope, depth + 1));
                Some(())
            };
            match self.ctx.terms.get(term) {
                TermData::Var(name, _) => {
                    footprint.charge(name.len())?;
                    if let Some(binding_sort) = bound.get(name) {
                        if binding_sort != sort {
                            return None;
                        }
                        continue;
                    }
                    let original = original_free.get(&term)?;
                    if original.entry != entry || &original.sort != sort {
                        return None;
                    }
                    if let Some((previous, previous_sort)) = footprint.variables.get(name) {
                        if *previous != term || previous_sort != sort {
                            return None;
                        }
                    } else {
                        footprint
                            .variables
                            .insert(name.clone(), (term, sort.clone()));
                    }
                }
                TermData::Const(constant) => {
                    let bits = match constant {
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
                    footprint.charge(usize::try_from(bits).ok()?.saturating_add(1))?;
                }
                TermData::App(Symbol::Named(name), arguments) => {
                    let name = name.as_str();
                    footprint.charge(name.len())?;
                    if arguments.len() > MAX_OCCURRENCES {
                        return None;
                    }
                    if !is_builtin_operator(name) {
                        footprint
                            .charge(arguments.len().checked_mul(std::mem::size_of::<Sort>())?)?;
                        let mut parameter_sorts = Vec::with_capacity(arguments.len());
                        for &argument in arguments {
                            self.ctx.terms.entry_stamp(argument)?;
                            let argument_sort = self.ctx.terms.sort(argument);
                            footprint.sort(argument_sort)?;
                            parameter_sorts.push(argument_sort.clone());
                        }
                        let request = ProjectionBindingRequest {
                            symbol: Symbol::named(name),
                            parameter_sorts,
                            result_sort: sort.clone(),
                        };
                        if let Some(previous) = footprint.functions.get(name) {
                            if previous != &request {
                                return None;
                            }
                        } else {
                            footprint.functions.insert(name.to_owned(), request);
                        }
                    }
                    for &argument in arguments {
                        push(argument, Arc::clone(&bound))?;
                    }
                }
                TermData::App(_, _) => return None,
                TermData::Not(child) => push(*child, bound)?,
                TermData::Ite(condition, then_term, else_term) => {
                    for child in [*condition, *then_term, *else_term] {
                        push(child, Arc::clone(&bound))?;
                    }
                }
                TermData::Forall(variables, body, triggers)
                | TermData::Exists(variables, body, triggers) => {
                    let mut nested = footprint.clone_scope(&bound)?;
                    let mut names = BTreeSet::new();
                    for (name, sort) in variables {
                        footprint.charge(name.len())?;
                        footprint.sort(sort)?;
                        if !names.insert(name) {
                            return None;
                        }
                        nested.insert(name.clone(), sort.clone());
                    }
                    let nested = Arc::new(nested);
                    push(*body, Arc::clone(&nested))?;
                    for trigger in triggers.iter().flatten() {
                        push(*trigger, Arc::clone(&nested))?;
                    }
                }
                TermData::Let(bindings, body) => {
                    let mut nested = footprint.clone_scope(&bound)?;
                    let mut names = BTreeSet::new();
                    for (name, value) in bindings {
                        footprint.charge(name.len())?;
                        self.ctx.terms.entry_stamp(*value)?;
                        let value_sort = self.ctx.terms.sort(*value);
                        footprint.sort(value_sort)?;
                        if !names.insert(name) {
                            return None;
                        }
                        push(*value, Arc::clone(&bound))?;
                        nested.insert(name.clone(), value_sort.clone());
                    }
                    push(*body, Arc::new(nested))?;
                }
                _ => return None,
            }
        }
        let requests: Vec<_> = footprint.functions.values().cloned().collect();
        let bindings = self
            .ctx
            .check_projection_bindings_with_stop(&roots, &requests, &should_stop)
            .ok()?;
        let mut sorts = BTreeSet::new();
        let mut declarations = BTreeMap::new();
        for (name, (_, sort)) in &footprint.variables {
            if ay_proof::carcara_declaration_gap(name, &[], sort).is_some() {
                return None;
            }
            collect_uninterpreted_sort_names(sort, &mut sorts);
            declarations.insert(
                name.clone(),
                format!(
                    "(declare-const {} {})\n",
                    quote_symbol(name),
                    format_sort_surface(&self.ctx, sort)
                ),
            );
        }
        for (name, request) in &footprint.functions {
            if declarations.contains_key(name)
                || ay_proof::carcara_declaration_gap(
                    name,
                    &request.parameter_sorts,
                    &request.result_sort,
                )
                .is_some()
            {
                return None;
            }
            collect_uninterpreted_sort_names(&request.result_sort, &mut sorts);
            let mut arguments = Vec::new();
            for sort in &request.parameter_sorts {
                collect_uninterpreted_sort_names(sort, &mut sorts);
                arguments.push(format_sort_surface(&self.ctx, sort));
            }
            declarations.insert(
                name.clone(),
                format!(
                    "(declare-fun {} ({}) {})\n",
                    quote_symbol(name),
                    arguments.join(" "),
                    format_sort_surface(&self.ctx, &request.result_sort)
                ),
            );
        }
        let mut text = String::from("(set-logic ALL)\n");
        for sort in sorts {
            if ay_proof::carcara_declaration_gap(&sort, &[], &Sort::Bool).is_some() {
                return None;
            }
            text.push_str(&format!("(declare-sort {} 0)\n", quote_symbol(&sort)));
        }
        for declaration in declarations.into_values() {
            text.push_str(&declaration);
        }
        for &assertion in selected_roots {
            if should_stop() {
                return None;
            }
            text.push_str("(assert ");
            text.push_str(&ay_proof::format_term_alethe(&self.ctx.terms, assertion));
            text.push_str(")\n");
            if text.len() > MAX_BYTES {
                return None;
            }
        }
        text.push_str("(check-sat)\n");
        if should_stop() || !source.is_current_after_proof_growth(self) {
            return None;
        }
        Some(CheckedExternalSupportProblem {
            text,
            bindings,
            roots,
            entries: footprint.entries.into_iter().collect(),
        })
    }
}

#[cfg(test)]
mod tests;
