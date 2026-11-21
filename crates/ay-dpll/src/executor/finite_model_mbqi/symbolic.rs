// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-authored total-function proposals. Choosing an interpretation adds
//! no assertion: every original universal, residual and model gate is owed.

use ay_core::{Sort, Symbol, TermData, TermId};
use ay_frontend::{CheckedProjectionBinding, ProjectionBindingRequest};

use super::interpretation::{Interpretation, UfTable, MAX_TABLE_ROWS};
use super::Executor;
use crate::executor::model::{SymbolicAdmission, SymbolicUfDefinition, SymbolicUfModel};

mod admission;
mod substitution;
#[cfg(test)]
mod tests;

const MAX_DEFINITIONS: usize = 64;

struct RawDefinition {
    binding: CheckedProjectionBinding,
    names: Vec<String>,
    body: TermId,
}

impl Executor {
    pub(super) fn qmc_symbolic_candidate(
        &mut self,
        roots: &[TermId],
        owner: &SymbolicAdmission,
    ) -> Option<SymbolicUfModel> {
        // This optional producer never uses the current mutable working stack
        // as a substitute for the retained public input. Temporary assumptions
        // still belong to the later FULL query checks, not to this seed list.
        let authored = self.independent_gate_authored_assertions.as_ref()?;
        if authored.len() > MAX_TABLE_ROWS || roots.len() > MAX_TABLE_ROWS {
            return None;
        }
        let mut pending = Vec::new();
        owner.reserve(&mut pending, authored.len())?;
        pending.extend_from_slice(authored);
        let mut raw: Vec<Option<RawDefinition>> = Vec::new();
        while let Some(source) = pending.pop() {
            if !owner.pay(1, 0) || self.ctx.terms.entry_stamp(source).is_none() {
                return None;
            }
            if let TermData::App(Symbol::Named(name), children) = self.ctx.terms.get(source) {
                owner
                    .pay(self.ctx.terms.declared_function_lookup_work(name.len())?, 0)
                    .then_some(())?;
                if name == "and" && !self.ctx.terms.is_declared_function(name) {
                    owner.reserve(&mut pending, children.len())?;
                    pending.extend_from_slice(children);
                    continue;
                }
            }
            if !matches!(self.ctx.terms.get(source), TermData::Forall(..)) {
                continue;
            }
            if let Some(definition) = self.qmc_symbolic_definition(source, owner)? {
                if raw.len() >= MAX_DEFINITIONS {
                    return None;
                }
                if !owner.pay(raw.len().saturating_mul(512), 0)
                    || raw
                        .iter()
                        .flatten()
                        .any(|earlier| earlier.binding.symbol() == definition.binding.symbol())
                {
                    return None;
                }
                owner.reserve(&mut raw, 1)?;
                raw.push(Some(definition));
            }
        }
        if raw.is_empty() {
            return None;
        }
        let mut definitions = Vec::new();
        owner.reserve(&mut definitions, raw.len())?;
        // No search choice grants anything. A source function must be closed
        // over its actual formals and already-compiled symbolic dependencies.
        // A stalled pass means a cycle or an unresolved dependency, not an
        // excuse to use a constant interpretation or a sampled equation.
        while definitions.len() < raw.len() {
            let mut progressed = false;
            for slot in &mut raw {
                let Some(definition) = slot.as_ref() else {
                    continue;
                };
                if !substitution::dependencies_ready(
                    self,
                    definition.body,
                    &definitions,
                    &definition.names,
                    owner,
                )? {
                    continue;
                }
                let definition = slot.take()?;
                let mut parameters = Vec::new();
                owner.reserve(&mut parameters, definition.names.len())?;
                for sort in definition.binding.parameter_sorts() {
                    let parameter = self
                        .ctx
                        .terms
                        .try_fresh_var_with_progress(
                            "__ay_symbolic_arg",
                            sort,
                            &mut |work, bytes| owner.pay(work, bytes),
                        )
                        .ok()?;
                    parameters.push(parameter);
                }
                let body = substitution::compile(
                    &mut self.ctx.terms,
                    definition.body,
                    &definition.names,
                    &parameters,
                    &definitions,
                    owner,
                )?;
                admission::body(&self.ctx.terms, body, &parameters, owner)?;
                let rendered_body = admission::render(&self.ctx.terms, body, owner)?;
                definitions.push(SymbolicUfDefinition {
                    binding: definition.binding,
                    parameters,
                    body,
                    rendered_body,
                });
                progressed = true;
            }
            if !progressed {
                return None;
            }
        }
        let mut retained_roots = Vec::new();
        owner.reserve(&mut retained_roots, roots.len())?;
        retained_roots.extend_from_slice(roots);
        SymbolicUfModel::from_prepared(self, retained_roots, definitions, owner)
    }

    fn qmc_symbolic_definition(
        &self,
        source: TermId,
        owner: &SymbolicAdmission,
    ) -> Option<Option<RawDefinition>> {
        let mut binders: Vec<(String, Sort)> = Vec::new();
        let mut body = source;
        while let TermData::Forall(vars, inner, _) = self.ctx.terms.get(body) {
            if binders.len().checked_add(vars.len())? > MAX_TABLE_ROWS {
                return None;
            }
            owner.reserve(&mut binders, vars.len())?;
            for (name, sort) in vars {
                if !owner.pay(
                    binders.len().saturating_mul(name.len().saturating_add(256)),
                    0,
                ) || binders.iter().any(|(earlier, _)| earlier == name)
                {
                    return None;
                }
                binders.push((
                    admission::text(name, owner)?,
                    admission::copy_sort(sort, owner)?,
                ));
            }
            body = *inner;
            self.ctx.terms.entry_stamp(body)?;
        }
        if binders.is_empty() {
            return Some(None);
        }
        let mut choices = Vec::new();
        owner.reserve(&mut choices, 2)?;
        owner
            .pay(self.ctx.terms.declared_function_lookup_work(1)?, 0)
            .then_some(())?;
        match self.ctx.terms.get(body) {
            TermData::App(Symbol::Named(name), args)
                if name == "=" && args.len() == 2 && !self.ctx.terms.is_declared_function(name) =>
            {
                choices.extend([(args[0], args[1]), (args[1], args[0])]);
            }
            TermData::Not(inner) => choices.push((*inner, self.ctx.terms.false_term())),
            _ => choices.push((body, self.ctx.terms.true_term())),
        }
        for (head, value) in choices {
            let Some((symbol, names, parameter_sorts)) =
                admission::formal_head(&self.ctx.terms, head, &binders, owner)?
            else {
                continue;
            };
            let result_sort = admission::copy_sort(self.ctx.terms.sort(head), owner)?;
            if self.ctx.terms.entry_stamp(value).is_none()
                || self.ctx.terms.sort(value) != &result_sort
            {
                return None;
            }
            let request = ProjectionBindingRequest {
                symbol,
                parameter_sorts,
                result_sort,
            };
            // Exact binding validation scans physical source tables and clones
            // the selected signature. Price both before invoking that existing
            // authority API; unrelated signature payloads are never copied.
            // The returned fee already admits the full fixed sequence of
            // semantic identity/kind scans, rather than a renewed allowance.
            let _ = crate::executor::model::symbolic_source_inventory_work(
                self,
                owner,
                request.symbol.name().len(),
            )?;
            let mut bytes = request.symbol.name().len();
            for (surface, info) in self.ctx.model_recovery_symbol_iter() {
                if self.ctx.symbol_identity_name(surface, info) != request.symbol.name() {
                    continue;
                }
                if info.arg_sorts.len() > MAX_TABLE_ROWS {
                    return None;
                }
                for sort in info.arg_sorts.iter().chain(std::iter::once(&info.sort)) {
                    bytes = bytes.checked_add(admission::sort(sort, owner, 0)?)?;
                }
            }
            owner
                .pay(bytes.checked_mul(4)?, bytes.checked_mul(4)?)
                .then_some(())?;
            // An exact live ordinary declaration is required. Native operators,
            // constructors, macros and retired same-spelling bindings decline.
            let Ok(binding) = self.ctx.check_projection_declaration(&request) else {
                continue;
            };
            admission::source_body(&self.ctx.terms, value, &names, owner)?;
            return Some(Some(RawDefinition {
                binding,
                names,
                body: value,
            }));
        }
        Some(None)
    }
}

impl Interpretation {
    pub(super) fn substitute_symbolic(
        &self,
        terms: &mut ay_core::TermStore,
        root: TermId,
    ) -> Option<TermId> {
        if self.symbolic.is_empty() {
            return Some(self.substitute(terms, root));
        }
        let owner = self.symbolic_owner.as_ref()?;
        substitution::instantiate_query(terms, root, &self.symbolic, &self.tables, owner)
    }
}
