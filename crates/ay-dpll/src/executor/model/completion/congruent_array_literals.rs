// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Optional total constant-UF candidates, never SAT/proof authority.

use super::*;
use crate::executor::model::evaluation_copies::{self, EvaluationCopyScope};
use crate::executor::model::residual_completion::{ConstantArrayFunction, ConstantArrayFunctions};
use ay_core::term::{reserve_counted, TermConstructionAdmission, TermStore};
use std::sync::Arc;

impl Executor {
    pub(in crate::executor::model) fn is_ordinary_array_function_application(
        &self,
        term: TermId,
    ) -> Result<bool, String> {
        let TermData::App(Symbol::Named(symbol), args) = self.ctx.terms.get(term) else {
            return Ok(false);
        };
        if args.is_empty() || !self.is_opaque_array_valued_app(term) {
            return Ok(false);
        }
        if ay_frontend::is_canonical_theory_operator_identity(symbol.as_ref()) {
            return Ok(false);
        }
        if !evaluation_copies::pay(symbol.len(), 0) || !evaluation_copies::validate(self) {
            return Err("array function classification refused".to_owned());
        }
        let info = self
            .ctx
            .symbol_info_by_identity(symbol.as_ref())
            .ok_or_else(|| "array function declaration is unavailable".to_owned())?;
        Ok(self.ctx.effective_declaration_kind(info.declaration_id())
            == Some(DeclarationKind::Uninterpreted))
    }
    pub(in crate::executor::model) fn has_array_function_declarations(
        &self,
    ) -> Result<bool, crate::executor_types::UnknownOrigin> {
        let attempt = self.evaluation_attempt();
        let source = self.ctx.source_context_stamp();
        let guard = ay_core::resource::current_guard();
        let progress = || {
            use crate::executor_types::UnknownOrigin;
            use ay_core::resource::Exhausted;
            self.poll_evaluation_stop()?;
            if let Some(guard) = &guard {
                guard.tick(1).map_err(|reason| {
                    self.record_evaluation_stop(match reason {
                        Exhausted::Cancelled => UnknownOrigin::InterruptFlag,
                        Exhausted::Deadline | Exhausted::Cpu => UnknownOrigin::SolveDeadline,
                        Exhausted::Rlimit => UnknownOrigin::DeterministicResourceBudget,
                        Exhausted::Memory => UnknownOrigin::MemoryBudget,
                    })
                })?;
            }
            self.poll_evaluation_stop()?;
            if !attempt.is_same_attempt(&self.evaluation_attempt())
                || source != self.ctx.source_context_stamp()
            {
                return Err(self.record_evaluation_stop(
                    crate::executor_types::UnknownOrigin::IncompleteSolverLane,
                ));
            }
            Ok(())
        };
        progress()?;
        if self.array_functions_absent.borrow().as_ref() == Some(&source) {
            return Ok(false);
        }
        for (_, info) in self.ctx.symbol_iter() {
            progress()?;
            if !info.arg_sorts.is_empty()
                && matches!(info.sort, Sort::Array(_))
                && self.ctx.effective_declaration_kind(info.declaration_id())
                    == Some(DeclarationKind::Uninterpreted)
            {
                return Ok(true);
            }
        }
        progress()?;
        // No callback runs while borrowing this cache. A stamp includes both
        // context identity and revision, so registration/pop/reset/foreign
        // snapshots cannot turn this absence observation into authorization.
        *self.array_functions_absent.borrow_mut() = Some(source);
        Ok(false)
    }

    pub(in crate::executor::model) fn check_coherent_array_function_read(
        &self,
        model: &Model,
        root: TermId,
        scope: Option<&EvaluationCopyScope>,
    ) -> Result<Option<ay_model_check::ModelValue>, String> {
        let Some(scope) = scope else { return Ok(None) };
        let mut reads_function = false;
        let scratch = scope
            .temporary_admission(self)
            .map_err(|origin| format!("{origin:?}"))?;
        let owner: &dyn TermConstructionAdmission = &scratch;
        let mut pending = Vec::new();
        let mut visited = HashMap::default();
        reserve_counted(&mut pending, 1, owner).map_err(|e| e.to_string())?;
        pending.push(root);
        while let Some(term) = pending.pop() {
            owner.admit(1, 0).map_err(|e| e.to_string())?;
            if !evaluation_copies::validate(self) {
                return Err("array read source changed".to_owned());
            }
            if visited.contains_key(&term) {
                continue;
            }
            ay_core::term::reserve_map_counted(&mut visited, 1, owner)
                .map_err(|e| e.to_string())?;
            if !evaluation_copies::validate(self) {
                return Err("array read source changed".to_owned());
            }
            visited.insert(term, ());
            if model.projection_ufs.has_interpretations() {
                if let TermData::App(symbol, args) = self.ctx.terms.get(term) {
                    owner
                        .admit(symbol.name().len(), 0)
                        .map_err(|e| e.to_string())?;
                    for sort in std::iter::once(self.ctx.terms.sort(term))
                        .chain(args.iter().map(|arg| self.ctx.terms.sort(*arg)))
                    {
                        TermStore::inspect_sort_with_progress(sort, &mut |w, b| {
                            owner.admit(w, b).is_ok()
                        })
                        .map_err(|e| format!("{e:?}"))?;
                    }
                    if let Some(index) = model
                        .projection_ufs
                        .projected_argument_for_application_borrowed(
                            symbol,
                            &self.ctx.terms,
                            args,
                            self.ctx.terms.sort(term),
                        )
                        .map_err(|_| "array projection signature mismatch".to_owned())?
                    {
                        let selected = *args.get(index).ok_or("invalid array projection")?;
                        reserve_counted(&mut pending, 1, owner).map_err(|e| e.to_string())?;
                        if !evaluation_copies::validate(self) {
                            return Err("array read source changed".to_owned());
                        }
                        pending.push(selected);
                        continue;
                    }
                }
            }
            if self.is_ordinary_array_function_application(term)? {
                reads_function = true;
                let owned = model
                    .constant_array_value(self, term)
                    .map_err(|_| "array function DATA is stale")?
                    .is_some()
                    || model.functional_array_value(self, term)?.is_some()
                    || self
                        .const_interp_witness_value(model, term)
                        .map_err(|_| "array function certificate is stale")?
                        .is_some()
                    || self.has_printed_array_function_interpretation(model, term);
                if !owned {
                    return Err(
                        "array-valued function has no coherent committed interpretation".to_owned(),
                    );
                }
                // The retained/certified reader owns this whole application;
                // it must not be replaced by independently guessed values for
                // arguments its total interpretation does not need to expose.
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => {
                    reserve_counted(&mut pending, args.len(), owner).map_err(|e| e.to_string())?;
                    if !evaluation_copies::validate(self) {
                        return Err("array read source changed".to_owned());
                    }
                    pending.extend_from_slice(args);
                }
                TermData::Not(term) => {
                    reserve_counted(&mut pending, 1, owner).map_err(|e| e.to_string())?;
                    if !evaluation_copies::validate(self) {
                        return Err("array read source changed".to_owned());
                    }
                    pending.push(*term);
                }
                TermData::Ite(c, t, e) => {
                    reserve_counted(&mut pending, 3, owner).map_err(|e| e.to_string())?;
                    if !evaluation_copies::validate(self) {
                        return Err("array read source changed".to_owned());
                    }
                    pending.extend([*c, *t, *e]);
                }
                TermData::Let(bindings, body) => {
                    reserve_counted(
                        &mut pending,
                        bindings.len().checked_add(1).ok_or("array read overflow")?,
                        owner,
                    )
                    .map_err(|e| e.to_string())?;
                    if !evaluation_copies::validate(self) {
                        return Err("array read source changed".to_owned());
                    }
                    pending.extend(bindings.iter().map(|(_, term)| *term));
                    pending.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    reserve_counted(&mut pending, 1, owner).map_err(|e| e.to_string())?;
                    if !evaluation_copies::validate(self) {
                        return Err("array read source changed".to_owned());
                    }
                    pending.push(*body);
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return Err("unsupported array read expression".to_owned()),
            }
        }
        if !evaluation_copies::validate(self) {
            return Err("array read source changed".to_owned());
        }
        if !reads_function {
            return Ok(None);
        }
        // Use the same value-keyed total UF interpretation as independent
        // confirmation. A legacy per-application select pin is not a second
        // interpretation of this whole public query.
        let value = self
            .independent_completed_model_value(model, root)
            .ok_or("array function query has no coherent committed value")?;
        if !evaluation_copies::validate(self) {
            return Err("array read source changed".to_owned());
        }
        Ok(Some(value))
    }

    pub(super) fn complete_congruent_array_literals(&mut self, model: &mut Model) {
        if model.functional_arrays.is_some()
            || model.residual_arrays.is_some()
            || model.projection_ufs.has_interpretations()
            || !model.certified_const_interp_entries().is_empty()
            || !model.certified_total_ufs.by_symbol.is_empty()
            || !model.certified_total_ufs.ground_pins.is_empty()
            || !model.formula_neutral_function_default_entries().is_empty()
            || model.quantified_confirmation_seal.is_installed()
            || model.quantified_grant_model_seal.is_installed()
        {
            return;
        }
        // Borrow the existing operation's counter/stop before acquiring a copy
        // arena. No-array queries do not inherit an unrelated FP copy ceiling.
        if self.has_array_function_declarations() != Ok(true) {
            return;
        }
        let used = self.evaluation_attempt().functional_work_counter();
        let Ok(scope) = EvaluationCopyScope::enter(self) else {
            return;
        };
        let admission = scope.read_admission(self);
        let owner: &dyn TermConstructionAdmission = &admission;
        let Some(definitions) = self.closed_array_definition_sources(owner) else {
            return;
        };
        // Group once, rather than repeatedly rescanning identical RHS rows.
        // None records a competing definition; it never selects a winner.
        let mut by_symbol = HashMap::default();
        let mut groups: Vec<(TermId, Option<TermId>)> = Vec::new();
        for (app, rhs) in definitions {
            if self.declared_array_application(app, owner).is_none() {
                continue;
            }
            let TermData::App(symbol, _) = self.ctx.terms.get(app) else {
                continue;
            };
            if owner
                .admit(symbol.name().len().saturating_mul(2), 0)
                .is_err()
            {
                return;
            }
            if let Some(&index) = by_symbol.get(symbol) {
                let (_, previous): &mut (TermId, Option<TermId>) = &mut groups[index];
                if *previous != Some(rhs) {
                    *previous = None;
                }
                continue;
            }
            if ay_core::term::reserve_map_counted(&mut by_symbol, 1, owner).is_err()
                || reserve_counted(&mut groups, 1, owner).is_err()
                || !evaluation_copies::validate(self)
            {
                return;
            }
            by_symbol.insert(symbol.clone(), groups.len());
            groups.push((app, Some(rhs)));
        }
        let mut functions = HashMap::default();
        for (app, rhs) in groups {
            let Some(rhs) = rhs else { continue };
            let Some((_, args)) = self.declared_array_application(app, owner) else {
                continue;
            };
            if !self.is_closed_array_literal(rhs, owner) {
                continue;
            }
            // The independent evaluator admits literal materialization under
            // THIS original owner before its variable-sized allocations.
            let Some(value @ ay_model_check::ModelValue::Array(_)) =
                self.independent_completed_model_value(model, rhs)
            else {
                continue;
            };
            let mut arguments = Vec::new();
            if reserve_counted(&mut arguments, args.len(), owner).is_err() {
                return;
            }
            for &arg in args {
                let sort = self.ctx.terms.sort(arg);
                if TermStore::inspect_sort_with_progress(sort, &mut |w, b| {
                    owner.admit(w, b).is_ok()
                })
                .is_err()
                    || !evaluation_copies::validate(self)
                {
                    return;
                }
                arguments.push(sort.clone());
            }
            let TermData::App(symbol, _) = self.ctx.terms.get(app) else {
                continue;
            };
            if ay_core::term::reserve_map_counted(&mut functions, 1, owner).is_err()
                || owner
                    .admit(
                        symbol.name().len().saturating_mul(2),
                        std::mem::size_of::<ay_model_check::ModelValue>()
                            + 2 * std::mem::size_of::<usize>()
                            + symbol.name().len(),
                    )
                    .is_err()
                || !evaluation_copies::validate(self)
            {
                return;
            }
            functions.insert(
                symbol.name().to_owned(),
                ConstantArrayFunction {
                    arguments,
                    result: self.ctx.terms.sort(app).clone(),
                    value: Arc::new(value),
                },
            );
        }
        if functions.is_empty() {
            return;
        }
        if owner
            .admit(
                1,
                std::mem::size_of::<ConstantArrayFunctions>() + 2 * std::mem::size_of::<usize>(),
            )
            .is_err()
        {
            return;
        }
        let Some(memory) = scope.retain_data_memory(self) else {
            return;
        };
        if !evaluation_copies::validate(self) {
            return;
        }
        let data = Arc::new(ConstantArrayFunctions {
            source: self.ctx.source_context_stamp(),
            query: self.query_authority_epoch.clone(),
            store: self.ctx.terms.snapshot_stamp(),
            functions,
            used,
            memory,
        });
        model.install_constant_array_candidate(&self.ctx, data);
        // A total constant function is a possible witness, NOT an entailed
        // interpretation. Independently replay every original root/assumption.
        let accepted = self.completed_gap_model_accepted(model);
        if !evaluation_copies::validate(self) || !accepted {
            model.remove_constant_array_candidate();
        }
    }

    fn declared_array_application<'a>(
        &'a self,
        term: TermId,
        owner: &dyn TermConstructionAdmission,
    ) -> Option<(&'a str, &'a [TermId])> {
        let TermData::App(Symbol::Named(symbol), args) = self.ctx.terms.get(term) else {
            return None;
        };
        owner.admit(symbol.len(), 0).ok()?;
        if !matches!(self.ctx.terms.sort(term), Sort::Array(_))
            || ay_frontend::is_canonical_theory_operator_identity(symbol.as_ref())
        {
            return None;
        }
        let info = self.ctx.symbol_info_by_identity(symbol.as_ref())?;
        if self.ctx.effective_declaration_kind(info.declaration_id())
            != Some(DeclarationKind::Uninterpreted)
        {
            return None;
        }
        let mut inspect = |work, bytes| owner.admit(work, bytes).is_ok();
        TermStore::inspect_sort_with_progress(&info.sort, &mut inspect).ok()?;
        TermStore::inspect_sort_with_progress(self.ctx.terms.sort(term), &mut inspect).ok()?;
        if info.arg_sorts.len() != args.len() || info.sort != *self.ctx.terms.sort(term) {
            return None;
        }
        for (sort, &arg) in info.arg_sorts.iter().zip(args) {
            TermStore::inspect_sort_with_progress(sort, &mut inspect).ok()?;
            TermStore::inspect_sort_with_progress(self.ctx.terms.sort(arg), &mut inspect).ok()?;
            if sort != self.ctx.terms.sort(arg) {
                return None;
            }
        }
        Some((symbol.as_ref(), args))
    }

    fn closed_array_definition_sources(
        &self,
        owner: &dyn TermConstructionAdmission,
    ) -> Option<Vec<(TermId, TermId)>> {
        let mut pending = Vec::new();
        let mut definitions = Vec::new();
        for root in self.definitional_constraint_terms() {
            reserve_counted(&mut pending, 1, owner).ok()?;
            pending.push(root);
        }
        while let Some(root) = pending.pop() {
            owner.admit(1, 0).ok()?;
            if !evaluation_copies::validate(self) {
                return None;
            }
            let TermData::App(symbol, args) = self.ctx.terms.get(root) else {
                continue;
            };
            if symbol.name() == "and" {
                reserve_counted(&mut pending, args.len(), owner).ok()?;
                pending.extend_from_slice(args);
            } else if symbol.name() == "=" && args.len() == 2 {
                for (app, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                    if self.declared_array_application(app, owner).is_some()
                        && self.ctx.terms.sort(app) == self.ctx.terms.sort(rhs)
                    {
                        reserve_counted(&mut definitions, 1, owner).ok()?;
                        definitions.push((app, rhs));
                    }
                }
            }
        }
        Some(definitions)
    }

    fn is_closed_array_literal(&self, root: TermId, owner: &dyn TermConstructionAdmission) -> bool {
        let Sort::Array(sort) = self.ctx.terms.sort(root) else {
            return false;
        };
        let mut current = root;
        loop {
            if owner.admit(1, 0).is_err()
                || !evaluation_copies::validate(self)
                || self.ctx.terms.sort(current) != self.ctx.terms.sort(root)
            {
                return false;
            }
            let TermData::App(symbol, args) = self.ctx.terms.get(current) else {
                return false;
            };
            if symbol.name() == "const-array" && args.len() == 1 {
                return matches!(self.ctx.terms.get(args[0]), TermData::Const(_))
                    && self.ctx.terms.sort(args[0]) == &sort.element_sort;
            }
            if symbol.name() != "store"
                || args.len() != 3
                || self.ctx.terms.sort(args[1]) != &sort.index_sort
                || self.ctx.terms.sort(args[2]) != &sort.element_sort
                || !matches!(self.ctx.terms.get(args[1]), TermData::Const(_))
                || !matches!(self.ctx.terms.get(args[2]), TermData::Const(_))
            {
                return false;
            }
            current = args[0];
        }
    }
}

#[cfg(test)]
mod tests;
