// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate-only late recovery of exact datatype-element array aliases.

use super::super::independent_gate::PreparedPendingArrayAlias;
use super::super::recovery_admission::RecoveryScope;
use super::*;
use ay_arrays::{ArrayModel, PendingArrayDefinition};
use ay_core::original_query::{QueryError, WorkBudget};
use ay_core::term::Constant;

const MAX_PENDING: usize = 1024;
const MAX_SCOPE: usize = 4096;
const MAX_WORK: u64 = 1_000_000;
const MAX_COPY_BYTES: usize = 64 * 1024 * 1024;

mod rendered_value;

impl Executor {
    /// A private DATA transaction after typed DT construction. No SAT token,
    /// root authority or proof is produced here. The resulting candidate must
    /// still pass all remaining completion and the original final gates.
    pub(super) fn recover_pending_datatype_array_aliases(
        &self,
        model: &mut Model,
        extra_roots: &[TermId],
    ) -> usize {
        let Some(arrays) = model.array_model.as_ref() else {
            return 0;
        };
        if arrays.pending_definitions.is_empty()
            || arrays.pending_definitions.len() > MAX_PENDING
            || model.dt_array_field_classes.is_empty()
            || model.residual_arrays.is_some()
            || model.functional_arrays.is_some()
            || model.fp_model.is_some()
            || model.string_model.is_some()
            || model.seq_model.is_some()
            || !model.materialized_scalar_functions.is_empty()
            || !model.certified_const_interp_entries().is_empty()
            || !model.certified_total_ufs.by_symbol.is_empty()
            || !model.certified_total_ufs.ground_pins.is_empty()
            || model.projection_ufs.has_interpretations()
            || !model.formula_neutral_function_default_entries().is_empty()
            || super::super::scoped_term_evaluation_override_active()
            || self.evaluation_stop_origin().is_some()
            || super::super::independent_gate::shared_gate_view_cache_active()
            || self.external_stop_reason().is_some()
            || !self.bulk_state_clone_fits_memory()
        {
            return 0;
        }

        // Fresh parser/view budgets join this owned aggregate scope. Their
        // internal traversals and the explicit DATA copies below debit the
        // same live query guard; a failed retry never refills this ledger.
        let Some(recovery_scope) = RecoveryScope::enter(self, MAX_WORK as usize, MAX_COPY_BYTES)
        else {
            return 0;
        };
        let aggregate = recovery_scope.admission();
        let mut admission = |units: usize, bytes: usize| {
            aggregate
                .pay(units, bytes)
                .then_some(())
                .ok_or(QueryError::Exhausted)
        };
        let mut work = WorkBudget::with_admission(MAX_WORK, &mut admission);
        let Some(scope) = self.pending_array_authored_scope(&mut work) else {
            return 0;
        };
        let mut records = Vec::new();
        if work
            .admit(
                arrays.pending_definitions.len(),
                arrays
                    .pending_definitions
                    .len()
                    .saturating_mul(std::mem::size_of::<PendingArrayDefinition>()),
            )
            .is_err()
        {
            return 0;
        }
        for (&source, &record) in &arrays.pending_definitions {
            if !record.matches_current(&self.ctx.terms)
                || source != record.source()
                || self.recorded_var_substitutions.get(&source) != Some(&record.target())
            {
                return 0;
            }
            let target = record.target();
            if scope.binary_search(&source).is_err()
                || scope.binary_search(&target).is_err()
                || arrays.read_conflicted.contains(&source)
                || arrays.read_conflicted.contains(&target)
            {
                return 0;
            }
            let Sort::Array(sort) = self.ctx.terms.sort(source) else {
                return 0;
            };
            if matches!(self.ctx.terms.get(target), TermData::Var(_, _))
                && self.datatype_sort_carries_array_field(&sort.element_sort)
            {
                records.push(record);
            }
        }
        if records.is_empty() {
            return 0;
        }
        if self
            .pending_array_inventory_admission(model, extra_roots, &mut work)
            .is_err()
        {
            return 0;
        }
        records.sort_by_key(|record| (record.source(), record.target()));
        let Ok(candidate) = arrays.try_clone_with_budget(&mut work) else {
            return 0;
        };
        self.with_pending_array_candidate(
            model,
            candidate,
            |candidate| {
                self.build_pending_array_alias_candidate(
                    candidate,
                    extra_roots,
                    &scope,
                    &records,
                    &mut work,
                )
            },
            || {
                aggregate.pay(0, 0)
                    && super::super::recovery_admission::RecoveryAdmission::current_for(self)
                        .is_some()
                    && self.external_stop_reason().is_none()
            },
        )
    }

    fn with_pending_array_candidate(
        &self,
        model: &mut Model,
        candidate: ArrayModel,
        build: impl FnOnce(&mut Model) -> Result<usize, QueryError>,
        admitted: impl FnOnce() -> bool,
    ) -> usize {
        let saved_assignment = self.dt_egraph_assignment.replace(None);
        // Keep identity-sensitive authority parked before the private witness
        // changes. Default seals are empty; moving them preserves the exact
        // original identities for decline and unwind, unlike cloning Model.
        let saved_confirmation = std::mem::take(&mut model.quantified_confirmation_seal);
        let saved_grant = std::mem::take(&mut model.quantified_grant_model_seal);
        let saved_cegqi_epoch = model.certified_total_ufs.cegqi_recompletion_epoch.take();
        let original = model.array_model.replace(candidate);
        super::super::eval_memo_clear();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let changed = build(model)?;
            if !admitted() {
                return Err(QueryError::Exhausted);
            }
            Ok(changed)
        }));
        let accepted = matches!(&result, Ok(Ok(changed)) if *changed > 0);
        if accepted {
            model.revoke_all_quantified_model_seals();
            self.dt_egraph_assignment.replace(None);
        } else {
            model.array_model = original;
            model.quantified_confirmation_seal = saved_confirmation;
            model.quantified_grant_model_seal = saved_grant;
            model.certified_total_ufs.cegqi_recompletion_epoch = saved_cegqi_epoch;
            self.dt_egraph_assignment.replace(saved_assignment);
        }
        super::super::eval_memo_clear();
        match result {
            Ok(Ok(changed)) if accepted => changed,
            Ok(_) => 0,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    fn build_pending_array_alias_candidate(
        &self,
        model: &mut Model,
        extra_roots: &[TermId],
        scope: &[TermId],
        records: &[PendingArrayDefinition],
        work: &mut WorkBudget<'_>,
    ) -> Result<usize, QueryError> {
        self.pending_array_inventory_admission(model, extra_roots, work)?;
        let edges = self.collect_pending_array_dependency_edges(model, extra_roots);
        let mut semantic = super::super::datatype_array_fields::SemanticNormalizationBudget::new();
        // Prepare ALL observations from the original value/authority rows
        // before installing ANY candidate interpretation. Only the per-record
        // pending quarantine changes during this read-only preparation pass.
        work.admit(
            records.len(),
            records
                .len()
                .checked_mul(std::mem::size_of::<PreparedPendingArrayAlias>())
                .ok_or(QueryError::Exhausted)?,
        )?;
        let mut prepared = Vec::with_capacity(records.len());
        for &record in records {
            work.charge(1)?;
            let source = record.source();
            let target = record.target();
            let Some(arrays) = model.array_model.as_mut() else {
                return Err(QueryError::Invalid("missing preparation array data"));
            };
            if arrays.pending_definitions.get(&source) != Some(&record)
                || arrays.read_conflicted.contains(&source)
                || arrays.read_conflicted.contains(&target)
                || !record.matches_current(&self.ctx.terms)
            {
                continue;
            }
            arrays.pending_definitions.remove(&source);
            self.refresh_pending_array_dependency_mask(model, &edges, work)?;
            self.pending_array_mutation_boundary();
            let input =
                (|| {
                    if model.array_model.as_ref().is_none_or(|arrays| {
                        arrays.is_withheld(&source) || arrays.is_withheld(&target)
                    }) {
                        return Ok(None);
                    }
                    self.pending_array_inventory_admission(model, extra_roots, work)?;
                    self.prepare_pending_array_alias_data(model, record, scope, work, &mut semantic)
                })();
            model
                .array_model
                .as_mut()
                .ok_or(QueryError::Invalid("preparation array data"))?
                .pending_definitions
                .insert(source, record);
            self.refresh_pending_array_dependency_mask(model, &edges, work)?;
            self.pending_array_mutation_boundary();
            if let Some(input) = input? {
                prepared.push(input);
            }
        }
        work.admit(
            records.len(),
            records
                .len()
                .checked_mul(std::mem::size_of::<&PreparedPendingArrayAlias>())
                .ok_or(QueryError::Exhausted)?,
        )?;
        let mut completed = Vec::with_capacity(records.len());
        for _ in 0..prepared.len() {
            let mut moved = false;
            for input in &prepared {
                work.charge(1)?;
                let record = input.record();
                let source = record.source();
                let target = record.target();
                if !input.is_current(self, work)? {
                    return Err(QueryError::Invalid("stale pending read data"));
                }
                let Some(arrays) = model.array_model.as_mut() else {
                    return Err(QueryError::Invalid("missing candidate array data"));
                };
                if !arrays.pending_definitions.contains_key(&source) {
                    continue;
                }
                if arrays.read_conflicted.contains(&target)
                    || arrays.read_conflicted.contains(&source)
                    || !record.matches_current(&self.ctx.terms)
                {
                    continue;
                }
                // This removal is private speculation, not a discharge grant.
                // Failure restores the exact pending record; transaction
                // decline/panic restores the complete original array object.
                arrays.pending_definitions.remove(&source);
                self.refresh_pending_array_dependency_mask(model, &edges, work)?;
                self.pending_array_mutation_boundary();
                if model
                    .array_model
                    .as_ref()
                    .is_none_or(|arrays| arrays.is_withheld(&source) || arrays.is_withheld(&target))
                {
                    model
                        .array_model
                        .as_mut()
                        .unwrap()
                        .pending_definitions
                        .insert(source, record);
                    self.refresh_pending_array_dependency_mask(model, &edges, work)?;
                    self.pending_array_mutation_boundary();
                    continue;
                }
                let Sort::Array(sort) = self.ctx.terms.sort(source) else {
                    return Err(QueryError::Invalid("pending source is not an array"));
                };
                let mut candidate = input.proposal().try_clone_with_budget(work)?;
                self.pending_array_inventory_admission(model, extra_roots, work)?;
                let exact = self.exact_datatype_cell_completions(model, extra_roots);
                let arrays = model
                    .array_model
                    .as_ref()
                    .ok_or(QueryError::Invalid("array data"))?;
                self.pending_array_merge_admission(
                    &candidate,
                    arrays.array_values.get(&target),
                    work,
                )?;
                candidate = self
                    .merge_array_completion_candidate(
                        &exact,
                        arrays.array_values.get(&target),
                        candidate,
                        sort,
                        ExistingArrayDefaultPolicy::Require,
                        ExistingArrayCellPolicy::Authoritative,
                    )
                    .map_err(|()| QueryError::Invalid("target array authority disagrees"))?;
                if arrays.definition_authoritative.contains(&source) {
                    self.pending_array_merge_admission(
                        &candidate,
                        arrays.array_values.get(&source),
                        work,
                    )?;
                    candidate = self
                        .merge_array_completion_candidate(
                            &exact,
                            arrays.array_values.get(&source),
                            candidate,
                            sort,
                            ExistingArrayDefaultPolicy::Require,
                            ExistingArrayCellPolicy::Authoritative,
                        )
                        .map_err(|()| QueryError::Invalid("source array authority disagrees"))?;
                }
                let source_value = candidate.try_clone_with_budget(work)?;
                let target_value = candidate.try_clone_with_budget(work)?;
                let arrays = model
                    .array_model
                    .as_mut()
                    .ok_or(QueryError::Invalid("array data"))?;
                arrays.array_values.insert(source, source_value);
                arrays.array_values.insert(target, target_value);
                self.refresh_pending_array_dependency_mask(model, &edges, work)?;
                completed.push(input);
                moved = true;
                self.pending_array_mutation_boundary();
            }
            if !moved {
                break;
            }
        }
        for input in &completed {
            self.pending_array_inventory_admission(model, extra_roots, work)?;
            if !self.pending_array_prepared_reads_match(model, input, work, &mut semantic) {
                return Err(QueryError::Invalid(
                    "pending alias lacks complete active-read evidence",
                ));
            }
        }
        Ok(completed.len())
    }

    fn pending_array_mutation_boundary(&self) {
        self.dt_egraph_assignment.replace(None);
        super::super::eval_memo_clear();
    }

    fn pending_array_merge_admission(
        &self,
        candidate: &ArrayInterpretation,
        existing: Option<&ArrayInterpretation>,
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        use super::super::rendered_dt_limits::SchemaSourceBudget;
        let mut rows = 0usize;
        let mut bytes = 0usize;
        for interpretation in std::iter::once(candidate).chain(existing) {
            rows = rows
                .checked_add(interpretation.stores.len())
                .ok_or(QueryError::Exhausted)?;
            bytes = bytes
                .checked_add(interpretation.default.as_ref().map_or(0, String::len))
                .ok_or(QueryError::Exhausted)?;
            work.charge(interpretation.stores.len())?;
            for (key, value) in &interpretation.stores {
                bytes = bytes
                    .checked_add(key.len())
                    .and_then(|n| n.checked_add(value.len()))
                    .ok_or(QueryError::Exhausted)?;
            }
            let mut schema = SchemaSourceBudget::new();
            for sort in interpretation
                .index_sort
                .iter()
                .chain(&interpretation.element_sort)
            {
                if !schema.charge_sort(sort) {
                    return Err(QueryError::Exhausted);
                }
            }
        }
        // The existing merge scans accumulated rows for each candidate row.
        // Charge complete string-comparison work as well as copied storage
        // before entering that quadratic legacy loop.
        let visits = rows
            .checked_add(1)
            .and_then(|n| n.checked_mul(bytes.checked_add(rows)?))
            .ok_or(QueryError::Exhausted)?;
        let storage = rows
            .checked_mul(std::mem::size_of::<(String, String)>())
            .and_then(|n| n.checked_add(bytes))
            .ok_or(QueryError::Exhausted)?;
        work.admit(visits, storage)
    }

    fn refresh_pending_array_dependency_mask(
        &self,
        model: &mut Model,
        edges: &[(TermId, TermId)],
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        let records = model
            .array_model
            .as_ref()
            .map_or(0, |arrays| arrays.pending_definitions.len());
        // Adjacency, work stack and result are each bounded by this exact
        // borrowed inventory before the existing graph builder allocates.
        let entries = edges
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(records))
            .ok_or(QueryError::Exhausted)?;
        work.admit(
            entries,
            entries.checked_mul(64).ok_or(QueryError::Exhausted)?,
        )?;
        let mask = self.pending_array_dependency_mask(model, edges);
        model
            .array_model
            .as_mut()
            .ok_or(QueryError::Invalid("array data"))?
            .pending_definition_dependents = mask;
        self.pending_array_mutation_boundary();
        Ok(())
    }

    pub(super) fn pending_array_dependency_mask(
        &self,
        model: &Model,
        edges: &[(TermId, TermId)],
    ) -> HashSet<TermId> {
        let seeds = model
            .array_model
            .as_ref()
            .map_or_else(HashSet::default, |arrays| {
                arrays.pending_definitions.keys().copied().collect()
            });
        self.propagate_array_completion_taint(edges, &seeds, true)
    }

    /// Prepay the actual arena nodes/argument edges and all declaration/model
    /// payloads that the legacy builders below may scan or clone. Nested local
    /// schema/value/parser budgets additionally charge their actual visits.
    fn pending_array_inventory_admission(
        &self,
        model: &Model,
        extra_roots: &[TermId],
        work: &mut WorkBudget<'_>,
    ) -> Result<(), QueryError> {
        use super::super::rendered_dt_limits::{model_value_work, SchemaSourceBudget};
        for roots in [
            self.ctx.assertions.as_slice(),
            extra_roots,
            self.independent_gate_authored_assertions
                .as_deref()
                .unwrap_or(&[]),
            self.self_check_authored_assertions
                .as_deref()
                .unwrap_or(&[]),
            self.last_assumptions.as_deref().unwrap_or(&[]),
            self.lane_model_pin_roots.as_slice(),
        ] {
            work.admit(
                roots.len(),
                roots
                    .len()
                    .checked_mul(std::mem::size_of::<TermId>())
                    .ok_or(QueryError::Exhausted)?,
            )?;
        }
        work.admit(
            self.recorded_var_substitutions.allocation_size(),
            self.recorded_var_substitutions.allocation_size(),
        )?;
        work.charge(self.recorded_var_substitutions.len())?;
        work.charge(self.ctx.terms.len())?;
        for term in self.ctx.terms.term_ids() {
            let mut schema = SchemaSourceBudget::new();
            if !schema.charge_sort(self.ctx.terms.sort(term)) {
                return Err(QueryError::Exhausted);
            }
            let (edges, bytes) = match self.ctx.terms.get(term) {
                TermData::App(symbol, args) => (args.len(), symbol.name().len()),
                TermData::Var(name, _) => (0, name.len()),
                TermData::Const(Constant::String(value)) => (0, value.len()),
                TermData::Const(Constant::Int(value))
                | TermData::Const(Constant::BitVec { value, .. }) => (
                    0,
                    usize::try_from(value.bits()).map_err(|_| QueryError::Exhausted)?,
                ),
                TermData::Const(Constant::Rational(value)) => (
                    0,
                    usize::try_from(
                        value
                            .0
                            .numer()
                            .bits()
                            .saturating_add(value.0.denom().bits()),
                    )
                    .map_err(|_| QueryError::Exhausted)?,
                ),
                TermData::Const(Constant::Bool(_)) => (0, 1),
                TermData::Not(_) => (1, 0),
                TermData::Ite(_, _, _) => (3, 0),
                _ => return Err(QueryError::Invalid("unsupported recovery arena term")),
            };
            let storage = edges
                .checked_mul(std::mem::size_of::<TermId>())
                .and_then(|n| n.checked_add(bytes))
                .ok_or(QueryError::Exhausted)?;
            work.admit(
                edges.checked_add(bytes).ok_or(QueryError::Exhausted)?,
                storage,
            )?;
        }
        for (name, info) in self.ctx.symbol_iter() {
            work.admit(
                name.len()
                    .checked_add(info.arg_sorts.len())
                    .ok_or(QueryError::Exhausted)?,
                name.len(),
            )?;
            let mut schema = SchemaSourceBudget::new();
            if !schema.charge_sort(&info.sort)
                || info.arg_sorts.iter().any(|sort| !schema.charge_sort(sort))
            {
                return Err(QueryError::Exhausted);
            }
        }
        if let Some(euf) = model.euf_model.as_ref() {
            work.charge(euf.term_values.allocation_size())?;
            for value in euf.term_values.values() {
                work.admit(value.len(), value.len())?;
            }
        }
        work.charge(model.dt_ground.allocation_size())?;
        for value in model.dt_ground.values() {
            model_value_work(value).ok_or(QueryError::Exhausted)?;
        }
        work.admit(
            model.dt_array_field_classes.len(),
            model
                .dt_array_field_classes
                .len()
                .checked_mul(std::mem::size_of::<
                    super::super::datatype_array_fields::ExactDatatypeArrayClassAuthority,
                >())
                .ok_or(QueryError::Exhausted)?,
        )?;
        for authority in &model.dt_array_field_classes {
            let mut schema = SchemaSourceBudget::new();
            if !schema.charge_sort(&authority.cell_sort)
                || !schema.charge_name(authority.carrier.len())
            {
                return Err(QueryError::Exhausted);
            }
            work.admit(
                authority.members.allocation_size(),
                authority.members.allocation_size(),
            )?;
            work.admit(
                authority.unobserved_fields.allocation_size(),
                authority.unobserved_fields.allocation_size(),
            )?;
        }
        Ok(())
    }

    fn pending_array_authored_scope(&self, work: &mut WorkBudget<'_>) -> Option<Vec<TermId>> {
        let roots = self
            .independent_gate_authored_assertions
            .as_deref()
            .unwrap_or(&self.ctx.assertions);
        let assumptions = self.last_assumptions.as_deref().unwrap_or(&[]);
        if roots.len().checked_add(assumptions.len())? > MAX_SCOPE {
            return None;
        }
        work.admit(MAX_SCOPE, MAX_SCOPE.checked_mul(64)?).ok()?;
        let mut seen = HashSet::default();
        let mut stack = Vec::with_capacity(MAX_SCOPE);
        stack.extend_from_slice(roots);
        stack.extend_from_slice(assumptions);
        while let Some(term) = stack.pop() {
            work.charge(1).ok()?;
            self.ctx.terms.entry_stamp(term)?;
            if seen.contains(&term) {
                continue;
            }
            if seen.len() >= MAX_SCOPE {
                return None;
            }
            seen.insert(term);
            match self.ctx.terms.get(term) {
                TermData::App(_, args) => {
                    if stack.len().checked_add(args.len())? > MAX_SCOPE {
                        return None;
                    }
                    work.charge(args.len()).ok()?;
                    stack.extend_from_slice(args);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    if stack.len().checked_add(3)? > MAX_SCOPE {
                        return None;
                    }
                    stack.extend([*c, *t, *e]);
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return None,
            }
        }
        let mut result: Vec<_> = seen.into_iter().collect();
        result.sort_unstable();
        Some(result)
    }
}

#[cfg(test)]
mod tests;
