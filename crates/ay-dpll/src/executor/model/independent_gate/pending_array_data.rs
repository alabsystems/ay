// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete candidate DATA from original, reauthenticated W6 observations.

use super::super::datatype_array_fields::NormalizedDatatypeArrayValue;
use super::super::rendered_dt_limits::model_value_work;
use super::*;
use ay_arrays::{ArrayInterpretation, PendingArrayDefinition};
use ay_core::original_query::{QueryError, WorkBudget};

const MAX_READS: usize = 4096;

fn admit_slot<T>(values: &mut Vec<T>, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    if values.len() == values.capacity() {
        let next = values.len().checked_add(1).ok_or(QueryError::Exhausted)?;
        // Include the whole replacement buffer and its copied old entries,
        // before asking Vec for exactly this next slot.
        work.admit(
            next,
            next.checked_mul(size_of::<T>())
                .ok_or(QueryError::Exhausted)?,
        )?;
        values
            .try_reserve_exact(1)
            .map_err(|_| work.refuse_exhaustion())?;
    }
    Ok(())
}

struct PreparedRead {
    term: TermId,
    stamp: TermEntryStamp,
    index_term: TermId,
    index_stamp: TermEntryStamp,
    point: usize,
}

struct PreparedPoint {
    index: NormalizedDatatypeArrayValue,
    value: NormalizedDatatypeArrayValue,
    index_work: usize,
    value_work: usize,
}

pub(in crate::executor::model) struct PreparedPendingArrayAlias {
    record: PendingArrayDefinition,
    terms: TermStoreSnapshotStamp,
    source: SourceContextStamp,
    reads: Vec<PreparedRead>,
    points: Vec<PreparedPoint>,
    proposal: ArrayInterpretation,
}

impl PreparedPendingArrayAlias {
    pub(in crate::executor::model) fn record(&self) -> PendingArrayDefinition {
        self.record
    }

    pub(in crate::executor::model) fn proposal(&self) -> &ArrayInterpretation {
        &self.proposal
    }

    pub(in crate::executor::model) fn is_current(
        &self,
        exec: &Executor,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        work.charge(
            self.reads
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(QueryError::Exhausted)?,
        )?;
        Ok(self.record.matches_current(&exec.ctx.terms)
            && self.terms == exec.ctx.terms.snapshot_stamp()
            && self.source == exec.ctx.source_context_stamp()
            && exec.recorded_var_substitutions.get(&self.record.source())
                == Some(&self.record.target())
            && self.reads.iter().all(|read| {
                exec.ctx.terms.entry_stamp(read.term) == Some(read.stamp)
                    && exec.ctx.terms.entry_stamp(read.index_term) == Some(read.index_stamp)
            }))
    }
}

fn scalar_index_matches(value: &ModelValue, sort: &Sort) -> bool {
    match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool)
        | (ModelValue::Int(_), Sort::Int)
        | (ModelValue::Real(_), Sort::Real) => true,
        (ModelValue::BitVec { width, value }, Sort::BitVec(expected)) => {
            *width > 0
                && *width == expected.width
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width)
        }
        _ => false,
    }
}

struct RowBuilder {
    points: Vec<PreparedPoint>,
    stores: Vec<(String, String)>,
    default: Option<(String, NormalizedDatatypeArrayValue, usize)>,
}

impl RowBuilder {
    fn new() -> Self {
        Self {
            points: Vec::new(),
            stores: Vec::new(),
            default: None,
        }
    }

    fn row(
        &mut self,
        exec: &Executor,
        index: &ModelValue,
        value: &ModelValue,
        sort: &ay_core::ArraySort,
        work: &mut WorkBudget<'_>,
        semantic: &mut SemanticNormalizationBudget,
    ) -> Result<usize, QueryError> {
        if !scalar_index_matches(index, &sort.index_sort) {
            return Err(QueryError::Invalid(
                "unsupported or mismatched pending array index",
            ));
        }
        let index_work = model_value_work(index).ok_or(QueryError::Exhausted)?;
        let value_work = model_value_work(value).ok_or(QueryError::Exhausted)?;
        let normalized_index = normalize_datatype_array_value(index, semantic)
            .ok_or(QueryError::Invalid("pending array index is not complete"))?;
        let normalized_value = normalize_datatype_array_value(value, semantic)
            .ok_or(QueryError::Invalid("pending array value is not complete"))?;
        let key = exec.pending_array_render_value(index, &sort.index_sort)?;
        let spelling = exec.pending_array_render_value(value, &sort.element_sort)?;
        for (position, ((old_key, _), point)) in self.stores.iter().zip(&self.points).enumerate() {
            work.charge(
                key.len()
                    .checked_add(old_key.len())
                    .and_then(|n| n.checked_add(1))
                    .ok_or(QueryError::Exhausted)?,
            )?;
            if old_key != &key {
                continue;
            }
            work.charge(
                value_work
                    .checked_add(point.value_work)
                    .ok_or(QueryError::Exhausted)?,
            )?;
            if normalized_value != point.value {
                return Err(QueryError::Invalid(
                    "pending aliases disagree at the same evaluated index",
                ));
            }
            return Ok(position);
        }
        if self.points.len() >= MAX_READS {
            return Err(QueryError::Exhausted);
        }
        admit_slot(&mut self.points, work)?;
        admit_slot(&mut self.stores, work)?;
        let position = self.points.len();
        self.points.push(PreparedPoint {
            index: normalized_index,
            value: normalized_value,
            index_work,
            value_work,
        });
        self.stores.push((key, spelling));
        Ok(position)
    }

    fn known_default(
        &mut self,
        exec: &Executor,
        value: &ModelValue,
        sort: &Sort,
        work: &mut WorkBudget<'_>,
        semantic: &mut SemanticNormalizationBudget,
    ) -> Result<(), QueryError> {
        let amount = model_value_work(value).ok_or(QueryError::Exhausted)?;
        let normalized = normalize_datatype_array_value(value, semantic)
            .ok_or(QueryError::Invalid("pending array default is not complete"))?;
        let spelling = exec.pending_array_render_value(value, sort)?;
        if let Some((_, previous, previous_work)) = self.default.as_ref() {
            work.charge(
                amount
                    .checked_add(*previous_work)
                    .ok_or(QueryError::Exhausted)?,
            )?;
            if previous != &normalized {
                return Err(QueryError::Invalid("known pending alias defaults disagree"));
            }
        } else {
            self.default = Some((spelling, normalized, amount));
        }
        Ok(())
    }
}

impl Executor {
    /// Called only during the preparation pass: no candidate interpretation
    /// has been installed, and the private clone differs from the ORIGINAL
    /// model only in this record's temporary pending-reason quarantine.
    pub(in crate::executor::model) fn prepare_pending_array_alias_data(
        &self,
        model: &Model,
        record: PendingArrayDefinition,
        scope: &[TermId],
        work: &mut WorkBudget<'_>,
        semantic: &mut SemanticNormalizationBudget,
    ) -> Result<Option<PreparedPendingArrayAlias>, QueryError> {
        if !record.matches_current(&self.ctx.terms)
            || self.recorded_var_substitutions.get(&record.source()) != Some(&record.target())
            || shared_gate_view_cache_active()
            || !self.ctx.canonical_operator_binding_is_unambiguous("select")
        {
            return Ok(None);
        }
        let Some(arrays) = model.array_model.as_ref() else {
            return Ok(None);
        };
        if arrays.is_withheld(&record.source()) || arrays.is_withheld(&record.target()) {
            return Ok(None);
        }
        let Sort::Array(sort) = self.ctx.terms.sort(record.source()) else {
            return Ok(None);
        };
        let Some(classes) = self.authenticated_datatype_array_field_classes(model) else {
            return Ok(None);
        };
        let count = classes
            .iter()
            .try_fold(scope.len(), |count, class| {
                count.checked_add(class.members.len())
            })
            .ok_or(QueryError::Exhausted)?;
        if count > MAX_READS {
            return Err(QueryError::Exhausted);
        }
        work.admit(
            count,
            count
                .checked_mul(size_of::<TermId>())
                .ok_or(QueryError::Exhausted)?,
        )?;
        let mut census = Vec::with_capacity(count);
        census.extend_from_slice(scope);
        for class in &classes {
            census.extend(class.members.keys().copied());
        }
        let levels = usize::BITS as usize - count.max(1).leading_zeros() as usize;
        work.charge(
            count
                .checked_mul(levels.checked_add(1).ok_or(QueryError::Exhausted)?)
                .ok_or(QueryError::Exhausted)?,
        )?;
        census.sort_unstable();
        census.dedup();
        // This view never installs/exports a shared cache. The recovery entry
        // excludes an active GateViewCacheSession, and public stop callbacks
        // receive no handle to this view or its private leaf caches.
        let view = IndependentModelView::new(self, model);
        view.ensure_def_index().map_err(|_| QueryError::Exhausted)?;
        let evaluator = Evaluator::new(&self.ctx.terms, &view);
        let mut builder = RowBuilder::new();
        // Preserve every effective original row and every known default, even
        // when its array was not marked definition_authoritative. An absent
        // default is fillable; a present partial value is not evidence.
        for term in [record.source(), record.target()] {
            let Some(existing) = arrays.array_values.get(&term) else {
                continue;
            };
            let mut schema = super::super::rendered_dt_limits::SchemaSourceBudget::new();
            for descriptor in existing.index_sort.iter().chain(&existing.element_sort) {
                if !schema.charge_sort(descriptor) {
                    return Err(QueryError::Exhausted);
                }
            }
            work.charge(existing.stores.len())?;
            if existing
                .index_sort
                .as_ref()
                .is_some_and(|index| index != &sort.index_sort)
                || existing
                    .element_sort
                    .as_ref()
                    .is_some_and(|element| element != &sort.element_sort)
            {
                return Ok(None);
            }
            if let Some(spelling) = existing.default.as_ref() {
                let Some(value) = view.parse_leaf(spelling, &sort.element_sort) else {
                    return Ok(None);
                };
                builder.known_default(self, &value, &sort.element_sort, work, semantic)?;
            }
            let mut seen_keys: Vec<String> = Vec::new();
            for (key, spelling) in &existing.stores {
                let Some(index) = view.parse_leaf(key, &sort.index_sort) else {
                    return Ok(None);
                };
                let canonical = self.pending_array_render_value(&index, &sort.index_sort)?;
                let mut shadowed = false;
                for seen in &seen_keys {
                    work.charge(
                        canonical
                            .len()
                            .checked_add(seen.len())
                            .and_then(|n| n.checked_add(1))
                            .ok_or(QueryError::Exhausted)?,
                    )?;
                    if seen == &canonical {
                        shadowed = true;
                        break;
                    }
                }
                if shadowed {
                    continue;
                }
                admit_slot(&mut seen_keys, work)?;
                seen_keys.push(canonical);
                let Some(value) = view.parse_leaf(spelling, &sort.element_sort) else {
                    return Ok(None);
                };
                builder.row(self, &index, &value, sort, work, semantic)?;
            }
        }
        let mut reads = Vec::new();
        for read in census {
            work.charge(1)?;
            let TermData::App(symbol, args) = self.ctx.terms.get(read) else {
                continue;
            };
            if symbol.name() != "select"
                || args.len() != 2
                || (args[0] != record.source() && args[0] != record.target())
            {
                continue;
            }
            work.charge(classes.len())?;
            let Some(class) = classes
                .iter()
                .find(|class| class.members.contains_key(&read))
            else {
                return Ok(None);
            };
            work.charge(class.carrier.len())?;
            if class.cell_sort != sort.element_sort
                || self.ctx.terms.entry_stamp(read) != class.members.get(&read).copied()
                || model
                    .euf_model
                    .as_ref()
                    .and_then(|euf| euf.term_values.get(&read))
                    != Some(&class.carrier)
            {
                return Ok(None);
            }
            let EvalOutcome::Value(index) = evaluator.evaluate(args[1]) else {
                return Ok(None);
            };
            let point = builder.row(self, &index, &class.value, sort, work, semantic)?;
            admit_slot(&mut reads, work)?;
            reads.push(PreparedRead {
                term: read,
                stamp: self
                    .ctx
                    .terms
                    .entry_stamp(read)
                    .ok_or(QueryError::Invalid("missing pending read"))?,
                index_term: args[1],
                index_stamp: self
                    .ctx
                    .terms
                    .entry_stamp(args[1])
                    .ok_or(QueryError::Invalid("missing pending index"))?,
                point,
            });
        }
        if reads.is_empty() {
            return Ok(None);
        }
        let default = match builder.default {
            Some((spelling, _, _)) => spelling,
            None => {
                let point = reads[0].point;
                let spelling = &builder.stores[point].1;
                work.admit(spelling.len(), spelling.len())?;
                spelling.clone()
            }
        };
        let mut schema = super::super::rendered_dt_limits::SchemaSourceBudget::new();
        if !schema.charge_sort(&sort.index_sort) || !schema.charge_sort(&sort.element_sort) {
            return Err(QueryError::Exhausted);
        }
        Ok(Some(PreparedPendingArrayAlias {
            record,
            terms: self.ctx.terms.snapshot_stamp(),
            source: self.ctx.source_context_stamp(),
            reads,
            points: builder.points,
            proposal: ArrayInterpretation {
                default: Some(default),
                stores: builder.stores,
                index_sort: Some(sort.index_sort.clone()),
                element_sort: Some(sort.element_sort.clone()),
            },
        }))
    }

    pub(in crate::executor::model) fn pending_array_prepared_reads_match(
        &self,
        model: &Model,
        prepared: &PreparedPendingArrayAlias,
        work: &mut WorkBudget<'_>,
        semantic: &mut SemanticNormalizationBudget,
    ) -> bool {
        if !matches!(prepared.is_current(self, work), Ok(true)) || shared_gate_view_cache_active() {
            return false;
        }
        let view = IndependentModelView::new(self, model);
        if view.ensure_def_index().is_err() {
            return false;
        }
        let evaluator = Evaluator::new(&self.ctx.terms, &view);
        for read in &prepared.reads {
            if work.charge(1).is_err() {
                return false;
            }
            let point = &prepared.points[read.point];
            let EvalOutcome::Value(index) = evaluator.evaluate(read.index_term) else {
                return false;
            };
            let Some(index_work) = model_value_work(&index) else {
                return false;
            };
            let Some(index_work) = index_work.checked_add(point.index_work) else {
                return false;
            };
            if work.charge(index_work).is_err() {
                return false;
            }
            if normalize_datatype_array_value(&index, semantic).as_ref() != Some(&point.index) {
                return false;
            }
            let EvalOutcome::Value(value @ ModelValue::Datatype { .. }) =
                evaluator.evaluate(read.term)
            else {
                return false;
            };
            let Some(value_work) = model_value_work(&value) else {
                return false;
            };
            let Some(value_work) = value_work.checked_add(point.value_work) else {
                return false;
            };
            if work.charge(value_work).is_err() {
                return false;
            }
            if normalize_datatype_array_value(&value, semantic).as_ref() != Some(&point.value) {
                return false;
            }
        }
        !prepared.reads.is_empty() && self.evaluation_stopped_gate_verdict().is_none()
    }
}

#[cfg(test)]
mod tests;
