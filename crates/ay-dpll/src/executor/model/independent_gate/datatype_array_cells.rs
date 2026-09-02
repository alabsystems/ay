// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, authenticated datatype values carried in array cells.

use std::collections::{HashMap, HashSet};

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermId};
use ay_model_check::ModelValue;

use super::super::datatype_array_fields::{
    normalize_datatype_array_value, SemanticNormalizationBudget,
};
use super::super::datatype_cell_authority::exact_datatype_carrier_token;
use super::super::rendered_dt_guard::RenderedDatatypeGuard;
use super::super::rendered_dt_limits::{model_value_work, MAX_RENDERED_DT_BYTES};
use super::IndependentModelView;

/// One unique, structurally typed datatype value per exact cell spelling.
/// `None` poisons a spelling for which the fixed model supplied two different
/// constructor trees. Both the raw EUF carrier (`@D!n`) and the exact rendered
/// tree are indexed, so array extraction and completion may use either spelling
/// without handing equality two encodings of the same semantic value.
pub(super) type ExactDatatypeCellValues =
    HashMap<Sort, HashMap<String, Option<ExactDatatypeCellValue>>>;

#[derive(Clone)]
pub(super) struct ExactDatatypeCellValue {
    pub(super) rendered: String,
    pub(super) value: ModelValue,
}

pub(super) fn merge_exact_datatype_cell_value(
    values: &mut ExactDatatypeCellValues,
    sort: &Sort,
    spelling: &str,
    candidate: &ExactDatatypeCellValue,
) {
    let slot = values
        .entry(sort.clone())
        .or_default()
        .entry(spelling.to_string())
        .or_insert_with(|| Some(candidate.clone()));
    if slot
        .as_ref()
        .is_some_and(|existing| existing.rendered != candidate.rendered)
    {
        *slot = None;
    }
}

impl IndependentModelView<'_> {
    /// Resolve one array-cell spelling only when Phase 5 produced a unique,
    /// exactly typed constructor tree for that spelling's same-sort EUF class.
    /// This deliberately runs before the generic scalar parser collapses a
    /// datatype carrier to `ModelValue::Uninterpreted`.
    pub(super) fn exact_datatype_cell_value(
        &self,
        spelling: &str,
        sort: &Sort,
    ) -> Option<ModelValue> {
        const MAX_WORK: usize = 4 * 1_024 * 1_024;

        if spelling.len() > MAX_RENDERED_DT_BYTES {
            return None;
        }
        let values = self
            .exact_datatype_cells
            .get_or_init(|| self.build_exact_datatype_cell_values());
        let entries = values.get(sort)?;
        if let Some(entry) = entries.get(spelling) {
            return entry.as_ref().map(|entry| entry.value.clone());
        }
        if !self.exec.datatype_sort_carries_array_field(sort)
            || !self.datatype_guard().is_exact_array_cell(sort)
        {
            return None;
        }
        let candidate_value =
            self.exec
                .parse_rendered_dt_value_cached(spelling, sort, self.datatype_guard())?;
        let mut work = model_value_work(&candidate_value)?;
        let mut semantic_budget = SemanticNormalizationBudget::new();
        let candidate = normalize_datatype_array_value(&candidate_value, &mut semantic_budget)?;
        work = work.checked_add(spelling.len())?;
        if work > MAX_WORK {
            return None;
        }
        let mut seen = HashSet::new();
        let mut best: Option<&ExactDatatypeCellValue> = None;
        for entry in entries.values().filter_map(Option::as_ref) {
            if !seen.insert(entry.rendered.as_str()) {
                continue;
            }
            work = work
                .checked_add(model_value_work(&entry.value)?)?
                .checked_add(entry.rendered.len())?;
            if work > MAX_WORK {
                return None;
            }
            let normalized_entry =
                normalize_datatype_array_value(&entry.value, &mut semantic_budget)?;
            if candidate == normalized_entry && best.is_none_or(|old| entry.rendered < old.rendered)
            {
                best = Some(entry);
            }
        }
        best.map(|entry| entry.value.clone())
    }

    /// Resolve one live structured datatype occurrence through its current EUF
    /// carrier and the fully reauthenticated exact map. Stored birth stamps are
    /// certificate anchors, not an exhaustive census of congruent terms.
    pub(super) fn exact_datatype_cell_value_for_term(
        &self,
        term: TermId,
        sort: &Sort,
    ) -> Option<ModelValue> {
        self.exec.ctx.terms.entry_stamp(term)?;
        let carrier = self.model.euf_model.as_ref()?.term_values.get(&term)?;
        self.exact_datatype_cell_value(carrier, sort)
    }

    /// Seed exact cell normalization from the current W6 inventory only after
    /// its whole-class field evidence has been revalidated. The returned keys
    /// protect those current carriers from stale, non-inventoried `dt_ground`
    /// rows in the legacy normalization pass below.
    fn install_authenticated_datatype_array_cells(
        &self,
        values: &mut ExactDatatypeCellValues,
        guard: &RenderedDatatypeGuard,
        work: &mut usize,
    ) -> Option<HashMap<Sort, HashSet<String>>> {
        const MAX_WORK: usize = 4 * 1_024 * 1_024;

        if self.model.dt_array_field_classes.is_empty() {
            return Some(HashMap::new());
        }
        let classes = self
            .exec
            .authenticated_datatype_array_field_classes(self.model)?;
        let mut protected: HashMap<Sort, HashSet<String>> = HashMap::new();
        for class in classes {
            if !self.structured_datatype_value_matches_sort(&class.value, &class.cell_sort, guard) {
                return None;
            }
            let value_work = model_value_work(&class.value)?;
            let rendered = self
                .exec
                .format_gate_model_value(&class.value, &class.cell_sort)?;
            *work = work
                .checked_add(value_work)?
                .checked_add(rendered.len())?
                .checked_add(class.carrier.len())?;
            if *work > MAX_WORK {
                return None;
            }
            let entry = ExactDatatypeCellValue {
                rendered: rendered.clone(),
                value: class.value,
            };
            merge_exact_datatype_cell_value(values, &class.cell_sort, &rendered, &entry);
            merge_exact_datatype_cell_value(values, &class.cell_sort, &class.carrier, &entry);
            protected
                .entry(class.cell_sort)
                .or_default()
                .insert(class.carrier);
        }
        Some(protected)
    }

    fn build_exact_datatype_cell_values(&self) -> ExactDatatypeCellValues {
        const MAX_GROUND: usize = 1_024;
        const MAX_WORK: usize = 4 * 1_024 * 1_024;

        let mut values = ExactDatatypeCellValues::new();
        let Some(euf) = self.model.euf_model.as_ref() else {
            return values;
        };
        let guard = self.datatype_guard();
        if !guard.is_bounded() {
            return values;
        }
        let mut work = 0usize;
        let Some(protected) =
            self.install_authenticated_datatype_array_cells(&mut values, guard, &mut work)
        else {
            return ExactDatatypeCellValues::new();
        };
        // W6 authentication above is already charged exclusively to its
        // current authored-query closure. Preserve those exact entries even if
        // unrelated generated rows made the legacy global model tables large.
        // Only the compatibility import below scans `dt_ground`, so its own
        // bounded fallback may decline without erasing authenticated W6 cells.
        if self.model.dt_ground.len() > MAX_GROUND {
            return values;
        }
        let mut constructor_tokens = DetHashSet::default();
        for (_, constructors) in self.exec.ctx.datatype_iter() {
            for constructor in constructors {
                constructor_tokens.insert(constructor.clone());
                constructor_tokens.insert(self.exec.dt_surface(constructor).to_string());
            }
        }
        // Keep the compatibility import transactional. Authenticated W6 rows
        // already in `values` remain usable if this unrelated legacy scan
        // exhausts its aggregate budget, and no prefix of the legacy map gains
        // authority unless the complete bounded scan succeeds.
        let mut legacy_values = ExactDatatypeCellValues::new();
        for (&term, value) in &self.model.dt_ground {
            if self.exec.ctx.terms.entry_stamp(term).is_none() {
                continue;
            }
            let sort = self.exec.ctx.terms.sort(term);
            let carrier = euf.term_values.get(&term);
            if carrier.is_some_and(|carrier| {
                protected
                    .get(sort)
                    .is_some_and(|carriers| carriers.contains(carrier))
            }) {
                continue;
            }
            // A datatype with array-valued fields is never admitted through
            // this legacy dt_ground normalization pass. Its only structured
            // producer is the fully authenticated stamped inventory above.
            if self.exec.datatype_sort_carries_array_field(sort) {
                continue;
            }
            let registered = guard.is_registered(sort);
            let shape_matches =
                registered && self.structured_datatype_value_matches_sort(value, sort, guard);
            if !shape_matches {
                continue;
            }
            let Some(value_work) = model_value_work(value) else {
                continue;
            };
            let Some(rendered) = self.exec.format_gate_model_value(value, sort) else {
                continue;
            };
            let Some(next_work) = work
                .checked_add(value_work)
                .and_then(|next| next.checked_add(rendered.len()))
            else {
                return values;
            };
            if next_work > MAX_WORK {
                return values;
            }
            work = next_work;
            let entry = ExactDatatypeCellValue {
                rendered: rendered.clone(),
                value: value.clone(),
            };
            merge_exact_datatype_cell_value(&mut legacy_values, sort, &rendered, &entry);

            let Some(carrier) = carrier else {
                continue;
            };
            if exact_datatype_carrier_token(guard, &constructor_tokens, sort, carrier) {
                let Some(next_work) = work.checked_add(carrier.len()) else {
                    return values;
                };
                if next_work > MAX_WORK {
                    return values;
                }
                work = next_work;
                merge_exact_datatype_cell_value(&mut legacy_values, sort, carrier, &entry);
            }
        }
        for (sort, entries) in legacy_values {
            for (spelling, entry) in entries {
                if let Some(entry) = entry {
                    merge_exact_datatype_cell_value(&mut values, &sort, &spelling, &entry);
                } else {
                    values
                        .entry(sort.clone())
                        .or_default()
                        .insert(spelling, None);
                }
            }
        }
        values
    }

    /// Re-check constructor owner, arity, every field sort, and all nested
    /// container cells before an opaque carrier can be normalized. The walk is
    /// bounded independently of the construction phase and rejects every
    /// unsupported or mismatched shape.
    fn structured_datatype_value_matches_sort(
        &self,
        root: &ModelValue,
        root_sort: &Sort,
        guard: &RenderedDatatypeGuard,
    ) -> bool {
        const MAX_NODES: usize = 1_024;
        const MAX_DEPTH: usize = 32;

        let mut stack = vec![(root, root_sort.clone(), 0usize)];
        let mut nodes = 0usize;
        while let Some((value, sort, depth)) = stack.pop() {
            if depth > MAX_DEPTH {
                return false;
            }
            nodes = match nodes.checked_add(1) {
                Some(next) if next <= MAX_NODES => next,
                _ => return false,
            };
            if let Some(expected_datatype) = guard.datatype_name(&sort) {
                let ModelValue::Datatype { ctor, args } = value else {
                    return false;
                };
                let Some((actual_datatype, internal_ctor)) = self.exec.ctx.is_constructor(ctor)
                else {
                    return false;
                };
                if actual_datatype != expected_datatype || internal_ctor.as_str() != ctor.as_str() {
                    return false;
                }
                let Some(fields) = self.exec.ctx.constructor_selector_info(ctor) else {
                    return false;
                };
                if fields.len() != args.len()
                    || stack
                        .len()
                        .checked_add(args.len())
                        .is_none_or(|pending| pending > MAX_NODES)
                {
                    return false;
                }
                stack.extend(
                    args.iter()
                        .zip(fields)
                        .map(|(arg, (_, field_sort))| (arg, field_sort.clone(), depth + 1)),
                );
                continue;
            }
            match (value, &sort) {
                (ModelValue::Bool(_), Sort::Bool)
                | (ModelValue::Int(_), Sort::Int)
                | (ModelValue::Real(_), Sort::Real)
                | (ModelValue::Str(_), Sort::String)
                | (ModelValue::Uninterpreted(_), Sort::Uninterpreted(_)) => {}
                (ModelValue::BitVec { width, value }, Sort::BitVec(bitvec))
                    if *width == bitvec.width
                        && value.sign() != num_bigint::Sign::Minus
                        && value.bits() <= u64::from(*width) => {}
                (ModelValue::Array(array), Sort::Array(array_sort)) => {
                    let extra = match array
                        .store
                        .len()
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(1))
                    {
                        Some(extra) => extra,
                        None => return false,
                    };
                    if stack
                        .len()
                        .checked_add(extra)
                        .is_none_or(|pending| pending > MAX_NODES)
                    {
                        return false;
                    }
                    stack.push((&array.default, array_sort.element_sort.clone(), depth + 1));
                    for (index, cell) in &array.store {
                        stack.push((index, array_sort.index_sort.clone(), depth + 1));
                        stack.push((cell, array_sort.element_sort.clone(), depth + 1));
                    }
                }
                (ModelValue::Seq(elements), Sort::Seq(element_sort)) => {
                    if stack
                        .len()
                        .checked_add(elements.len())
                        .is_none_or(|pending| pending > MAX_NODES)
                    {
                        return false;
                    }
                    stack.extend(
                        elements
                            .iter()
                            .map(|element| (element, element_sort.as_ref().clone(), depth + 1)),
                    );
                }
                _ => return false,
            }
        }
        true
    }
}
