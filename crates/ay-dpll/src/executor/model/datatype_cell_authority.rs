// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact class authority for datatype-valued array cells.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::Sort;

use super::rendered_dt_guard::RenderedDatatypeGuard;
use super::Model;
use crate::executor::Executor;

const MAX_DATATYPE_CELL_AUTHORITY_WORK: usize = 4 * 1024 * 1024;

/// One prevalidated structured rendering per exact datatype carrier class.
/// `None` marks a poisoned class whose same-sort ground rows disagree.
pub(super) type ExactDatatypeCellCompletions = HashMap<Sort, HashMap<String, Option<String>>>;

impl Executor {
    /// Build immutable datatype-cell authority once per array-completion pass.
    /// Every later merge lookup is O(1), including bounded fixpoint retries.
    pub(super) fn exact_datatype_cell_completions(
        &self,
        model: &Model,
    ) -> ExactDatatypeCellCompletions {
        let mut completions = HashMap::default();
        if model.dt_ground.is_empty() {
            return completions;
        }
        let Some(euf) = model.euf_model.as_ref() else {
            return completions;
        };
        // Total-DT construction is capped at 1024 terms. A larger payload came
        // from another producer and is outside this narrow authority protocol.
        if model.dt_ground.len() > 1_024 {
            return completions;
        }
        let datatype_guard = RenderedDatatypeGuard::new(self);
        if !datatype_guard.is_bounded() {
            return completions;
        }
        let mut constructor_tokens = HashSet::default();
        for (_, constructors) in self.ctx.datatype_iter() {
            for constructor in constructors {
                constructor_tokens.insert(constructor.clone());
                constructor_tokens.insert(self.dt_surface(constructor).to_string());
            }
        }
        let mut aggregate_work = 0usize;
        for (&term, value) in &model.dt_ground {
            let sort = self.ctx.terms.sort(term);
            if !datatype_guard.is_exact(sort) {
                continue;
            }
            let Some(carrier) = euf.term_values.get(&term) else {
                continue;
            };
            if !exact_datatype_carrier_token(&datatype_guard, &constructor_tokens, sort, carrier) {
                continue;
            }
            let Some(value_work) = super::rendered_dt_limits::model_value_work(value) else {
                continue;
            };
            aggregate_work = match aggregate_work
                .checked_add(value_work)
                .and_then(|work| work.checked_add(value_work))
            {
                Some(work) if work <= MAX_DATATYPE_CELL_AUTHORITY_WORK => work,
                _ => return ExactDatatypeCellCompletions::default(),
            };
            let rendered = self
                .format_gate_model_value(value, sort)
                .filter(|candidate| {
                    self.parse_rendered_dt_value_guarded(candidate, sort, &datatype_guard)
                        .is_some()
                });
            if let Some(candidate) = rendered.as_deref() {
                aggregate_work = match aggregate_work
                    .checked_add(candidate.len())
                    .and_then(|work| work.checked_add(candidate.len()))
                {
                    Some(work) if work <= MAX_DATATYPE_CELL_AUTHORITY_WORK => work,
                    _ => return ExactDatatypeCellCompletions::default(),
                };
            }
            let slot = completions
                .entry(sort.clone())
                .or_default()
                .entry(carrier.clone())
                .or_insert_with(|| rendered.clone());
            if *slot != rendered {
                *slot = None;
            }
        }
        completions
    }

    /// Whether `candidate` is the unique structured value authorized for the
    /// exact bare datatype carrier `authority` in this immutable class map.
    pub(super) fn exact_datatype_cell_completion(
        &self,
        completions: &ExactDatatypeCellCompletions,
        authority: &str,
        candidate: &str,
        element_sort: &Sort,
    ) -> bool {
        completions
            .get(element_sort)
            .and_then(|by_carrier| by_carrier.get(authority))
            .and_then(Option::as_deref)
            == Some(candidate)
    }
}

/// Exact extractor carrier spelling for `sort`: `@<name>!<canonical usize>`.
/// Ascriptions, quoted spellings, whitespace, foreign sorts, overflow, and
/// live constructor identities all decline.
fn exact_datatype_carrier_token(
    guard: &RenderedDatatypeGuard,
    constructor_tokens: &HashSet<String>,
    sort: &Sort,
    token: &str,
) -> bool {
    let Some(datatype_name) = guard.datatype_name(sort) else {
        return false;
    };
    let Some(max_token_len) = datatype_name
        .len()
        .checked_add(2)
        .and_then(|len| len.checked_add(usize::BITS as usize))
    else {
        return false;
    };
    if token.len() > max_token_len {
        return false;
    }
    if ay_core::quote_symbol(datatype_name) != datatype_name
        || ay_core::quote_symbol(token) != token
    {
        return false;
    }
    let prefix = format!("@{datatype_name}!");
    let Some(counter) = token.strip_prefix(&prefix) else {
        return false;
    };
    let Ok(counter_value) = counter.parse::<usize>() else {
        return false;
    };
    counter_value.to_string() == counter && !constructor_tokens.contains(token)
}
