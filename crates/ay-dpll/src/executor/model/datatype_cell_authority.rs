// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact class authority for datatype-valued array cells.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};

use super::rendered_dt_guard::RenderedDatatypeGuard;
use super::{EvalValue, Model};
use crate::executor::Executor;

const MAX_DATATYPE_CELL_AUTHORITY_WORK: usize = 4 * 1024 * 1024;
const MAX_DATATYPE_CELL_AUTHORITY_TERMS: usize = 4 * 1024;

/// One prevalidated structured rendering per exact datatype carrier class.
/// `None` marks a poisoned class whose same-sort ground rows disagree.
pub(super) type ExactDatatypeCellCompletions = HashMap<Sort, HashMap<String, Option<String>>>;

impl Executor {
    /// Build immutable datatype-cell authority once per array-completion pass.
    /// Every later merge lookup is O(1), including bounded fixpoint retries.
    pub(super) fn exact_datatype_cell_completions(
        &self,
        model: &Model,
        extra_roots: &[TermId],
    ) -> ExactDatatypeCellCompletions {
        let mut completions = HashMap::default();
        let Some(euf) = model.euf_model.as_ref() else {
            return completions;
        };
        // Total-DT construction is capped at 1024 terms. A larger payload came
        // from another producer and is outside this narrow authority protocol.
        if model.dt_ground.len() > 1_024 {
            return completions;
        }
        // Bound the externally produced carrier inventory even though the hard
        // equality lane below performs only O(1) lookups into it.
        if euf.term_values.len() > MAX_DATATYPE_CELL_AUTHORITY_TERMS {
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
        if !self.collect_ground_datatype_cell_authority(
            model,
            &datatype_guard,
            &constructor_tokens,
            &mut completions,
            &mut aggregate_work,
        ) {
            return ExactDatatypeCellCompletions::default();
        }
        let Some(equalities) = self.hard_datatype_cell_equalities(extra_roots) else {
            return ExactDatatypeCellCompletions::default();
        };
        if !self.collect_hard_datatype_cell_authority(
            model,
            &datatype_guard,
            &constructor_tokens,
            &equalities,
            &mut completions,
            &mut aggregate_work,
        ) {
            return ExactDatatypeCellCompletions::default();
        }
        completions
    }

    fn collect_ground_datatype_cell_authority(
        &self,
        model: &Model,
        guard: &RenderedDatatypeGuard,
        constructor_tokens: &HashSet<String>,
        completions: &mut ExactDatatypeCellCompletions,
        aggregate_work: &mut usize,
    ) -> bool {
        let Some(euf) = model.euf_model.as_ref() else {
            return false;
        };
        for (&term, value) in &model.dt_ground {
            // Some model-repair lanes use reserved sentinel TermIds as private
            // metadata. They are not terms and can never carry semantic
            // datatype authority.
            if self.ctx.terms.entry_stamp(term).is_none() {
                continue;
            }
            let sort = self.ctx.terms.sort(term);
            if !guard.is_exact_array_cell(sort) {
                continue;
            }
            let Some(carrier) = euf.term_values.get(&term) else {
                continue;
            };
            if !exact_datatype_carrier_token(guard, constructor_tokens, sort, carrier) {
                continue;
            }
            let Some(value_work) = super::rendered_dt_limits::model_value_work(value) else {
                continue;
            };
            if !charge_datatype_cell_authority_work(aggregate_work, value_work) {
                return false;
            }
            let rendered = self
                .format_gate_model_value(value, sort)
                .filter(|candidate| {
                    self.parse_rendered_dt_value_cached(candidate, sort, guard)
                        .is_some()
                });
            if rendered.as_ref().is_some_and(|candidate| {
                !charge_datatype_cell_authority_work(aggregate_work, candidate.len())
            }) {
                return false;
            }
            merge_datatype_cell_completion(completions, sort, carrier, rendered);
        }
        true
    }

    /// Collect only equalities that are themselves active top-level facts.
    /// Descending through `and` mirrors the solver's assertion flattening;
    /// every other Boolean connective remains opaque to this authority lane.
    fn hard_datatype_cell_equalities(
        &self,
        extra_roots: &[TermId],
    ) -> Option<Vec<(TermId, TermId)>> {
        let root_count = self.ctx.assertions.len().checked_add(extra_roots.len())?;
        if root_count > MAX_DATATYPE_CELL_AUTHORITY_TERMS {
            return None;
        }
        let mut hard: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .chain(extra_roots.iter().copied())
            .collect();
        let mut seen = HashSet::default();
        let mut equalities = Vec::new();
        while let Some(root) = hard.pop() {
            self.ctx.terms.entry_stamp(root)?;
            if !seen.insert(root) {
                continue;
            }
            if seen.len() > MAX_DATATYPE_CELL_AUTHORITY_TERMS {
                return None;
            }
            let TermData::App(symbol, args) = self.ctx.terms.get(root) else {
                continue;
            };
            if symbol.name() == "and" {
                if hard
                    .len()
                    .checked_add(args.len())
                    .is_none_or(|pending| pending > MAX_DATATYPE_CELL_AUTHORITY_TERMS)
                {
                    return None;
                }
                hard.extend(args.iter().copied());
                continue;
            }
            if symbol.name() == "=" && args.len() == 2 {
                equalities.push((args[0], args[1]));
            }
        }
        Some(equalities)
    }

    /// The combined array+datatype lane can leave `dt_ground` empty while the
    /// array extractor stores an opaque `@D!n` cell. Bind that class only to a
    /// literal constructor tree named by an active hard equality. Two distinct
    /// trees for one carrier poison it; final model gates still arbitrate SAT.
    fn collect_hard_datatype_cell_authority(
        &self,
        model: &Model,
        guard: &RenderedDatatypeGuard,
        constructor_tokens: &HashSet<String>,
        equalities: &[(TermId, TermId)],
        completions: &mut ExactDatatypeCellCompletions,
        aggregate_work: &mut usize,
    ) -> bool {
        let Some(euf) = model.euf_model.as_ref() else {
            return false;
        };
        for &(lhs, rhs) in equalities {
            for (select, constructor) in [(lhs, rhs), (rhs, lhs)] {
                let TermData::App(select_symbol, select_args) = self.ctx.terms.get(select) else {
                    continue;
                };
                if !self.dt_completion_array_cell_select_application_guarded(
                    guard,
                    select_symbol,
                    select_args,
                    select,
                ) {
                    continue;
                }
                let sort = self.ctx.terms.sort(select);
                if !guard.is_exact_array_cell(sort) || self.ctx.terms.sort(constructor) != sort {
                    continue;
                }
                let Some(carrier) = euf.term_values.get(&select) else {
                    continue;
                };
                if !exact_datatype_carrier_token(guard, constructor_tokens, sort, carrier) {
                    continue;
                }
                let Some(rendered) = self.exact_concrete_datatype_literal(constructor, sort, guard)
                else {
                    continue;
                };
                if !charge_datatype_cell_authority_work(aggregate_work, rendered.len()) {
                    return false;
                }
                merge_datatype_cell_completion(completions, sort, carrier, Some(rendered));
            }
        }
        true
    }

    /// Install a structured rendering for every live term in an authorized
    /// exact EUF carrier class. Array extraction keeps its own opaque carrier
    /// spelling, but all semantic evaluators must observe the same constructor
    /// value that the hard equality and completed array cell establish.
    ///
    /// A poisoned or absent class is skipped. The caller clears the immutable
    /// evaluation memo when this reports a change; the ordinary strict and
    /// independent gates still recheck every assertion after installation.
    pub(super) fn apply_exact_datatype_cell_completions(
        &self,
        model: &mut Model,
        completions: &ExactDatatypeCellCompletions,
    ) -> bool {
        let Some(euf) = model.euf_model.as_ref() else {
            return false;
        };
        if euf.term_values.len() > MAX_DATATYPE_CELL_AUTHORITY_TERMS {
            return false;
        }
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return false;
        }
        // Collect only matched, bounded candidates while `euf` is borrowed;
        // never clone unrelated (and potentially very large) carrier strings.
        let assignments: Vec<_> = euf
            .term_values
            .iter()
            .filter_map(|(&term, carrier)| {
                self.ctx.terms.entry_stamp(term)?;
                let sort = self.ctx.terms.sort(term);
                let candidate = completions.get(sort)?.get(carrier)?.as_deref()?;
                let value = self.parse_rendered_dt_value_cached(candidate, sort, &guard)?;
                Some((term, candidate.to_string(), value))
            })
            .collect();
        let changed = !assignments.is_empty();
        for (term, candidate, value) in assignments {
            model.dt_ground.insert(term, value);
            model.dt_pins.insert(term, EvalValue::Element(candidate));
        }
        changed
    }

    /// Render one entirely literal constructor tree after a bounded structural
    /// preflight. This avoids calling the recursive term printer on an
    /// adversarial DAG before its expanded work is known to fit the same limits
    /// as the exact datatype parser.
    fn exact_concrete_datatype_literal(
        &self,
        root: TermId,
        root_sort: &Sort,
        guard: &RenderedDatatypeGuard,
    ) -> Option<String> {
        use super::rendered_dt_limits::{
            MAX_RENDERED_DT_BYTES, MAX_RENDERED_DT_DEPTH, MAX_RENDERED_DT_NODES,
        };

        let mut stack = vec![(root, root_sort.clone(), 0usize)];
        let mut nodes = 0usize;
        let mut work = 0usize;
        while let Some((term, expected_sort, depth)) = stack.pop() {
            if depth > MAX_RENDERED_DT_DEPTH || self.ctx.terms.sort(term) != &expected_sort {
                return None;
            }
            nodes = nodes.checked_add(1)?;
            if nodes > MAX_RENDERED_DT_NODES {
                return None;
            }
            if guard.datatype_name(&expected_sort).is_some() {
                let (head, args): (&str, &[TermId]) = match self.ctx.terms.get(term) {
                    TermData::Var(name, _) => (name.as_str(), &[]),
                    TermData::App(symbol, args) => (symbol.name(), args.as_slice()),
                    _ => return None,
                };
                self.ctx.is_constructor(head)?;
                let (_, field_sorts) = guard.constructor(&expected_sort, head)?;
                if field_sorts.len() != args.len()
                    || stack
                        .len()
                        .checked_add(args.len())
                        .is_none_or(|pending| pending > MAX_RENDERED_DT_NODES)
                {
                    return None;
                }
                work = work.checked_add(head.len().checked_add(2)?)?;
                if work > MAX_RENDERED_DT_BYTES {
                    return None;
                }
                stack.extend(
                    args.iter()
                        .copied()
                        .zip(field_sorts.iter().cloned())
                        .map(|(arg, sort)| (arg, sort, depth + 1)),
                );
                continue;
            }
            let literal_work = match (self.ctx.terms.get(term), &expected_sort) {
                (TermData::Const(Constant::Bool(_)), Sort::Bool) => 5,
                (TermData::Const(Constant::Int(value)), Sort::Int) => {
                    usize::try_from(value.bits()).ok()?.checked_add(2)?
                }
                (TermData::Const(Constant::BitVec { value, width }), Sort::BitVec(sort))
                    if *width == sort.width =>
                {
                    usize::try_from(value.bits())
                        .ok()?
                        .max(usize::try_from(*width).ok()?)
                        .checked_add(16)?
                }
                _ => return None,
            };
            work = work.checked_add(literal_work)?;
            if work > MAX_RENDERED_DT_BYTES {
                return None;
            }
        }

        let rendered = self.format_term(root);
        let value = self.parse_rendered_dt_value_cached(&rendered, root_sort, guard)?;
        self.format_gate_model_value(&value, root_sort)
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

fn charge_datatype_cell_authority_work(aggregate: &mut usize, amount: usize) -> bool {
    let Some(next) = aggregate
        .checked_add(amount)
        .and_then(|work| work.checked_add(amount))
    else {
        return false;
    };
    if next > MAX_DATATYPE_CELL_AUTHORITY_WORK {
        return false;
    }
    *aggregate = next;
    true
}

fn merge_datatype_cell_completion(
    completions: &mut ExactDatatypeCellCompletions,
    sort: &Sort,
    carrier: &str,
    rendered: Option<String>,
) {
    let slot = completions
        .entry(sort.clone())
        .or_default()
        .entry(carrier.to_string())
        .or_insert_with(|| rendered.clone());
    if *slot != rendered {
        *slot = None;
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
