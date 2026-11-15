// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A RoundingMode value in a model is one of the five modes.
//!
//! RoundingMode is `Sort::Uninterpreted("RoundingMode")` in the core, so EUF
//! model extraction names every class of the sort. A class that holds a mode
//! literal takes the literal's name; any other class gets a minted
//! `@RoundingMode!n` element (ay-euf `model_extraction.rs`). The domain axioms
//! (`rm_domain`) put every RoundingMode term of the solved assertions into a
//! literal class, so a minted class holds only terms that solve never
//! constrained: a declared constant no assertion mentions, or a term of the
//! store that the unscoped extraction sweeps in. The FP-to-Real lane shows
//! both. Its Real subproblem replaces each decided mode with its literal, yet
//! its EUF model still names the original constant `r1` and a stale `(g r1)`.
//!
//! Printed, a minted element is `(as @RoundingMode!1 RoundingMode)`. That is
//! not a value of the sort, and z3 rejects the model (2026-09-30 FP verify 2:
//! an unused mode constant with a UF over RoundingMode or an array in scope).
//! [`Executor::concretize_rounding_mode_values`] gives every minted class a
//! mode before completion and the gates read the model. The printers,
//! get-value and the gates then read one concrete value, and the gate checks
//! the value that is printed.

use ay_arrays::{ArrayInterpretation, ArrayModel};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermId};
use ay_euf::{EufModel, FunctionTable};
use ay_fp::RoundingMode;

use super::{EvalValue, Model};
use crate::executor::rm_domain::{is_rm_sort, rm_long_name, RM_MODES};
use crate::executor::Executor;

const RM_SORT_NAME: &str = "RoundingMode";
const MINTED_RM_PREFIX: &str = "@RoundingMode!";

/// Argument and result sorts of the declared functions whose signature
/// mentions RoundingMode, by the model identity their table is stored under.
type RmFunctionSorts = HashMap<String, (Vec<Sort>, Sort)>;

/// Whether a RoundingMode-sorted `value` may be published: one of the five
/// modes, or no value at all. Values of every other sort are not judged here.
pub(in crate::executor) fn publishable_rm_value(sort: &Sort, value: &EvalValue) -> bool {
    if !is_rm_sort(sort) {
        return true;
    }
    match value {
        EvalValue::Element(name) => RoundingMode::from_name(name).is_some(),
        EvalValue::Unknown => true,
        _ => false,
    }
}

/// Whether the raw model entry `raw` at a position of sort `rm_position`
/// (known to be RoundingMode, or not) is a RoundingMode value. A minted
/// element carries its sort in its name, so it is recognised anywhere.
fn at_rm_position(rm_position: bool, raw: &str) -> bool {
    rm_position || raw.starts_with(MINTED_RM_PREFIX)
}

/// The mode `raw` becomes, when it is a minted RoundingMode value.
fn chosen_for<'c>(
    chosen: &'c HashMap<String, String>,
    rm_position: bool,
    raw: &str,
) -> Option<&'c String> {
    if at_rm_position(rm_position, raw) {
        chosen.get(raw)
    } else {
        None
    }
}

/// The RoundingMode values a model holds that are not modes, with the terms
/// EUF gave each, and the modes the model's classes already name.
#[derive(Default)]
struct RmValueScan {
    /// Each value in first-seen order, with its member terms.
    minted: Vec<(String, Vec<TermId>)>,
    position: HashMap<String, usize>,
    named: HashSet<RoundingMode>,
}

impl RmValueScan {
    fn note(&mut self, raw: &str, member: Option<TermId>) {
        // `@?N` is a placeholder the printer resolves through the evaluation
        // chain, which never answers a minted mode (`evaluate_var`).
        if raw.starts_with("@?") {
            return;
        }
        if let Some(mode) = RoundingMode::from_name(raw) {
            self.named.insert(mode);
            return;
        }
        let slot = match self.position.get(raw) {
            Some(&slot) => slot,
            None => {
                self.minted.push((raw.to_string(), Vec::new()));
                self.position.insert(raw.to_string(), self.minted.len() - 1);
                self.minted.len() - 1
            }
        };
        if let Some(term) = member {
            self.minted[slot].1.push(term);
        }
    }

    /// The mode each minted value becomes, in its first-seen order:
    /// 1. the mode the FP circuit decoded for a member (`rm_values`): the
    ///    model already holds that equality;
    /// 2. a mode no class of the model names and no earlier value took, which
    ///    keeps every pair of classes distinct;
    /// 3. a mode no earlier value took, which keeps the minted classes
    ///    pairwise distinct: a literal class shares its mode, and a function
    ///    row keyed by the minted class yields to the literal's row
    ///    ([`rewrite_function_table`]);
    /// 4. `roundNearestTiesToEven`.
    ///
    /// Any choice is sound for a class no assertion constrains, and the gate
    /// re-checks every assertion against the chosen values.
    fn choose(self, decided: Option<&HashMap<TermId, RoundingMode>>) -> HashMap<String, String> {
        let Self { minted, named, .. } = self;
        let mut taken: HashSet<RoundingMode> = HashSet::default();
        let mut chosen = HashMap::default();
        for (raw, mut members) in minted {
            members.sort_unstable_by_key(|term| term.index());
            let mode = members
                .iter()
                .find_map(|term| decided.and_then(|modes| modes.get(term)).copied())
                .or_else(|| {
                    RM_MODES
                        .iter()
                        .copied()
                        .find(|mode| !named.contains(mode) && !taken.contains(mode))
                })
                .or_else(|| RM_MODES.iter().copied().find(|mode| !taken.contains(mode)))
                .unwrap_or(RoundingMode::RNE);
            taken.insert(mode);
            chosen.insert(raw, rm_long_name(mode).to_string());
        }
        chosen
    }
}

impl Executor {
    /// Give every RoundingMode value of `model` that is not a mode (a minted
    /// EUF element) a concrete mode: constants and other terms, the sort's
    /// element list, function-table arguments and results, array defaults,
    /// indices and cells, and completed values. Returns whether the model
    /// changed; a caller holding validation evidence for it must revoke it.
    pub(in crate::executor) fn concretize_rounding_mode_values(&self, model: &mut Model) -> bool {
        // Minted elements come from EUF classes, and reach arrays through them.
        let function_sorts = match model.euf_model.as_ref() {
            Some(euf) if !euf.function_tables.is_empty() => self.rm_function_sorts(),
            Some(_) => RmFunctionSorts::default(),
            None if model.array_model.is_none() => return false,
            None => RmFunctionSorts::default(),
        };
        let mut scan = RmValueScan::default();
        if let Some(euf) = model.euf_model.as_ref() {
            self.scan_euf_rm_values(euf, &function_sorts, &mut scan);
        }
        if let Some(arrays) = model.array_model.as_ref() {
            for (&term, interp) in sorted_interpretations(&arrays.array_values) {
                self.scan_array_rm_values(term, interp, &mut scan);
            }
        }
        if scan.minted.is_empty() {
            return false;
        }
        let chosen = scan.choose(model.fp_model.as_ref().map(|fp| &fp.rm_values));
        if let Some(euf) = model.euf_model.as_mut() {
            self.rewrite_euf_rm_values(euf, &function_sorts, &chosen);
        }
        if let Some(arrays) = model.array_model.as_mut() {
            self.rewrite_array_rm_values(arrays, &chosen);
        }
        for (&term, value) in &mut model.completed_values {
            if let EvalValue::Element(name) = value {
                if let Some(mode) = chosen_for(&chosen, is_rm_sort(self.ctx.terms.sort(term)), name)
                {
                    *name = mode.clone();
                }
            }
        }
        super::eval_memo_clear();
        true
    }

    fn rm_function_sorts(&self) -> RmFunctionSorts {
        self.ctx
            .symbol_iter()
            .filter(|(_, info)| {
                !info.arg_sorts.is_empty()
                    && (is_rm_sort(&info.sort) || info.arg_sorts.iter().any(is_rm_sort))
            })
            .map(|(name, info)| {
                (
                    self.ctx.symbol_identity_name(name, info).to_string(),
                    (info.arg_sorts.clone(), info.sort.clone()),
                )
            })
            .collect()
    }

    fn scan_euf_rm_values(
        &self,
        euf: &EufModel,
        function_sorts: &RmFunctionSorts,
        scan: &mut RmValueScan,
    ) {
        // The element list first: it is in EUF's naming order.
        for element in euf.sort_elements.get(RM_SORT_NAME).into_iter().flatten() {
            scan.note(element, None);
        }
        let mut members: Vec<(TermId, &String)> = euf
            .term_values
            .iter()
            .filter(|(&term, _)| is_rm_sort(self.ctx.terms.sort(term)))
            .map(|(&term, value)| (term, value))
            .collect();
        members.sort_unstable_by_key(|(term, _)| term.index());
        for (term, value) in members {
            scan.note(value, Some(term));
        }
        let mut tables: Vec<(&String, &FunctionTable)> = euf.function_tables.iter().collect();
        tables.sort_unstable_by_key(|(name, _)| *name);
        for (name, table) in tables {
            let sorts = function_sorts.get(name);
            for (args, result) in table {
                for (i, arg) in args.iter().enumerate() {
                    if at_rm_position(arg_is_rm(sorts, i), arg) {
                        scan.note(arg, None);
                    }
                }
                if at_rm_position(result_is_rm(sorts), result) {
                    scan.note(result, None);
                }
            }
        }
    }

    fn rewrite_euf_rm_values(
        &self,
        euf: &mut EufModel,
        function_sorts: &RmFunctionSorts,
        chosen: &HashMap<String, String>,
    ) {
        for (&term, value) in &mut euf.term_values {
            if let Some(mode) = chosen_for(chosen, is_rm_sort(self.ctx.terms.sort(term)), value) {
                *value = mode.clone();
            }
        }
        if let Some(elements) = euf.sort_elements.get_mut(RM_SORT_NAME) {
            let mut seen = HashSet::default();
            for element in std::mem::take(elements) {
                let element = chosen.get(&element).cloned().unwrap_or(element);
                if seen.insert(element.clone()) {
                    elements.push(element);
                }
            }
        }
        for (name, table) in &mut euf.function_tables {
            rewrite_function_table(
                table,
                euf.function_table_terms.get_mut(name),
                function_sorts.get(name),
                chosen,
            );
        }
    }

    fn array_rm_positions(&self, term: TermId, interp: &ArrayInterpretation) -> (bool, bool) {
        match self.ctx.terms.sort(term) {
            Sort::Array(array) => (
                is_rm_sort(&array.index_sort),
                is_rm_sort(&array.element_sort),
            ),
            _ => (
                interp.index_sort.as_ref().is_some_and(is_rm_sort),
                interp.element_sort.as_ref().is_some_and(is_rm_sort),
            ),
        }
    }

    fn scan_array_rm_values(
        &self,
        term: TermId,
        interp: &ArrayInterpretation,
        scan: &mut RmValueScan,
    ) {
        let (index_rm, element_rm) = self.array_rm_positions(term, interp);
        if let Some(default) = &interp.default {
            if at_rm_position(element_rm, default) {
                scan.note(default, None);
            }
        }
        for (index, value) in &interp.stores {
            if at_rm_position(index_rm, index) {
                scan.note(index, None);
            }
            if at_rm_position(element_rm, value) {
                scan.note(value, None);
            }
        }
    }

    fn rewrite_array_rm_values(&self, arrays: &mut ArrayModel, chosen: &HashMap<String, String>) {
        for (&term, interp) in &mut arrays.array_values {
            let positions = self.array_rm_positions(term, interp);
            rewrite_array_interpretation(interp, positions, chosen);
        }
        for (&term, interp) in arrays
            .store_chain_class_candidate
            .iter_mut()
            .flat_map(|candidate| candidate.iter_mut())
        {
            let positions = self.array_rm_positions(term, interp);
            rewrite_array_interpretation(interp, positions, chosen);
        }
    }
}

fn sorted_interpretations(
    values: &HashMap<TermId, ArrayInterpretation>,
) -> Vec<(&TermId, &ArrayInterpretation)> {
    let mut sorted: Vec<_> = values.iter().collect();
    sorted.sort_unstable_by_key(|(term, _)| term.index());
    sorted
}

fn arg_is_rm(sorts: Option<&(Vec<Sort>, Sort)>, i: usize) -> bool {
    sorts.is_some_and(|(args, _)| args.get(i).is_some_and(is_rm_sort))
}

fn result_is_rm(sorts: Option<&(Vec<Sort>, Sort)>) -> bool {
    sorts.is_some_and(|(_, result)| is_rm_sort(result))
}

/// Rewrite one function table's RoundingMode entries.
///
/// A row keyed by a minted element moves to the element's mode. If a row
/// keyed only by values that stay (a literal class's row, which the solve
/// constrained) or an earlier moved row already holds that point, the moved
/// row is dropped rather than printed as a second, possibly conflicting arm:
/// the minted class is one no assertion constrained, so its row is not part
/// of the model the solve committed to. The aligned source applications
/// (`function_table_terms`) drop with their rows.
fn rewrite_function_table(
    table: &mut FunctionTable,
    sources: Option<&mut Vec<TermId>>,
    sorts: Option<&(Vec<Sort>, Sort)>,
    chosen: &HashMap<String, String>,
) {
    let moves = |args: &[String]| {
        args.iter()
            .enumerate()
            .any(|(i, arg)| chosen_for(chosen, arg_is_rm(sorts, i), arg).is_some())
    };
    let mut held: HashSet<Vec<String>> = table
        .iter()
        .filter(|(args, _)| !moves(args))
        .map(|(args, _)| args.clone())
        .collect();
    let mut keep = Vec::with_capacity(table.len());
    for (args, result) in table.iter_mut() {
        let moved = moves(args);
        for (i, arg) in args.iter_mut().enumerate() {
            if let Some(mode) = chosen_for(chosen, arg_is_rm(sorts, i), arg) {
                *arg = mode.clone();
            }
        }
        if let Some(mode) = chosen_for(chosen, result_is_rm(sorts), result) {
            *result = mode.clone();
        }
        keep.push(!moved || held.insert(args.clone()));
    }
    if keep.iter().all(|&kept| kept) {
        return;
    }
    if let Some(sources) = sources.filter(|sources| sources.len() == keep.len()) {
        let mut flags = keep.iter();
        sources.retain(|_| flags.next().copied().unwrap_or(true));
    }
    let mut flags = keep.iter();
    table.retain(|_| flags.next().copied().unwrap_or(true));
}

/// Rewrite one array interpretation's RoundingMode default, indices and
/// cells. `stores` is newest first and a read takes the first match, so a
/// store whose minted index moves onto an index another store keeps would
/// shadow or duplicate it: it is dropped, as a moved function row is.
fn rewrite_array_interpretation(
    interp: &mut ArrayInterpretation,
    (index_rm, element_rm): (bool, bool),
    chosen: &HashMap<String, String>,
) {
    if let Some(default) = interp.default.as_mut() {
        if let Some(mode) = chosen_for(chosen, element_rm, default) {
            *default = mode.clone();
        }
    }
    let mut held: HashSet<String> = interp
        .stores
        .iter()
        .filter(|(index, _)| chosen_for(chosen, index_rm, index).is_none())
        .map(|(index, _)| index.clone())
        .collect();
    let mut kept = Vec::with_capacity(interp.stores.len());
    for (mut index, mut value) in std::mem::take(&mut interp.stores) {
        if let Some(mode) = chosen_for(chosen, element_rm, &value) {
            value = mode.clone();
        }
        if let Some(mode) = chosen_for(chosen, index_rm, &index) {
            index = mode.clone();
            if !held.insert(index.clone()) {
                continue;
            }
        }
        kept.push((index, value));
    }
    interp.stores = kept;
}

#[cfg(test)]
#[path = "rm_concrete_tests.rs"]
mod tests;
