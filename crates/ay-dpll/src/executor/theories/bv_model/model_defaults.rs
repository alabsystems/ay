// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The model's value of `(default a)` as the else-value the select scan
//! publishes for `a`.
//!
//! The select scan pins every cell some read of `a` assigned and must choose
//! the value of every other cell: the else-value. It chose `#b0..0` (or
//! `false`) for every array. A formula that mentions `(default a)` (the
//! array-default congruence and store axioms mint the term,
//! `euf/array_patterns.rs`) already has a SAT value for it, and model
//! completion treats that value as authority: it mirrors it into `a`'s
//! interpretation and checks every unconditional definition of `a` against it
//! (`ExistingArrayDefaultPolicy::Require`, `model/completion.rs`). A
//! definition built over a base whose else-value was the scan's zero inherits
//! that zero, disagrees with the model's `(default w)`, and completion taints
//! the defined variable, its base and its stores; so a self-reading definition
//! had to stay withheld (`definition_order.rs`).
//!
//! The scan, a free base's one published default, and the scan of an array of
//! arrays (`nested_reads.rs`) take the model's `(default a)` value instead when
//! there is one. Only the else-value changes: every read cell is as before,
//! and the complete original-root validation still judges every value.

use super::*;

impl Executor {
    /// The model's value of `(default array)`, rendered as an array cell
    /// exactly as the select scan renders a read, when that term exists and
    /// the BV/Bool assignment gives it one that fits its width.
    pub(super) fn model_array_default(
        terms: &TermStore,
        bv_model: &BvModel,
        array: TermId,
    ) -> Option<String> {
        Self::model_array_default_value(terms, bv_model, array).flatten()
    }

    /// [`Self::model_array_default`], telling an absent value (`None`: no
    /// `(default array)` term, no BV/Bool value for it, or another element
    /// sort) from one no cell can render (`Some(None)`: it does not fit its
    /// width).
    pub(super) fn model_array_default_value(
        terms: &TermStore,
        bv_model: &BvModel,
        array: TermId,
    ) -> Option<Option<String>> {
        let default_term = terms.find_app_named("default", &[array])?;
        match terms.sort(default_term) {
            Sort::BitVec(sort) => bv_model.values.get(&default_term).map(|value| {
                (value.sign() != num_bigint::Sign::Minus && value.bits() <= u64::from(sort.width))
                    .then(|| format_bitvec(value, sort.width))
            }),
            Sort::Bool => bv_model
                .bool_overrides
                .get(&default_term)
                .map(|value| Some(value.to_string())),
            _ => None,
        }
    }

    /// The else-value the select scan publishes for an array with `element`
    /// cells: the model's `(default array)` when it has one, else `#b0..0` or
    /// `false`. `None` for an element sort the scan does not build.
    pub(super) fn select_scan_default(
        terms: &TermStore,
        bv_model: &BvModel,
        array: TermId,
        element: &Sort,
    ) -> Option<String> {
        let fallback = match element {
            Sort::BitVec(sort) => format_bitvec(&BigInt::from(0u8), sort.width),
            Sort::Bool => "false".to_string(),
            _ => return None,
        };
        Some(Self::model_array_default(terms, bv_model, array).unwrap_or(fallback))
    }

    /// Publish `hints` for the arrays the select scan gave no entry: the
    /// entry a definition over such a base would otherwise create with
    /// `#b0..0` (`resolve_substitution_target_interp`).
    pub(super) fn publish_unread_hinted_arrays(
        terms: &TermStore,
        hints: &HashMap<TermId, String>,
        array_values: &mut HashMap<TermId, ArrayInterpretation>,
    ) {
        for (&array, hint) in hints {
            let Sort::Array(sort) = terms.sort(array) else {
                continue;
            };
            if matches!(sort.index_sort, Sort::BitVec(_))
                && matches!(sort.element_sort, Sort::BitVec(_) | Sort::Bool)
            {
                array_values
                    .entry(array)
                    .or_insert_with(|| ArrayInterpretation {
                        index_sort: Some(sort.index_sort.clone()),
                        element_sort: Some(sort.element_sort.clone()),
                        default: Some(hint.clone()),
                        stores: Vec::new(),
                    });
            }
        }
    }

    /// The else-value each array's interpretation should take to agree with
    /// the model's `(default ..)` values: its own, else the one an
    /// unconditional definition passes down to it. A store chain's
    /// interpretation keeps its base's else-value, so `(= w (store u i v))`
    /// gives a base `u` without a value of its own `w`'s; `(= x y)` passes a
    /// value either way. A base offered two different values gets none. Only
    /// bases (and equated arrays) are listed.
    pub(super) fn array_default_hints(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
    ) -> HashMap<TermId, String> {
        // `(from, to)`: `to`'s interpretation keeps `from`'s else-value.
        let mut edges: Vec<(TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut top: Vec<TermId> = assertions.to_vec();
        while let Some(term) = top.pop() {
            if !seen.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::App(sym, args) if sym.name() == "and" => top.extend(args.iter().copied()),
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    for (var, other) in [(args[0], args[1]), (args[1], args[0])] {
                        if !matches!(terms.get(var), TermData::Var(_, _))
                            || !matches!(terms.sort(var), Sort::Array(_))
                        {
                            continue;
                        }
                        let base = match terms.get(other) {
                            TermData::Var(_, _) => Some(other),
                            TermData::App(sym, _) if sym.name() == "store" => {
                                Self::collect_store_chain_entries(terms, other)
                                    .map(|(_, base)| base)
                                    .filter(|&base| matches!(terms.get(base), TermData::Var(_, _)))
                            }
                            _ => None,
                        };
                        if let Some(base) = base.filter(|&base| base != var) {
                            edges.push((var, base));
                        }
                    }
                }
                _ => {}
            }
        }
        let mut hints: HashMap<TermId, Option<String>> = HashMap::default();
        for &(from, to) in &edges {
            for array in [from, to] {
                if let Some(value) = Self::model_array_default(terms, bv_model, array) {
                    hints.insert(array, Some(value));
                }
            }
        }
        let own: HashSet<TermId> = hints.keys().copied().collect();
        for _ in 0..edges.len() {
            let mut changed = false;
            for &(from, to) in &edges {
                if own.contains(&to) {
                    continue;
                }
                let Some(Some(value)) = hints.get(&from).cloned() else {
                    continue;
                };
                match hints.get(&to) {
                    None => {
                        hints.insert(to, Some(value));
                        changed = true;
                    }
                    Some(Some(existing)) if *existing != value => {
                        hints.insert(to, None);
                        changed = true;
                    }
                    Some(_) => {}
                }
            }
            if !changed {
                break;
            }
        }
        // Only a base or an equated array takes a value here; any other
        // array's own value is the select scan's default already.
        let bases: HashSet<TermId> = edges.iter().map(|&(_, to)| to).collect();
        hints
            .into_iter()
            .filter(|(array, _)| bases.contains(array))
            .filter_map(|(array, value)| Some((array, value?)))
            .collect()
    }
}
