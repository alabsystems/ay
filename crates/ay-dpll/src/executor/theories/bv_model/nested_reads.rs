// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The select scan for arrays of arrays.
//!
//! The scan in [`Executor::extract_array_model_from_bv_model`] reads
//! `(select a i)` over an array variable `a` with BV or Bool cells. A cell of
//! an array of arrays, `(select (select m i) j)` over
//! `m : (Array BV64 (Array BV64 BV8))`, is a bit-blasted BV term as well, but
//! its array operand is the array-valued read `(select m i)`, so the scan
//! skipped it and `m` got no interpretation at all. A nested-only definition
//! of such a variable then had to stay withheld whatever the model did with
//! it (`live_definitions.rs`): released, it would carry no value of its own.
//!
//! This scan builds `m`'s interpretation from its committed reads exactly as
//! the flat scan builds a flat one. Every read path `m[i1]..[ik]` down to a
//! BV or Bool cell whose indices resolve, none mentioning an eliminated
//! variable, pins its cell; two reads of one path that disagree pin nothing
//! there (#8510). Every other cell takes the else-value of the innermost array
//! it lies in: the model's `(default (select .. (select m i1) ..))` when that
//! term has one (`model_defaults.rs`), else `#b0..0` or `false`; an inner array
//! no read reaches is the constant array of that fallback. An inner array is a
//! cell of the outer one, rendered as the printer's text (`nested_cells.rs`)
//! with its stores in index order, so one inner array always renders alike.
//! This is model data only; the complete original-root validation judges it.
//!
//! An array of arrays that ends extraction withheld (`read_conflicted`) keeps
//! no entry from this scan, exactly as before the scan existed. The
//! independent gate refuses a withheld array whatever its entry
//! (`array_from_model`), but the strict oracle still reads its explicit
//! stores (`lookup_array_model`), so an entry let a round's model pass the
//! strict oracle only to stop at the gate as `unknown`, where without one the
//! strict oracle rejects it and the search refines on.

use std::collections::BTreeMap;

use super::*;

/// Nesting depth beyond which a read path is not followed.
const MAX_NESTING: usize = 32;

/// The committed cells of one array of arrays, keyed by index path.
#[derive(Default)]
struct NestedCells {
    /// Full read paths to their BV/Bool cell; `None` once two reads disagree.
    leaves: BTreeMap<Vec<String>, Option<String>>,
    /// Paths of innermost arrays to their model `(default ..)` value; `None`
    /// once two default terms of one path disagree.
    defaults: BTreeMap<Vec<String>, Option<String>>,
}

impl Executor {
    /// The levels of `sort` the select scans interpret: every level indexed by
    /// a bit-vector, the innermost holding BV or Bool cells. 1 for a flat
    /// array; `None` for any other sort.
    pub(super) fn select_scan_depth(sort: &Sort) -> Option<usize> {
        let mut depth = 0;
        let mut current = sort;
        while let Sort::Array(array) = current {
            if !matches!(array.index_sort, Sort::BitVec(_)) || depth >= MAX_NESTING {
                return None;
            }
            depth += 1;
            current = &array.element_sort;
        }
        (depth > 0 && matches!(current, Sort::BitVec(_) | Sort::Bool)).then_some(depth)
    }

    /// Publish [`Self::nested_select_interpretations`] for the arrays no
    /// earlier scan gave an entry, and return what it published.
    pub(super) fn publish_nested_reads(
        terms: &TermStore,
        bv_model: &BvModel,
        decoupled: &mut dyn FnMut(TermId) -> bool,
        array_values: &mut HashMap<TermId, ArrayInterpretation>,
    ) -> HashMap<TermId, ArrayInterpretation> {
        let mut published = Self::nested_select_interpretations(terms, bv_model, decoupled);
        published.retain(|root, _| !array_values.contains_key(root));
        for (&root, interp) in &published {
            array_values.insert(root, interp.clone());
        }
        published
    }

    /// Drop each entry [`Self::publish_nested_reads`] published whose array
    /// ends extraction withheld, unless something has replaced it since.
    pub(super) fn drop_withheld_nested_reads(
        published: &HashMap<TermId, ArrayInterpretation>,
        array_model: &mut ArrayModel,
    ) {
        for (root, interp) in published {
            if array_model.is_withheld(root) && array_model.array_values.get(root) == Some(interp) {
                array_model.array_values.remove(root);
            }
        }
    }

    /// The interpretation of every array variable of nesting depth two or more
    /// that some committed read reaches. `decoupled` is the flat scan's test
    /// for an index mentioning an eliminated variable.
    fn nested_select_interpretations(
        terms: &TermStore,
        bv_model: &BvModel,
        decoupled: &mut dyn FnMut(TermId) -> bool,
    ) -> HashMap<TermId, ArrayInterpretation> {
        let mut cells: BTreeMap<TermId, NestedCells> = BTreeMap::new();
        let leaves = bv_model
            .values
            .keys()
            .chain(bv_model.bool_overrides.keys())
            .copied();
        for term in leaves {
            if let Some((root, path, value)) =
                Self::nested_leaf_cell(terms, bv_model, term, decoupled)
            {
                let entry = cells.entry(root).or_default().leaves.entry(path);
                Self::record_nested_cell(entry, value);
            }
        }
        if cells.is_empty() {
            return HashMap::default();
        }
        let defaults = bv_model
            .values
            .keys()
            .chain(bv_model.bool_overrides.keys())
            .copied();
        for term in defaults {
            Self::record_nested_default(terms, bv_model, term, decoupled, &mut cells);
        }
        cells
            .into_iter()
            .filter_map(|(root, cells)| {
                let interp = Self::nested_interp(terms.sort(root), &mut Vec::new(), &cells)?;
                Some((root, interp))
            })
            .collect()
    }

    /// `(root, path, cell)` for a BV/Bool read `(select .. (select root i1) ..)`
    /// at least two levels deep, its indices resolved.
    fn nested_leaf_cell(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        decoupled: &mut dyn FnMut(TermId) -> bool,
    ) -> Option<(TermId, Vec<String>, String)> {
        let (root, indices) = Self::nested_read_indices(terms, term)?;
        if indices.len() < 2 || Self::select_scan_depth(terms.sort(root)) != Some(indices.len()) {
            return None;
        }
        let path = Self::nested_index_path(terms, bv_model, &indices, decoupled)?;
        let value = match terms.sort(term) {
            Sort::BitVec(sort) => bv_model
                .values
                .get(&term)
                .map(|value| format_bitvec(value, sort.width))?,
            Sort::Bool => bv_model.bool_overrides.get(&term)?.to_string(),
            _ => return None,
        };
        Some((root, path, value))
    }

    /// Record `term` when it is `(default (select .. (select root i1) ..))`
    /// over a scanned root whose innermost arrays it names.
    fn record_nested_default(
        terms: &TermStore,
        bv_model: &BvModel,
        term: TermId,
        decoupled: &mut dyn FnMut(TermId) -> bool,
        cells: &mut BTreeMap<TermId, NestedCells>,
    ) {
        let Some(array) = terms.get_array_default(term) else {
            return;
        };
        let Some((root, indices)) = Self::nested_read_indices(terms, array) else {
            return;
        };
        let Some(depth) = Self::select_scan_depth(terms.sort(root)) else {
            return;
        };
        if indices.is_empty() || indices.len() + 1 != depth || !cells.contains_key(&root) {
            return;
        }
        let Some(path) = Self::nested_index_path(terms, bv_model, &indices, decoupled) else {
            return;
        };
        let Some(value) = Self::model_array_default(terms, bv_model, array) else {
            return;
        };
        if let Some(cells) = cells.get_mut(&root) {
            Self::record_nested_cell(cells.defaults.entry(path), value);
        }
    }

    /// Insert `value` at a path; a disagreeing second value poisons it.
    fn record_nested_cell(
        entry: std::collections::btree_map::Entry<'_, Vec<String>, Option<String>>,
        value: String,
    ) {
        match entry {
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(Some(value));
            }
            std::collections::btree_map::Entry::Occupied(mut slot) => {
                if slot
                    .get()
                    .as_ref()
                    .is_some_and(|existing| *existing != value)
                {
                    slot.insert(None);
                }
            }
        }
    }

    /// `(root, [i1, .., ik])` for `(select .. (select root i1) .. ik)` over an
    /// array variable `root`, outermost index first. `([], term)` for a bare
    /// variable.
    fn nested_read_indices(terms: &TermStore, term: TermId) -> Option<(TermId, Vec<TermId>)> {
        let mut indices = Vec::new();
        let mut current = term;
        loop {
            match terms.get(current) {
                TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                    if indices.len() >= MAX_NESTING {
                        return None;
                    }
                    indices.push(args[1]);
                    current = args[0];
                }
                TermData::Var(_, _) => break,
                _ => return None,
            }
        }
        indices.reverse();
        Some((current, indices))
    }

    /// The formatted model values of `indices`, as the flat scan resolves an
    /// index; `None` when one is decoupled or does not resolve.
    fn nested_index_path(
        terms: &TermStore,
        bv_model: &BvModel,
        indices: &[TermId],
        decoupled: &mut dyn FnMut(TermId) -> bool,
    ) -> Option<Vec<String>> {
        indices
            .iter()
            .map(|&index| {
                let Sort::BitVec(sort) = terms.sort(index) else {
                    return None;
                };
                if decoupled(index) {
                    return None;
                }
                let value = bv_model
                    .values
                    .get(&index)
                    .cloned()
                    .or_else(|| Self::evaluate_bv_expr(terms, index, &bv_model.values))?;
                Some(format_bitvec(&value, sort.width))
            })
            .collect()
    }

    /// The interpretation of the (inner) array of `sort` at `prefix`.
    fn nested_interp(
        sort: &Sort,
        prefix: &mut Vec<String>,
        cells: &NestedCells,
    ) -> Option<ArrayInterpretation> {
        let Sort::Array(array) = sort else {
            return None;
        };
        let element = &array.element_sort;
        let mut stores = Vec::new();
        let default = if matches!(element, Sort::Array(_)) {
            // Every inner index some read or default reaches, in order.
            let mut children: Vec<String> = Self::paths_below(&cells.leaves, prefix)
                .chain(Self::paths_below(&cells.defaults, prefix))
                .filter(|(key, _)| key.len() > prefix.len())
                .map(|(key, _)| key[prefix.len()].clone())
                .collect();
            children.sort();
            children.dedup();
            for child in children {
                prefix.push(child);
                let inner = Self::nested_interp(element, prefix, cells);
                let child = prefix.pop()?;
                stores.push((child, Self::render_array_cell(element, &inner?)?));
            }
            Self::render_array_cell(element, &Self::nested_fallback_interp(element)?)?
        } else {
            for (key, value) in Self::paths_below(&cells.leaves, prefix) {
                if let (true, Some(value)) = (key.len() == prefix.len() + 1, value) {
                    stores.push((key[prefix.len()].clone(), value.clone()));
                }
            }
            match cells.defaults.get(prefix.as_slice()) {
                Some(Some(value)) => value.clone(),
                _ => Self::nested_fallback_interp(sort)?.default?,
            }
        };
        // Newest first, so the rendered chain stores the lowest index innermost.
        stores.reverse();
        Some(ArrayInterpretation {
            index_sort: Some(array.index_sort.clone()),
            element_sort: Some(element.clone()),
            default: Some(default),
            stores,
        })
    }

    /// The entries of `map` whose path starts with `prefix`, in path order.
    fn paths_below<'a>(
        map: &'a BTreeMap<Vec<String>, Option<String>>,
        prefix: &'a [String],
    ) -> impl Iterator<Item = (&'a Vec<String>, &'a Option<String>)> + 'a {
        map.range(prefix.to_vec()..)
            .take_while(move |(key, _)| key.starts_with(prefix))
    }

    /// The constant array of `#b0..0` / `false` cells of `sort`, at every level.
    fn nested_fallback_interp(sort: &Sort) -> Option<ArrayInterpretation> {
        let Sort::Array(array) = sort else {
            return None;
        };
        let default = match &array.element_sort {
            Sort::BitVec(bv) => format_bitvec(&BigInt::from(0u8), bv.width),
            Sort::Bool => "false".to_string(),
            inner @ Sort::Array(_) => {
                Self::render_array_cell(inner, &Self::nested_fallback_interp(inner)?)?
            }
            _ => return None,
        };
        Some(ArrayInterpretation {
            index_sort: Some(array.index_sort.clone()),
            element_sort: Some(array.element_sort.clone()),
            default: Some(default),
            stores: Vec::new(),
        })
    }
}
