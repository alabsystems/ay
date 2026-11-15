// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed McCarthy miss steps. No replacement term or store value is constructed.

use super::*;

#[derive(Default)]
pub(super) struct Misses {
    count: usize,
    edges: Vec<(TermId, TermId)>,
}

impl Misses {
    pub(super) fn len(&self) -> usize {
        self.count
    }

    pub(super) fn into_edges(self) -> Vec<(TermId, TermId)> {
        self.edges
    }

    pub(super) fn peel(
        &mut self,
        cx: &mut Classifier<'_>,
        select: TermId,
        mut array: TermId,
        index: TermId,
        path_depth: usize,
    ) -> Option<TermId> {
        if !is_store(cx.terms, array) {
            return Some(array);
        }
        if !matches!(cx.terms.get(select), TermData::App(Symbol::Named(name), _) if name == "select")
        {
            return None;
        }
        let before = cx.witness_value_work;
        let read_key = cx.inner_index(select, array, index)?;
        let read_cost = cx.witness_value_work.checked_sub(before)?;
        let mut parent = select;
        while is_store(cx.terms, array) {
            if path_depth.checked_add(self.count)? >= MAX_CLASSIFY_DEPTH
                || !cx.spend_classify_work(1)
                || cx.model.projection_argument(array).ok()?.is_some()
            {
                return None;
            }
            let TermData::App(Symbol::Named(name), arguments) = cx.terms.get(array) else {
                return None;
            };
            let [base, key, value] = arguments.as_slice() else {
                return None;
            };
            if name != "store" {
                return None;
            }
            let sort = cx.terms.sort(array);
            for actual in [
                sort,
                cx.terms.sort(*base),
                cx.terms.sort(*key),
                cx.terms.sort(*value),
            ] {
                if !metadata::sort_work(actual, 0, &mut |n| cx.spend_classify_work(n)) {
                    return None;
                }
            }
            let Sort::Array(array_sort) = sort else {
                return None;
            };
            if cx.terms.sort(*base) != sort
                || cx.terms.sort(*key) != &array_sort.index_sort
                || cx.terms.sort(*value) != &array_sort.element_sort
            {
                return None;
            }
            let before = cx.witness_value_work;
            let store_key = cx.typed_key(*key, &array_sort.index_sort)?;
            let store_cost = cx.witness_value_work.checked_sub(before)?;
            // Semantic array/sequence keys can compare entries pairwise. Both
            // payload scans and this product debit are monotone across OR trials.
            if !cx.spend_classify_work(read_cost.checked_mul(store_cost)?)
                || !matches!(crate::value_eq(&read_key, &store_key), Ok(false))
            {
                return None;
            }
            self.push_edge(parent, array, cx)?;
            self.count += 1;
            parent = array;
            array = *base;
        }
        self.push_edge(parent, array, cx)?;
        Some(array)
    }

    fn push_edge(&mut self, parent: TermId, child: TermId, cx: &mut Classifier<'_>) -> Option<()> {
        if !cx.spend_classify_work(std::mem::size_of::<(TermId, TermId)>()) {
            return None;
        }
        self.edges.try_reserve(1).ok()?;
        self.edges.push((parent, child));
        Some(())
    }
}

pub(in crate::residual) fn is_store(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::App(Symbol::Named(name), _)
        if name == "store" && !terms.is_declared_function("store"))
}

/// Permissions apply to one operand-zero use, never to a shared store node.
#[derive(Default)]
pub(in crate::residual) struct StoreEdges {
    edges: HashSet<(TermId, TermId)>,
}

impl StoreEdges {
    pub(in crate::residual) fn admit(
        &mut self,
        edges: Vec<(TermId, TermId)>,
        cx: &mut Classifier<'_>,
    ) -> Option<()> {
        // Prepay the complete union reservation, including duplicate entries.
        let work = edges
            .len()
            .checked_mul(std::mem::size_of::<(TermId, TermId)>())?
            .checked_mul(2)?;
        if !cx.spend_classify_work(work) {
            return None;
        }
        self.edges.try_reserve(edges.len()).ok()?;
        self.edges.extend(edges);
        Some(())
    }

    pub(in crate::residual) fn permits(
        &self,
        parent: TermId,
        child: TermId,
        position: usize,
    ) -> bool {
        position == 0 && self.edges.contains(&(parent, child))
    }
}
