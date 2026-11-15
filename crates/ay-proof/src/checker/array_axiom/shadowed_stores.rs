// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unconditional elimination of writes shadowed by a later identical index.
//!
//! Walk each chain from the last write to the first, retaining the first
//! occurrence of each syntactically identical index. Two chains over the same
//! base with identical ordered retained writes denote the same array. Different
//! index terms may alias: their relative order is preserved, never sorted.
//! At an arbitrary read index, both chains therefore find the same first
//! matching retained write, or read their common base. No disjointness premise
//! or claim about the array base (which may be an opaque call result) is used.

use super::{equality_sides, well_sorted_store_parts};
use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

pub(crate) const MAX_SHADOWED_STORES: usize = 128;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Write {
    pub outer: TermId,
    pub inner: TermId,
    pub index: TermId,
    pub value: TermId,
}

pub(crate) struct ShadowedStores {
    pub left: TermId,
    pub right: TermId,
    pub base: TermId,
    pub left_writes: Vec<Write>,
    pub right_writes: Vec<Write>,
    pub retained: Vec<(TermId, TermId)>,
}

/// Exact unit equality, with at least one overwritten write removed. Every
/// traversed store signature is rechecked, including discarded writes.
pub(crate) fn shadowed_stores(terms: &TermStore, clause: &[TermId]) -> Option<ShadowedStores> {
    let [equality] = clause else { return None };
    let (left, right) = equality_sides(terms, *equality)?;
    if !matches!(terms.sort(left), Sort::Array(_)) || terms.sort(left) != terms.sort(right) {
        return None;
    }
    let (base, left_writes) = chain(terms, left)?;
    let (other_base, right_writes) = chain(terms, right)?;
    if base != other_base {
        return None;
    }
    let retained = retain_last(&left_writes);
    let other = retain_last(&right_writes);
    if retained != other || left_writes.len() == retained.len() && right_writes.len() == other.len()
    {
        return None;
    }
    Some(ShadowedStores {
        left,
        right,
        base,
        left_writes,
        right_writes,
        retained,
    })
}

fn chain(terms: &TermStore, mut array: TermId) -> Option<(TermId, Vec<Write>)> {
    let mut writes = Vec::new();
    while matches!(terms.get(array), TermData::App(Symbol::Named(op), _) if op == "store") {
        if writes.len() == MAX_SHADOWED_STORES {
            return None;
        }
        let (inner, index, value) = well_sorted_store_parts(terms, array)?;
        writes.push(Write {
            outer: array,
            inner,
            index,
            value,
        });
        array = inner;
    }
    Some((array, writes))
}

fn retain_last(writes: &[Write]) -> Vec<(TermId, TermId)> {
    let mut seen = DetHashSet::default();
    writes
        .iter()
        .filter_map(|write| {
            seen.insert(write.index)
                .then_some((write.index, write.value))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::ProofId;

    #[test]
    fn shadowed_store_validation_honors_every_resource_poll() {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Int, Sort::Int);
        let base = terms.mk_var("a", sort.clone());
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let u = terms.mk_var("u", Sort::Int);
        let v = terms.mk_var("v", Sort::Int);
        let mut store =
            |a, index, value| terms.mk_app(Symbol::named("store"), [a, index, value], sort.clone());
        let one = store(base, i, u);
        let two = store(one, j, u);
        let left = store(two, i, v);
        let one = store(base, j, u);
        let right = store(one, i, v);
        let eq = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        let mut polls = Vec::new();
        super::super::validate_array_row_chain(&terms, ProofId(0), &[eq], &mut |work, bytes| {
            polls.push((work, bytes));
            true
        })
        .unwrap();
        assert!(polls
            .iter()
            .any(|&(work, bytes)| work >= 768 && bytes >= 768));
        for stop in 0..polls.len() {
            let mut calls = 0;
            let result =
                super::super::validate_array_row_chain(&terms, ProofId(0), &[eq], &mut |_, _| {
                    calls += 1;
                    calls <= stop
                });
            assert!(matches!(result, Err(crate::ProofCheckError::ResourceLimit)));
            assert_eq!(calls, stop + 1);
        }
    }
}
