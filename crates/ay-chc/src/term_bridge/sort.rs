// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared CHC/core sort conversion policy.

use crate::expr::{ChcDtConstructor, ChcDtSelector, ChcSort};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use std::sync::Arc;

/// Convert CHC sort into ay-core sort.
pub(crate) fn chc_sort_to_core(sort: &ChcSort) -> Sort {
    chc_sort_to_core_seen(sort, &mut FxHashSet::default())
}

fn chc_sort_to_core_seen(sort: &ChcSort, seen_datatypes: &mut FxHashSet<String>) -> Sort {
    match sort {
        ChcSort::Bool => Sort::Bool,
        ChcSort::Int => Sort::Int,
        ChcSort::Real => Sort::Real,
        ChcSort::BitVec(w) => Sort::bitvec(*w),
        ChcSort::Array(key, val) => Sort::array(
            chc_sort_to_core_seen(key, seen_datatypes),
            chc_sort_to_core_seen(val, seen_datatypes),
        ),
        ChcSort::Uninterpreted(name) => Sort::Uninterpreted(name.clone()),
        ChcSort::Datatype { name, constructors } => {
            if !seen_datatypes.insert(name.clone()) {
                return Sort::Uninterpreted(name.clone());
            }
            let core_constructors = constructors
                .iter()
                .map(|ctor| {
                    DatatypeConstructor::new(
                        ctor.name.clone(),
                        ctor.selectors
                            .iter()
                            .map(|sel| {
                                DatatypeField::new(
                                    sel.name.clone(),
                                    chc_sort_to_core_seen(&sel.sort, seen_datatypes),
                                )
                            })
                            .collect(),
                    )
                })
                .collect();
            seen_datatypes.remove(name);
            Sort::Datatype(DatatypeSort::new(name.clone(), core_constructors))
        }
    }
}

/// Convert ay-core sort into CHC sort with permissive fallback.
///
/// This preserves legacy behavior used by `From<Sort> for ChcSort`, where
/// unsupported theory sorts are represented as CHC uninterpreted sorts.
pub(crate) fn core_sort_to_chc_lossy(sort: &Sort) -> ChcSort {
    match sort {
        Sort::Bool => ChcSort::Bool,
        Sort::Int => ChcSort::Int,
        Sort::Real => ChcSort::Real,
        Sort::BitVec(bv) => ChcSort::BitVec(bv.width),
        Sort::Array(arr) => ChcSort::Array(
            Box::new(core_sort_to_chc_lossy(&arr.index_sort)),
            Box::new(core_sort_to_chc_lossy(&arr.element_sort)),
        ),
        Sort::String => ChcSort::Uninterpreted("String".to_string()),
        Sort::RegLan => ChcSort::Uninterpreted("RegLan".to_string()),
        Sort::FloatingPoint(e, s) => ChcSort::Uninterpreted(format!("FloatingPoint_{e}_{s}")),
        Sort::Uninterpreted(name) => ChcSort::Uninterpreted(name.clone()),
        Sort::Datatype(dt) => ChcSort::Datatype {
            name: dt.name.clone(),
            constructors: Arc::new(
                dt.constructors
                    .iter()
                    .map(|ctor| ChcDtConstructor {
                        name: ctor.name.clone(),
                        selectors: ctor
                            .fields
                            .iter()
                            .map(|f| ChcDtSelector {
                                name: f.name.clone(),
                                sort: core_sort_to_chc_lossy(&f.sort),
                            })
                            .collect(),
                    })
                    .collect(),
            ),
        },
        Sort::Seq(elem) => ChcSort::Uninterpreted(format!("Seq_{}", core_sort_to_chc_lossy(elem))),
        // Unknown Sort variant; map to Uninterpreted (#6091).
        _ => ChcSort::Uninterpreted("Unknown".to_string()),
    }
}

/// Convert ay-core sort into CHC sort for model extraction.
///
/// This strict path returns `None` for unsupported theory sorts to preserve
/// existing decode behavior in `term_to_chc_expr`.
pub(crate) fn core_sort_to_chc_strict(sort: &Sort) -> Option<ChcSort> {
    match sort {
        Sort::Bool => Some(ChcSort::Bool),
        Sort::Int => Some(ChcSort::Int),
        Sort::Real => Some(ChcSort::Real),
        Sort::BitVec(bv) => Some(ChcSort::BitVec(bv.width)),
        Sort::Array(arr) => Some(ChcSort::Array(
            Box::new(core_sort_to_chc_strict(&arr.index_sort)?),
            Box::new(core_sort_to_chc_strict(&arr.element_sort)?),
        )),
        Sort::Datatype(dt) => Some(ChcSort::Datatype {
            name: dt.name.clone(),
            constructors: Arc::new(
                dt.constructors
                    .iter()
                    .map(|ctor| ChcDtConstructor {
                        name: ctor.name.clone(),
                        selectors: ctor
                            .fields
                            .iter()
                            .map(|f| ChcDtSelector {
                                name: f.name.clone(),
                                sort: core_sort_to_chc_lossy(&f.sort),
                            })
                            .collect(),
                    })
                    .collect(),
            ),
        }),
        Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(_, _)
        | Sort::Uninterpreted(_)
        | Sort::Seq(_) => None,
        // Unknown Sort variant; unsupported (#6091).
        _ => None,
    }
}

#[cfg(test)]
#[path = "sort_tests.rs"]
mod tests;
