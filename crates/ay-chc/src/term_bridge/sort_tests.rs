// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{chc_sort_to_core, core_sort_to_chc_lossy, core_sort_to_chc_strict};
use crate::expr::{ChcDtConstructor, ChcDtSelector, ChcSort};
use ay_core::Sort;
use std::sync::Arc;

#[test]
fn lossy_core_sort_conversion_preserves_legacy_fallbacks() {
    assert_eq!(
        core_sort_to_chc_lossy(&Sort::String),
        ChcSort::Uninterpreted("String".to_string())
    );
    assert_eq!(
        core_sort_to_chc_lossy(&Sort::FloatingPoint(8, 24)),
        ChcSort::Uninterpreted("FloatingPoint_8_24".to_string())
    );
}

#[test]
fn strict_core_sort_conversion_rejects_unsupported_sorts() {
    assert_eq!(core_sort_to_chc_strict(&Sort::String), None);
    assert_eq!(
        core_sort_to_chc_strict(&Sort::Uninterpreted("U".to_string())),
        None
    );
}

#[test]
fn chc_to_core_roundtrip_on_supported_sorts() {
    let sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::BitVec(8)));
    assert_eq!(core_sort_to_chc_lossy(&chc_sort_to_core(&sort)), sort);
}

#[test]
fn recursive_datatype_canonicalizes_self_reference_to_same_core_sort() {
    let shallow_list = ChcSort::Datatype {
        name: "listOfInt".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "conslistOfInt".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "headlistOfInt".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "taillistOfInt".to_string(),
                    sort: ChcSort::Uninterpreted("listOfInt".to_string()),
                },
            ],
        }]),
    };
    let expanded_list = ChcSort::Datatype {
        name: "listOfInt".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "conslistOfInt".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "headlistOfInt".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "taillistOfInt".to_string(),
                    sort: shallow_list.clone(),
                },
            ],
        }]),
    };

    assert_eq!(
        chc_sort_to_core(&expanded_list),
        chc_sort_to_core(&shallow_list)
    );
}
