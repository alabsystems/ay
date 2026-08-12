// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused tests for bounded authored-root collection in the BV/LIA rebuild.

use super::*;

#[test]
fn root_collection_is_bounded_and_deduplicated() {
    let mut terms = TermStore::new();
    let repeated = terms.mk_var("bv_lia_repeated_root", Sort::Bool);
    let repeated_roots = vec![repeated; ay_proof::MAX_BV_LIA_QUERY_ROOTS * 4];
    assert_eq!(
        collect_bounded_bv_lia_roots(&terms, &repeated_roots),
        Some(vec![repeated])
    );

    let distinct: Vec<_> = (0..=ay_proof::MAX_BV_LIA_QUERY_ROOTS)
        .map(|index| terms.mk_var(format!("bv_lia_distinct_root_{index}"), Sort::Bool))
        .collect();
    assert_eq!(
        collect_bounded_bv_lia_roots(&terms, &distinct[..ay_proof::MAX_BV_LIA_QUERY_ROOTS]),
        Some(distinct[..ay_proof::MAX_BV_LIA_QUERY_ROOTS].to_vec())
    );
    assert!(collect_bounded_bv_lia_roots(&terms, &distinct).is_none());
}
