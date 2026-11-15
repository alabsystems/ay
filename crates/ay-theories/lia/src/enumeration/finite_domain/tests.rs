// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `count_free_fd_classes` checks its union-find forest once, not per lookup.

use super::super::union_find::whole_forest_scans;
use crate::LiaSolver;
use ay_core::kani_compat::DetHashMap;
use ay_core::term::{TermId, TermStore};
use ay_core::{Sort, TheorySolver};
use num_bigint::BigInt;

/// The whole-forest check was moved, not dropped: 1,023 equality edges (2,046
/// lookups) and 1,024 class lookups scan the forest exactly once in a debug
/// build (never in release, where `debug_assert!` is compiled out), where the
/// per-lookup form scanned it 3,070 times.
#[test]
fn count_free_fd_classes_checks_its_forest_once() {
    const N: usize = 1024;
    let mut store = TermStore::new();
    let vars: Vec<TermId> = (0..N)
        .map(|i| store.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    // x0 = x1 = ... = x1023: one equality class.
    let eqs: Vec<TermId> = vars
        .iter()
        .zip(vars.iter().skip(1))
        .map(|(&a, &b)| store.mk_eq(a, b))
        .collect();
    let mut lia = LiaSolver::new(&store);
    for &eq in &eqs {
        lia.assert_literal(eq, true);
    }
    let mut term_to_idx: DetHashMap<TermId, usize> = DetHashMap::default();
    for (i, &v) in vars.iter().enumerate() {
        term_to_idx.insert(v, i);
    }
    // Every column has a two-value domain, so every column is looked up.
    let domains = vec![vec![BigInt::from(0), BigInt::from(1)]; N];
    let before = whole_forest_scans();
    assert_eq!(lia.count_free_fd_classes(&term_to_idx, &domains), 1);
    assert_eq!(
        whole_forest_scans().saturating_sub(before),
        usize::from(cfg!(debug_assertions)),
        "one whole-forest check per call, zero per lookup"
    );
}
