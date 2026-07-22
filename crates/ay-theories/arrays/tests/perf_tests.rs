// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Performance regression tests for the array theory solver.
//!
//! These tests verify that known O(S²) and O(C1*C2) patterns in the array
//! solver's check() path don't cause unbounded blowups.

use ay_arrays::ArraySolver;
use ay_core::{Sort, TheorySolver};
use num_bigint::BigInt;
use std::time::Instant;

/// Performance regression: verify check() completes in bounded time with many
/// select terms. check_row2_extended and check_nested_select_conflicts both
/// iterate O(S²) over select_cache. With 50 indices, the pairwise loops
/// execute ~1225 iterations each.
#[test]
fn test_perf_many_selects_check_completes() {
    let mut store = ay_core::term::TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = store.mk_var("a", arr_sort);

    // Create 50 distinct index constants and corresponding select terms
    let n = 50;
    let mut indices = Vec::with_capacity(n);
    let mut selects = Vec::with_capacity(n);
    for k in 0..n {
        let idx = store.mk_int(BigInt::from(k));
        let sel = store.mk_select(a, idx);
        indices.push(idx);
        selects.push(sel);
    }

    // Build a store chain: store(store(...store(a, 0, v0)...), n-1, v_{n-1})
    // Also tests collect_effective_stores chain-walking (capped at 200)
    let mut current_arr = a;
    let mut values = Vec::with_capacity(n);
    for (idx, val_offset) in indices.iter().zip(0..n) {
        let val = store.mk_int(BigInt::from(100 + val_offset));
        current_arr = store.mk_store(current_arr, *idx, val);
        values.push(val);
    }

    // Create select terms on the stored array
    let mut stored_selects = Vec::with_capacity(n);
    for idx in &indices {
        let sel = store.mk_select(current_arr, *idx);
        stored_selects.push(sel);
    }

    // Pre-create all equality/disequality terms before borrowing store
    let eq_terms: Vec<_> = stored_selects
        .iter()
        .zip(values.iter())
        .map(|(&sel, &val)| store.mk_eq(sel, val))
        .collect();
    let diseq_terms: Vec<_> = selects
        .windows(2)
        .map(|w| store.mk_eq(w[0], w[1]))
        .collect();

    let mut solver = ArraySolver::new(&store);
    for &eq in &eq_terms {
        solver.assert_literal(eq, true);
    }
    for &diseq in &diseq_terms {
        solver.assert_literal(diseq, false);
    }

    let start = Instant::now();
    let result = solver.check();
    let elapsed = start.elapsed();

    assert!(
        matches!(result, ay_core::TheoryResult::Sat),
        "50-select consistent scenario should be SAT, got {result:?}"
    );

    // With ~100 total select terms, pairwise loops execute ~4950 iterations.
    assert!(
        elapsed.as_secs() < 5,
        "check() with 100 select terms took {elapsed:?} — exceeds 5s budget"
    );
}

/// Performance regression: verify known_distinct with large equivalence
/// classes doesn't cause O(C1*C2) blowup. Creates two equivalence classes
/// of size 10 each and checks that the cross-product iteration is bounded.
#[test]
fn test_perf_large_equiv_classes_known_distinct() {
    let mut store = ay_core::term::TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = store.mk_var("a", arr_sort);

    // Create two groups of index variables; each forms an equivalence class
    let class_size = 10;
    let mut group_a = Vec::with_capacity(class_size);
    let mut group_b = Vec::with_capacity(class_size);
    for k in 0..class_size {
        group_a.push(store.mk_var(&format!("ia_{k}"), Sort::Int));
        group_b.push(store.mk_var(&format!("ib_{k}"), Sort::Int));
    }

    // Pre-create all terms before borrowing store immutably for solver
    let eq_a_terms: Vec<_> = group_a[1..]
        .iter()
        .map(|&member| store.mk_eq(group_a[0], member))
        .collect();
    let eq_b_terms: Vec<_> = group_b[1..]
        .iter()
        .map(|&member| store.mk_eq(group_b[0], member))
        .collect();
    let diseq_term = store.mk_eq(group_a[0], group_b[0]);

    let sel_diseq_terms: Vec<_> = group_a
        .iter()
        .zip(group_b.iter())
        .map(|(&ga, &gb)| {
            let sel_a = store.mk_select(a, ga);
            let sel_b = store.mk_select(a, gb);
            store.mk_eq(sel_a, sel_b)
        })
        .collect();

    let mut solver = ArraySolver::new(&store);

    for &eq in &eq_a_terms {
        solver.assert_literal(eq, true);
    }
    for &eq in &eq_b_terms {
        solver.assert_literal(eq, true);
    }
    solver.assert_literal(diseq_term, false);
    for &sel_eq in &sel_diseq_terms {
        solver.assert_literal(sel_eq, false);
    }

    let start = Instant::now();
    let result = solver.check();
    let elapsed = start.elapsed();

    // known_distinct expands both equiv classes (10 each), checks 100
    // cross-product pairs.
    assert!(
        matches!(result, ay_core::TheoryResult::Sat),
        "Large equiv class scenario should be SAT, got {result:?}"
    );
    assert!(
        elapsed.as_secs() < 5,
        "check() with 10-element equiv classes took {elapsed:?} — exceeds 5s budget"
    );
}
