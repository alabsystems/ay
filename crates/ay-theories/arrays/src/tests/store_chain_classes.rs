// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction gives an equivalence class that holds a store chain one
//! value (`reconcile_store_chain_classes`, 2026-09-24/25 arrays fix-up) -- in
//! the SECOND candidate, `ArrayModel::store_chain_class_candidate`
//! (#store-chain-class-candidate); the first stays the per-term model.

use super::*;
use num_bigint::BigInt;

/// The reconciled interpretations: the class candidate when the
/// reconciliation changed the model, else the model itself.
fn class_model(model: &ArrayModel) -> &HashMap<TermId, ArrayInterpretation> {
    model
        .store_chain_class_candidate
        .as_ref()
        .unwrap_or(&model.array_values)
}

/// A class over TWO free bases shares one else value: `(= (store b 1 5)
/// (store c 1 5))` needs `b` and `c` to agree off index 1, and left open each
/// gets its own from completion and the printed model falsifies the equality
/// (the hunt's d4b_free_bases witness). The value is an observed cell value.
#[test]
fn test_two_free_bases_share_one_else_value() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let five = store.mk_int(BigInt::from(5));
    let b1 = store.mk_store(b, one, five);
    let c1 = store.mk_store(c, one, five);
    let eq = store.mk_eq(b1, c1);
    let read_b = store.mk_select(b, two);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let mut term_values = HashMap::default();
    for (term, value) in [(one, "1"), (two, "2"), (five, "5"), (read_b, "5")] {
        term_values.insert(term, value.to_string());
    }
    let model = solver.extract_model(&term_values);
    let default_of = |array: TermId| {
        class_model(&model)
            .get(&array)
            .and_then(|interp| interp.default.clone())
    };
    assert!(
        default_of(b).is_some(),
        "b: {:?}",
        class_model(&model).get(&b)
    );
    assert_eq!(
        default_of(b),
        default_of(c),
        "one class shares one else value"
    );
}

/// A const-array base fixes the class's else value: `(= (store K3 1 5)
/// (store b 2 7))` makes `b` read 3 off indices 1 and 2. The reconciliation
/// looked for a fixed default only on interpretations, and a const-array term
/// gets one only when its value term has a model value -- here, as on fresh
/// storeeq_2609_0475 --z3-mode, the literal `3` has none -- so it invented one
/// and printed `b` with the wrong else value (`sat` -> `unknown`).
#[test]
fn test_const_array_base_fixes_the_class_else_value() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));
    let five = store.mk_int(BigInt::from(5));
    let seven = store.mk_int(BigInt::from(7));
    let k3 = store.mk_const_array(Sort::Int, three);
    let lhs = store.mk_store(k3, one, five);
    let rhs = store.mk_store(b, two, seven);
    let eq = store.mk_eq(lhs, rhs);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let mut term_values = HashMap::default();
    for (term, value) in [(one, "1"), (two, "2"), (five, "5"), (seven, "7")] {
        term_values.insert(term, value.to_string());
    }
    let model = solver.extract_model(&term_values);
    assert_eq!(
        class_model(&model)
            .get(&b)
            .and_then(|interp| interp.default.as_deref()),
        Some("3"),
        "b agrees with (as const 3) off the written indices: {:?}",
        class_model(&model).get(&b)
    );
}

/// A class over ONE free base invents no else value: completion derives the
/// base's from its own reads and definitions. `(= x (store b 1 5))` with
/// `b[2] = 7` used to give `b` and `x` the invented else value 7, which fought
/// the value a read at a store-missed index needed (differential-fuzz arrays
/// seed 179, `sat` -> `unknown`).
#[test]
fn test_single_free_base_class_invents_no_else_value() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort.clone());
    let x = store.mk_var("x", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let five = store.mk_int(BigInt::from(5));
    let seven = store.mk_int(BigInt::from(7));
    let chain = store.mk_store(b, one, five);
    let eq = store.mk_eq(x, chain);
    let read = store.mk_select(b, two);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let mut term_values = HashMap::default();
    for (term, value) in [
        (one, "1"),
        (two, "2"),
        (five, "5"),
        (seven, "7"),
        (read, "7"),
    ] {
        term_values.insert(term, value.to_string());
    }
    let model = solver.extract_model(&term_values);
    assert_eq!(
        class_model(&model)
            .get(&b)
            .and_then(|interp| interp.default.clone()),
        None,
        "a single free base keeps its else value open for completion: {:?}",
        class_model(&model).get(&b)
    );
}

/// A const-array base denotes its default at every index: the class
/// reconciliation never writes cells into it (a cell observed on another
/// member at an unwritten index is the class's value there, and in any
/// consistent assignment it equals the const default anyway).
#[test]
fn test_const_array_base_gets_no_filled_cells() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let three = store.mk_int(BigInt::from(3));
    let five = store.mk_int(BigInt::from(5));
    let k0 = store.mk_const_array(Sort::Int, zero);
    let lhs = store.mk_store(k0, one, five);
    let rhs = store.mk_store(b, one, five);
    let eq = store.mk_eq(lhs, rhs);
    let read = store.mk_select(b, three);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let mut term_values = HashMap::default();
    for (term, value) in [
        (zero, "0"),
        (one, "1"),
        (three, "3"),
        (five, "5"),
        (read, "0"),
    ] {
        term_values.insert(term, value.to_string());
    }
    let model = solver.extract_model(&term_values);
    assert!(
        class_model(&model)
            .get(&k0)
            .is_none_or(|interp| interp.stores.is_empty()),
        "the const-array base must not carry filled cells: {:?}",
        class_model(&model).get(&k0)
    );
}

/// The class reconciliation is the SECOND candidate
/// (#store-chain-class-candidate): the first model stays the per-term
/// construction, and the reconciled one rides along only when it differs.
/// Reconciling in place cost fresh incr2_2809_0051's second query (`sat` on
/// main): it gave `c` cells of `(store a k 5)` against
/// `(= (as const 1) (store c k 1))`, while the per-term model was valid.
#[test]
fn test_class_reconciliation_is_the_second_candidate() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let five = store.mk_int(BigInt::from(5));
    let b1 = store.mk_store(b, one, five);
    let c1 = store.mk_store(c, one, five);
    let eq = store.mk_eq(b1, c1);
    let read_b = store.mk_select(b, two);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let mut term_values = HashMap::default();
    for (term, value) in [(one, "1"), (two, "2"), (five, "5"), (read_b, "5")] {
        term_values.insert(term, value.to_string());
    }
    let model = solver.extract_model(&term_values);
    let candidate = model
        .store_chain_class_candidate
        .as_ref()
        .expect("the reconciliation changes this model, so it must ride along");
    let default_in = |values: &HashMap<TermId, ArrayInterpretation>, array: TermId| {
        values.get(&array).and_then(|interp| interp.default.clone())
    };
    assert!(
        default_in(candidate, b).is_some(),
        "{:?}",
        candidate.get(&b)
    );
    assert_eq!(default_in(candidate, b), default_in(candidate, c));
    assert_ne!(
        model.array_values.get(&c),
        candidate.get(&c),
        "the first model is the per-term construction, not the reconciled one"
    );
}

/// No store chain in any class: nothing to reconcile, no second candidate.
#[test]
fn test_no_class_candidate_without_a_store_chain_class() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let b = store.mk_var("b", arr_sort.clone());
    let c = store.mk_var("c", arr_sort);
    let two = store.mk_int(BigInt::from(2));
    let eq = store.mk_eq(b, c);
    let read_b = store.mk_select(b, two);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq, true);
    solver.populate_caches();

    let mut term_values = HashMap::default();
    for (term, value) in [(two, "2"), (read_b, "4")] {
        term_values.insert(term, value.to_string());
    }
    let model = solver.extract_model(&term_values);
    assert!(
        model.store_chain_class_candidate.is_none(),
        "{:?}",
        model.store_chain_class_candidate
    );
}
