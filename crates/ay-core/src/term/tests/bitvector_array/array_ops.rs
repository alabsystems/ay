// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

// ==================== Array Operations Tests ====================

#[test]
fn test_array_select_basic() {
    let mut store = TermStore::new();

    // Create array: (Array Int Int)
    let arr = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let idx = store.mk_int(BigInt::from(0));

    let selected = store.mk_select(arr, idx);

    // Result should have element sort (Int)
    assert_eq!(store.sort(selected), &Sort::Int);
}

#[test]
fn test_array_store_basic() {
    let mut store = TermStore::new();

    // Create array: (Array Int Int)
    let arr = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let idx = store.mk_int(BigInt::from(0));
    let val = store.mk_int(BigInt::from(42));

    let stored = store.mk_store(arr, idx, val);

    // Result should have same sort as input array
    assert_eq!(store.sort(stored), &Sort::array(Sort::Int, Sort::Int));
}

#[test]
fn test_array_read_over_write_same_index() {
    let mut store = TermStore::new();

    // Create array: (Array Int Int)
    let arr = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let idx = store.mk_int(BigInt::from(0));
    let val = store.mk_int(BigInt::from(42));

    // select(store(a, 0, 42), 0) should simplify to 42
    let stored = store.mk_store(arr, idx, val);
    let selected = store.mk_select(stored, idx);

    assert_eq!(selected, val);
}

#[test]
fn test_array_read_over_write_different_constant_index() {
    let mut store = TermStore::new();

    // Create array: (Array Int Int)
    let arr = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let idx1 = store.mk_int(BigInt::from(0));
    let idx2 = store.mk_int(BigInt::from(1));
    let val = store.mk_int(BigInt::from(42));

    // select(store(a, 0, 42), 1) should simplify to select(a, 1)
    let stored = store.mk_store(arr, idx1, val);
    let selected = store.mk_select(stored, idx2);

    // Should be select(a, 1)
    let expected = store.mk_select(arr, idx2);
    assert_eq!(selected, expected);
}

#[test]
fn test_array_store_over_store_same_index() {
    let mut store = TermStore::new();

    // Create array: (Array Int Int)
    let arr = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let idx = store.mk_int(BigInt::from(0));
    let val1 = store.mk_int(BigInt::from(10));
    let val2 = store.mk_int(BigInt::from(20));

    // store(store(a, 0, 10), 0, 20) should simplify to store(a, 0, 20)
    let stored1 = store.mk_store(arr, idx, val1);
    let stored2 = store.mk_store(stored1, idx, val2);

    let expected = store.mk_store(arr, idx, val2);
    assert_eq!(stored2, expected);
}

#[test]
fn test_array_with_bitvec_index() {
    let mut store = TermStore::new();

    // Create array: (Array (_ BitVec 8) Int)
    let arr = store.mk_var("a", Sort::array(Sort::bitvec(8), Sort::Int));
    let idx = store.mk_bitvec(BigInt::from(5), 8);
    let val = store.mk_int(BigInt::from(100));

    // Basic store/select
    let stored = store.mk_store(arr, idx, val);
    let selected = store.mk_select(stored, idx);

    assert_eq!(selected, val);
}

#[test]
fn test_array_read_over_write_different_bv_constant_index() {
    let mut store = TermStore::new();

    // Create array: (Array (_ BitVec 8) Int)
    let arr = store.mk_var("a", Sort::array(Sort::bitvec(8), Sort::Int));
    let idx1 = store.mk_bitvec(BigInt::from(5), 8);
    let idx2 = store.mk_bitvec(BigInt::from(10), 8);
    let val = store.mk_int(BigInt::from(100));

    // select(store(a, 5, 100), 10) should simplify to select(a, 10)
    let stored = store.mk_store(arr, idx1, val);
    let selected = store.mk_select(stored, idx2);

    let expected = store.mk_select(arr, idx2);
    assert_eq!(selected, expected);
}

#[test]
fn test_const_array_basic() {
    let mut store = TermStore::new();

    // Create constant array: ((as const (Array Int Bool)) true)
    let default_val = store.mk_bool(true);
    let const_arr = store.mk_const_array(Sort::Int, default_val);

    // Check sort
    assert_eq!(store.sort(const_arr), &Sort::array(Sort::Int, Sort::Bool));

    // Check we can retrieve the default value
    assert_eq!(store.get_const_array(const_arr), Some(default_val));
}

#[test]
fn test_const_array_read_simplification() {
    let mut store = TermStore::new();

    // Create constant array with default value 42
    let default_val = store.mk_int(BigInt::from(42));
    let const_arr = store.mk_const_array(Sort::Int, default_val);

    // select(const-array(42), i) should simplify to 42 for any index
    let idx = store.mk_int(BigInt::from(100));
    let selected = store.mk_select(const_arr, idx);

    // Should simplify to the default value
    assert_eq!(selected, default_val);
}

#[test]
fn test_array_default_preserves_stores_over_bool_carrier() {
    let mut store = TermStore::new();
    let false_term = store.mk_bool(false);
    let true_term = store.mk_bool(true);
    let base = store.mk_const_array(Sort::Bool, false_term);
    let at_false = store.mk_store(base, false_term, true_term);
    let all_true = store.mk_store(at_false, true_term, true_term);

    let default = store.mk_array_default(all_true);

    assert_eq!(store.get_array_default(default), Some(all_true));
    assert_ne!(default, false_term);
}

#[test]
fn test_array_default_preserves_stores_over_finite_bitvec_carrier() {
    let mut store = TermStore::new();
    let false_term = store.mk_bool(false);
    let true_term = store.mk_bool(true);
    let zero = store.mk_bitvec(BigInt::from(0), 1);
    let one = store.mk_bitvec(BigInt::from(1), 1);
    let base = store.mk_const_array(Sort::bitvec(1), false_term);
    let at_zero = store.mk_store(base, zero, true_term);
    let all_true = store.mk_store(at_zero, one, true_term);

    let default = store.mk_array_default(all_true);

    assert_eq!(store.get_array_default(default), Some(all_true));
    assert_ne!(default, false_term);
}

#[test]
fn test_const_array_with_store() {
    let mut store = TermStore::new();

    // Create constant array with default value 0
    let default_val = store.mk_int(BigInt::from(0));
    let const_arr = store.mk_const_array(Sort::Int, default_val);

    // Store a different value at index 5
    let idx5 = store.mk_int(BigInt::from(5));
    let val = store.mk_int(BigInt::from(100));
    let stored = store.mk_store(const_arr, idx5, val);

    // select(store(const-array(0), 5, 100), 5) should give 100
    let select_at_5 = store.mk_select(stored, idx5);
    assert_eq!(select_at_5, val);

    // select(store(const-array(0), 5, 100), 10) should give 0 (the default)
    let idx10 = store.mk_int(BigInt::from(10));
    let select_at_10 = store.mk_select(stored, idx10);
    assert_eq!(select_at_10, default_val);
}

#[test]
fn test_const_array_store_same_value_eliminates() {
    let mut store = TermStore::new();

    let default_val = store.mk_int(BigInt::from(0));
    let const_arr = store.mk_const_array(Sort::Int, default_val);
    let idx5 = store.mk_int(BigInt::from(5));

    let stored_same = store.mk_store(const_arr, idx5, default_val);
    assert_eq!(
        stored_same, const_arr,
        "store(const-array(v), i, v) should return the original const-array"
    );
}

/// Identity store elimination: store(a, i, select(a, i)) → a
/// Z3 reference: array_rewriter.cpp:192-201
/// This optimization removes no-op stores where the value being written
/// is already the value at that index. Critical for storeinv benchmarks (#6282).
#[test]
fn test_identity_store_elimination() {
    let mut ts = TermStore::new();

    // Create array variable
    let arr = ts.intern(
        TermData::Var("a".to_string(), 0),
        Sort::array(Sort::Int, Sort::Int),
    );
    let idx = ts.intern(TermData::Var("i".to_string(), 0), Sort::Int);

    // select(a, i) → creates a select term
    let sel = ts.mk_select(arr, idx);

    // store(a, i, select(a, i)) → should return a (identity elimination)
    let stored = ts.mk_store(arr, idx, sel);
    assert_eq!(
        stored, arr,
        "Identity store elimination: store(a, i, select(a, i)) should return a"
    );

    // Negative case: store(a, i, select(b, i)) should NOT eliminate
    let arr_b = ts.intern(
        TermData::Var("b".to_string(), 0),
        Sort::array(Sort::Int, Sort::Int),
    );
    let sel_b = ts.mk_select(arr_b, idx);
    let stored_cross = ts.mk_store(arr, idx, sel_b);
    assert_ne!(
        stored_cross, arr,
        "Cross-array store should NOT be eliminated: store(a, i, select(b, i))"
    );

    // Negative case: store(a, i, select(a, j)) should NOT eliminate (different index)
    let idx_j = ts.intern(TermData::Var("j".to_string(), 0), Sort::Int);
    let sel_j = ts.mk_select(arr, idx_j);
    let stored_diff_idx = ts.mk_store(arr, idx, sel_j);
    assert_ne!(
        stored_diff_idx, arr,
        "Different-index select should NOT be eliminated: store(a, i, select(a, j))"
    );

    // Concrete case: store(const-array(0), 5, select(const-array(0), 5)) → const-array(0)
    let zero = ts.mk_int(BigInt::from(0));
    let const_arr = ts.mk_const_array(Sort::Int, zero);
    let idx5 = ts.mk_int(BigInt::from(5));
    // select(const-array(0), 5) → 0 (by read-over-const simplification)
    let sel_const = ts.mk_select(const_arr, idx5);
    assert_eq!(sel_const, zero, "Read-over-const should simplify");
    // store(const-array(0), 5, 0) now simplifies via the dedicated
    // store(const-array(v), i, v) -> const-array(v) rewrite.
    let stored_const = ts.mk_store(const_arr, idx5, zero);
    assert_eq!(
        stored_const, const_arr,
        "Writing the default value back into a const-array should be eliminated"
    );
}

/// squash_store: store(store(store(a, i, v1), j, w), i, v2) collapses
/// the inner store at index i when j is provably distinct from i.
/// Z3 ref: array_rewriter.cpp:206-239
#[test]
fn test_squash_store_concrete_indices() {
    let mut ts = TermStore::new();
    let arr = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = ts.mk_int(BigInt::from(1));
    let j = ts.mk_int(BigInt::from(2));
    let v1 = ts.mk_int(BigInt::from(10));
    let v2 = ts.mk_int(BigInt::from(20));
    let w = ts.mk_int(BigInt::from(30));

    // Build store(store(store(a, 1, 10), 2, 30), 1, 20)
    let s1 = ts.mk_store(arr, i, v1); // store(a, 1, 10)
    let s2 = ts.mk_store(s1, j, w); // store(store(a, 1, 10), 2, 30)
    let s3 = ts.mk_store(s2, i, v2); // store(store(store(a, 1, 10), 2, 30), 1, 20)

    // Should collapse to store(store(a, 2, 30), 1, 20)
    // (the inner store at index 1 with value 10 is dead)
    let inner_expected = ts.mk_store(arr, j, w);
    let expected = ts.mk_store(inner_expected, i, v2);
    assert_eq!(
        s3, expected,
        "squash_store should eliminate dead inner store at same index"
    );
}

/// Symbolic store indices are NOT commuted at the term level (#6367).
///
/// `store(store(a, j, w), i, v)` with symbolic i, j stays as-is.
/// The theory solver handles index equality/disequality reasoning at runtime
/// via ROW1/ROW2 lemmas. ITE-guard expansion was removed because it caused
/// O(2^N) blowup on storeinv-family benchmarks.
///
/// Z3 ref: array_rewriter.cpp:130-139 returns l_undef for symbolic indices,
/// blocking sort_store. Only concrete constants go through are_distinct().
#[test]
fn test_sort_store_symbolic_indices_are_not_commuted() {
    let mut ts = TermStore::new();
    let arr = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = ts.mk_var("i", Sort::Int);
    let j = ts.mk_var("j", Sort::Int);
    let v = ts.mk_int(BigInt::from(10));
    let w = ts.mk_int(BigInt::from(20));

    // store(store(a, j, 20), i, 10) — with symbolic i, j
    let inner = ts.mk_store(arr, j, w);
    let outer = ts.mk_store(inner, i, v);

    // With symbolic indices, mk_store does NOT rewrite: the term stays
    // store(store(a, j, 20), i, 10) in its original nesting order.
    // Commuting requires proven distinctness — if i=j at runtime, the
    // outer store wins and swapping would change which value is live.
    let expected = ts.intern(
        TermData::App(Symbol::named("store"), vec![inner, i, v]),
        Sort::array(Sort::Int, Sort::Int),
    );

    assert_eq!(
        outer, expected,
        "symbolic store indices should NOT be commuted at the term level"
    );
}

/// Symbolic store squash does NOT walk through non-distinct indices (#6367).
///
/// `store(store(store(a, i, 10), j, 30), i, 20)` with symbolic i, j:
/// the squash_store walk encounters j (not provably distinct from i) and
/// aborts. The term stays in its original nesting order. The theory solver
/// handles same-index reasoning at runtime.
#[test]
fn test_squash_store_symbolic_blocked_by_non_distinct_middle() {
    let mut ts = TermStore::new();
    let arr = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = ts.mk_var("i", Sort::Int);
    let j = ts.mk_var("j", Sort::Int);
    let v1 = ts.mk_int(BigInt::from(10));
    let v2 = ts.mk_int(BigInt::from(20));
    let w = ts.mk_int(BigInt::from(30));

    // store(store(store(a, i, 10), j, 30), i, 20)
    let s1 = ts.mk_store(arr, i, v1);
    let s2 = ts.mk_store(s1, j, w);
    let s3 = ts.mk_store(s2, i, v2);

    // No rewriting occurs: symbolic j blocks the squash walk because
    // are_provably_distinct_indices(i, j) is false. The same-index check
    // (inner_index == index) only fires at depth 1 where inner_index is j,
    // not i. So the result is the literal store(store(store(a,i,10),j,30),i,20).
    let expected = ts.intern(
        TermData::App(Symbol::named("store"), vec![s2, i, v2]),
        Sort::array(Sort::Int, Sort::Int),
    );

    assert_eq!(
        s3, expected,
        "symbolic stores with non-distinct middle index should NOT be squashed"
    );
}

/// Concrete distinct stores normally commute, but when the outer concrete
/// index already appears deeper in the chain we keep the raw topology until
/// squash_store can prove the intermediate path away.
#[test]
fn test_duplicate_concrete_index_guard_blocks_top_level_swap_when_squash_is_blocked() {
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let arr = ts.mk_var("a", array_sort.clone());
    let i = ts.mk_int(BigInt::from(1));
    let k = ts.mk_int(BigInt::from(3));
    let j = ts.mk_var("j", Sort::Int);
    let v1 = ts.mk_int(BigInt::from(10));
    let v2 = ts.mk_int(BigInt::from(20));
    let v3 = ts.mk_int(BigInt::from(30));
    let wj = ts.mk_int(BigInt::from(40));

    let s1 = ts.mk_store(arr, i, v1);
    let s2 = ts.mk_store(s1, j, wj);
    let s3 = ts.mk_store(s2, k, v3);
    let guarded = ts.mk_store(s3, i, v2);

    let expected = ts.intern(
        TermData::App(Symbol::named("store"), vec![s3, i, v2]),
        array_sort.clone(),
    );
    let swapped_inner = ts.intern(
        TermData::App(Symbol::named("store"), vec![s2, i, v2]),
        array_sort.clone(),
    );
    let swapped = ts.intern(
        TermData::App(Symbol::named("store"), vec![swapped_inner, k, v3]),
        array_sort,
    );

    assert_eq!(
        guarded, expected,
        "duplicate-index guard should keep the outer concrete store in place when a symbolic middle blocks squash_store"
    );
    assert_ne!(
        guarded, swapped,
        "the guarded rewrite must not perform the top-level concrete swap across a deeper duplicate index"
    );
}

#[test]
fn test_duplicate_free_concrete_store_chain_still_sorts() {
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let arr = ts.mk_var("a", array_sort.clone());
    let i1 = ts.mk_int(BigInt::from(1));
    let i2 = ts.mk_int(BigInt::from(2));
    let i3 = ts.mk_int(BigInt::from(3));
    let v1 = ts.mk_int(BigInt::from(10));
    let v2 = ts.mk_int(BigInt::from(20));
    let v3 = ts.mk_int(BigInt::from(30));

    let s1 = ts.mk_store(arr, i2, v2);
    let s2 = ts.mk_store(s1, i3, v3);
    let sorted = ts.mk_store(s2, i1, v1);

    let raw_i1 = ts.intern(
        TermData::App(Symbol::named("store"), vec![arr, i1, v1]),
        array_sort.clone(),
    );
    let raw_i2 = ts.intern(
        TermData::App(Symbol::named("store"), vec![raw_i1, i2, v2]),
        array_sort.clone(),
    );
    let expected = ts.intern(
        TermData::App(Symbol::named("store"), vec![raw_i2, i3, v3]),
        array_sort.clone(),
    );
    let unsorted = ts.intern(
        TermData::App(Symbol::named("store"), vec![s2, i1, v1]),
        array_sort,
    );

    assert_eq!(
        sorted, expected,
        "duplicate-free concrete stores should still normalize into sorted order"
    );
    assert_ne!(
        sorted, unsorted,
        "the duplicate-index guard must not disable ordinary concrete store sorting"
    );
}

#[test]
fn test_expand_select_store_symbolic_index_creates_ite() {
    let mut ts = TermStore::new();
    let arr = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let store_idx = ts.mk_var("i", Sort::Int);
    let select_idx = ts.mk_var("j", Sort::Int);
    let value = ts.mk_var("v", Sort::Int);

    let stored = ts.mk_store(arr, store_idx, value);
    let select = ts.mk_select(stored, select_idx);
    let expanded = ts.expand_select_store(select);

    let eq = ts.mk_eq(store_idx, select_idx);
    let base_select = ts.mk_select(arr, select_idx);
    let expected = ts.mk_ite(eq, value, base_select);
    assert_eq!(
        expanded, expected,
        "expand_select_store should rewrite symbolic select(store(a,i,v), j) to ite(i=j, v, select(a,j))"
    );
}

#[test]
fn test_expand_select_store_nested_stores_creates_nested_ite_chain() {
    let mut ts = TermStore::new();
    let arr = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i1 = ts.mk_var("i1", Sort::Int);
    let i2 = ts.mk_var("i2", Sort::Int);
    let j = ts.mk_var("j", Sort::Int);
    let v1 = ts.mk_var("v1", Sort::Int);
    let v2 = ts.mk_var("v2", Sort::Int);

    let inner_store = ts.mk_store(arr, i1, v1);
    let stored = ts.mk_store(inner_store, i2, v2);
    let select = ts.mk_select(stored, j);
    let expanded = ts.expand_select_store(select);

    let outer_eq = ts.mk_eq(i2, j);
    let inner_eq = ts.mk_eq(i1, j);
    let base_select = ts.mk_select(arr, j);
    let inner_ite = ts.mk_ite(inner_eq, v1, base_select);
    let expected = ts.mk_ite(outer_eq, v2, inner_ite);
    assert_eq!(
        expanded, expected,
        "expand_select_store should recurse through nested stores in last-write-wins order"
    );
}

#[test]
fn test_expand_select_store_all_only_rewrites_select_terms() {
    let mut ts = TermStore::new();
    let arr = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = ts.mk_var("i", Sort::Int);
    let j = ts.mk_var("j", Sort::Int);
    let v = ts.mk_var("v", Sort::Int);

    let store = ts.mk_store(arr, i, v);
    let select = ts.mk_select(store, j);
    let unchanged = ts.mk_eq(arr, arr);
    let expanded = ts.expand_select_store_all(&[select, unchanged]);

    let eq = ts.mk_eq(i, j);
    let base_select = ts.mk_select(arr, j);
    let expected_select = ts.mk_ite(eq, v, base_select);
    assert_eq!(expanded, vec![expected_select, unchanged]);
}

#[test]
fn test_expand_select_store_symbolic_budget_stops_deep_chains() {
    // Verify that the symbolic ITE budget (SYMBOLIC_ITE_BUDGET=4) stops
    // expansion on deep symbolic store chains (#6367).
    let mut ts = TermStore::new();
    let arr = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let j = ts.mk_var("j", Sort::Int);

    // Build a chain of 6 symbolic stores: store(store(...store(a, i1, v1)..., i6, v6))
    let mut current = arr;
    for k in 1..=6 {
        let idx = ts.mk_var(format!("i{k}"), Sort::Int);
        let val = ts.mk_var(format!("v{k}"), Sort::Int);
        current = ts.mk_store(current, idx, val);
    }

    let select = ts.mk_select(current, j);
    let expanded = ts.expand_select_store(select);

    // The outermost 4 store levels should become ITEs (budget=4).
    // Levels 5-6 (i1, i2) should remain as select(store(store(a, i1, v1), i2, v2), j).
    // Verify: the result is an ITE at the top level (from i6=j)
    assert!(
        matches!(ts.get(expanded), TermData::Ite(_, _, _)),
        "top level should be ITE, got {:?}",
        ts.get(expanded)
    );

    // Walk down the ITE chain to count symbolic ITE levels
    let mut node = expanded;
    let mut ite_count = 0;
    while let TermData::Ite(_, _, else_branch) = ts.get(node) {
        ite_count += 1;
        node = *else_branch;
    }
    assert_eq!(
        ite_count,
        TermStore::SYMBOLIC_ITE_BUDGET,
        "should generate exactly SYMBOLIC_ITE_BUDGET ({}) ITE levels for 6 symbolic stores",
        TermStore::SYMBOLIC_ITE_BUDGET
    );

    // The leaf should be select(store_chain, j) — not further expanded
    assert!(
        matches!(ts.get(node), TermData::App(Symbol::Named(n), _) if n == "select"),
        "leaf of ITE chain should be select(...), got {:?}",
        ts.get(node)
    );
}

// ==================== Array Map Tests (#8533) ====================

/// map[f](a) creates an array term with the correct sort.
#[test]
fn test_array_map_basic_sort() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    // map[f](a) where f : Int -> Bool should produce (Array Int Bool)
    let result = ts.mk_array_map("f", vec![a], Sort::array(Sort::Int, Sort::Bool));
    assert_eq!(ts.sort(result), &Sort::array(Sort::Int, Sort::Bool));
}

/// map[f] is detectable via get_array_map.
#[test]
fn test_array_map_get_array_map() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let b = ts.mk_var("b", Sort::array(Sort::Int, Sort::Int));
    let map_term = ts.mk_array_map("add", vec![a, b], Sort::array(Sort::Int, Sort::Int));

    let (func_name, args) = ts.get_array_map(map_term).expect("should be a map term");
    assert_eq!(func_name, "add");
    assert_eq!(args.len(), 2);
    assert_eq!(args[0], a);
    assert_eq!(args[1], b);
}

/// select(map[f](a1,...,an), i) rewrites to f(select(a1,i),...,select(an,i)).
#[test]
fn test_array_map_select_over_map_rewrite() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let b = ts.mk_var("b", Sort::array(Sort::Int, Sort::Int));
    let i = ts.mk_var("i", Sort::Int);

    // map[add](a, b) : (Array Int Int)
    let map_term = ts.mk_array_map("add", vec![a, b], Sort::array(Sort::Int, Sort::Int));

    // select(map[add](a, b), i) should rewrite to add(select(a, i), select(b, i))
    let result = ts.mk_select(map_term, i);

    // The result should be add(select(a, i), select(b, i))
    match ts.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "add");
            assert_eq!(args.len(), 2);
            // First arg: select(a, i)
            match ts.get(args[0]) {
                TermData::App(Symbol::Named(n), a) => {
                    assert_eq!(n, "select");
                    assert_eq!(a.len(), 2);
                }
                other => panic!("Expected select term, got {other:?}"),
            }
            // Second arg: select(b, i)
            match ts.get(args[1]) {
                TermData::App(Symbol::Named(n), a) => {
                    assert_eq!(n, "select");
                    assert_eq!(a.len(), 2);
                }
                other => panic!("Expected select term, got {other:?}"),
            }
        }
        other => panic!("Expected add(...) term, got {other:?}"),
    }
}

/// select(map[f](a), i) with unary f rewrites to f(select(a, i)).
#[test]
fn test_array_map_select_over_map_unary() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = ts.mk_int(BigInt::from(5));

    let map_term = ts.mk_array_map("inc", vec![a], Sort::array(Sort::Int, Sort::Int));
    let result = ts.mk_select(map_term, i);

    // Pre-compute the expected select term before pattern matching
    let expected_select = ts.mk_select(a, i);

    match ts.get(result) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "inc");
            assert_eq!(args.len(), 1);
            // Arg should be select(a, 5)
            assert_eq!(args[0], expected_select);
        }
        other => panic!("Expected inc(...) term, got {other:?}"),
    }
}

/// Non-map terms are not detected by get_array_map.
#[test]
fn test_array_map_get_array_map_non_map() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    assert!(ts.get_array_map(a).is_none());

    let v = ts.mk_int(BigInt::from(42));
    let const_arr = ts.mk_const_array(Sort::Int, v);
    assert!(ts.get_array_map(const_arr).is_none());
}

#[test]
fn test_const_array_bitvec_index() {
    let mut store = TermStore::new();

    // Create constant array: (Array (_ BitVec 32) Int) with default 0
    let default_val = store.mk_int(BigInt::from(0));
    let const_arr = store.mk_const_array(Sort::bitvec(32), default_val);

    // Check sort
    assert_eq!(
        store.sort(const_arr),
        &Sort::array(Sort::bitvec(32), Sort::Int)
    );

    // Read should simplify
    let idx = store.mk_bitvec(BigInt::from(0xDEADBEEFu32), 32);
    let selected = store.mk_select(const_arr, idx);
    assert_eq!(selected, default_val);
}
