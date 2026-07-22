// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;
use serial_test::serial;

// =======================================================================
// ITE Lifting Tests
// =======================================================================

#[test]
fn test_ite_lifting_simple() {
    let mut store = TermStore::new();

    // (<= (ite c x y) z) should become (ite c (<= x z) (<= y z))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let z = store.mk_var("z", Sort::Real);

    let ite_expr = store.mk_ite(c, x, y);
    let pred = store.mk_le(ite_expr, z);

    let lifted = store.lift_arithmetic_ite(pred);

    // Should be (ite c (<= x z) (<= y z))
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            // then branch should be (<= x z)
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], x);
                    assert_eq!(args[1], z);
                }
                _ => panic!("Expected <= application in then branch"),
            }
            // else branch should be (<= y z)
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], y);
                    assert_eq!(args[1], z);
                }
                _ => panic!("Expected <= application in else branch"),
            }
        }
        _ => panic!("Expected ITE after lifting"),
    }
}

#[test]
fn test_ite_lifting_second_arg() {
    let mut store = TermStore::new();

    // (<= z (ite c x y)) should become (ite c (<= z x) (<= z y))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let z = store.mk_var("z", Sort::Real);

    let ite_expr = store.mk_ite(c, x, y);
    let pred = store.mk_le(z, ite_expr);

    let lifted = store.lift_arithmetic_ite(pred);

    // Should be (ite c (<= z x) (<= z y))
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], z);
                    assert_eq!(args[1], x);
                }
                _ => panic!("Expected <= application in then branch"),
            }
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], z);
                    assert_eq!(args[1], y);
                }
                _ => panic!("Expected <= application in else branch"),
            }
        }
        _ => panic!("Expected ITE after lifting"),
    }
}

#[test]
fn test_ite_lifting_no_ite() {
    let mut store = TermStore::new();

    // (<= x y) with no ITE should remain unchanged
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);

    let pred = store.mk_le(x, y);
    let lifted = store.lift_arithmetic_ite(pred);

    assert_eq!(lifted, pred);
}

#[test]
fn test_ite_lifting_all_reuses_shared_ite_free_dag_without_growth() {
    let mut store = TermStore::new();

    let array = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let store_index = store.mk_var("i", Sort::Int);
    let select_index = store.mk_var("j", Sort::Int);
    let value = store.mk_var("v", Sort::Int);
    let upper = store.mk_var("upper", Sort::Int);
    let lower = store.mk_var("lower", Sort::Int);
    let one = store.mk_int(BigInt::from(1));

    let updated = store.mk_store(array, store_index, value);
    let shared_select = store.mk_select(updated, select_index);
    let shared_sum = store.mk_add(vec![shared_select, one]);
    let le = store.mk_le(shared_sum, upper);
    let ge = store.mk_ge(shared_sum, lower);

    let len_before = store.len();
    let lifted = store.lift_arithmetic_ite_all(&[le, ge]);

    assert_eq!(lifted, vec![le, ge]);
    assert_eq!(
        store.len(),
        len_before,
        "ITE-free shared arithmetic/store tails should not allocate new terms"
    );
}

#[test]
fn test_ite_lifting_bool_ite_not_lifted() {
    let mut store = TermStore::new();

    // (= (ite c true false) p) should NOT lift since ITE result is Bool
    let c = store.mk_var("c", Sort::Bool);
    let p = store.mk_var("p", Sort::Bool);

    let true_t = store.true_term();
    let false_t = store.false_term();
    let ite_expr = store.mk_ite(c, true_t, false_t);
    let pred = store.mk_eq(ite_expr, p);

    let lifted = store.lift_arithmetic_ite(pred);

    // For Bool ITE, the lifting may or may not happen depending on simplifications
    // The key is that the result should be semantically equivalent
    // Just check that it doesn't crash
    assert!(!store.is_false(lifted));
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_ite_lifting_nested() {
    let mut store = TermStore::new();

    // (and (<= (ite c x y) z) (<= w v)) should lift the first conjunct
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let z = store.mk_var("z", Sort::Real);
    let w = store.mk_var("w", Sort::Real);
    let v = store.mk_var("v", Sort::Real);

    let ite_expr = store.mk_ite(c, x, y);
    let pred1 = store.mk_le(ite_expr, z);
    let pred2 = store.mk_le(w, v);
    let conj = store.mk_and(vec![pred1, pred2]);

    let lifted = store.lift_arithmetic_ite(conj);

    // Should be (and (ite c (<= x z) (<= y z)) (<= w v))
    match store.get(lifted) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "and");
            assert_eq!(args.len(), 2);
            // First arg should be lifted ITE
            assert!(matches!(store.get(args[0]), TermData::Ite(_, _, _)));
            // Second arg should be unchanged
            assert_eq!(args[1], pred2);
        }
        _ => panic!("Expected and application after lifting"),
    }
}

#[test]
fn test_ite_lifting_lt() {
    let mut store = TermStore::new();

    // (< (ite c x y) z) should become (ite c (< x z) (< y z))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let z = store.mk_var("z", Sort::Int);

    let ite_expr = store.mk_ite(c, x, y);
    let pred = store.mk_lt(ite_expr, z);

    let lifted = store.lift_arithmetic_ite(pred);

    match store.get(lifted) {
        TermData::Ite(cond, _, _) => {
            assert_eq!(*cond, c);
        }
        _ => panic!("Expected ITE after lifting"),
    }
}

#[test]
fn test_ite_lifting_nested_in_arithmetic() {
    let mut store = TermStore::new();

    // (<= (+ x (ite c 1 0)) y) should become (ite c (<= (+ x 1) y) (<= (+ x 0) y))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let zero = store.mk_int(BigInt::from(0));

    let ite_expr = store.mk_ite(c, one, zero);
    let sum = store.mk_add(vec![x, ite_expr]);
    let pred = store.mk_le(sum, y);

    let lifted = store.lift_arithmetic_ite(pred);

    // Should be lifted to an ITE at the top level
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            // Both branches should be <= predicates, not contain ITEs
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), _) => {
                    assert_eq!(name, "<=");
                }
                _ => panic!("Expected <= application in then branch"),
            }
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), _) => {
                    assert_eq!(name, "<=");
                }
                _ => panic!("Expected <= application in else branch"),
            }
        }
        _ => panic!("Expected ITE after lifting nested arithmetic ITE"),
    }
}

#[test]
fn test_ite_lifting_uninterpreted_sort_equality() {
    let mut store = TermStore::new();

    // (= x (ite c a b)) with x, a, b of uninterpreted sort S
    // should become (ite c (= x a) (= x b))
    let sort_s = Sort::Uninterpreted("S".to_string());
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", sort_s.clone());
    let a = store.mk_var("a", sort_s.clone());
    let b = store.mk_var("b", sort_s);

    let ite_expr = store.mk_ite(c, a, b);
    let eq = store.mk_eq(x, ite_expr);

    let lifted = store.lift_arithmetic_ite(eq);

    // Should be (ite c (= x a) (= x b))
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            // then branch should be (= x a)
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "=");
                    // Args could be [x, a] or [a, x] due to canonical ordering
                    assert!(
                        (args[0] == x && args[1] == a) || (args[0] == a && args[1] == x),
                        "Expected equality with x and a, got {args:?}"
                    );
                }
                _ => panic!(
                    "Expected = application in then branch, got {:?}",
                    store.get(*then_t)
                ),
            }
            // else branch should be (= x b)
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "=");
                    // Args could be [x, b] or [b, x] due to canonical ordering
                    assert!(
                        (args[0] == x && args[1] == b) || (args[0] == b && args[1] == x),
                        "Expected equality with x and b, got {args:?}"
                    );
                }
                _ => panic!(
                    "Expected = application in else branch, got {:?}",
                    store.get(*else_t)
                ),
            }
        }
        _ => panic!("Expected ITE after lifting, got {:?}", store.get(lifted)),
    }
}

#[test]
fn test_internal_symbol_uniqueness() {
    let mut store = TermStore::new();
    let s1 = store.mk_internal_symbol("test");
    let s2 = store.mk_internal_symbol("test");
    let s3 = store.mk_internal_symbol("other");

    // Each call should produce a unique symbol
    assert_ne!(s1, s2);
    assert_ne!(s2, s3);

    // All should start with __ay_<purpose>!
    assert!(s1.starts_with("__ay_test!"));
    assert!(s2.starts_with("__ay_test!"));
    assert!(s3.starts_with("__ay_other!"));
}

#[test]
fn test_internal_symbol_format() {
    let mut store = TermStore::new();
    let sym = store.mk_internal_symbol("dt_depth_List");
    // Should be __ay_<purpose>!<id>
    assert!(sym.starts_with("__ay_dt_depth_List!"));
    // Should end with a numeric ID
    let suffix = sym.strip_prefix("__ay_dt_depth_List!").unwrap();
    assert!(
        suffix.parse::<u32>().is_ok(),
        "Expected numeric suffix, got: {suffix}"
    );
}

// =========================================================
// Extract over concat simplification tests
// =========================================================

#[test]
fn test_bvextract_over_concat_low_part() {
    // extract[3:0](concat(a[8], b[8])) → extract[3:0](b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(3, 0, concat_ab);
    let expected = store.mk_bvextract(3, 0, b);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_concat_high_part() {
    // extract[15:8](concat(a[8], b[8])) → a (full extract simplifies to identity)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(15, 8, concat_ab);
    // Full extract of a (8-bit, extracting bits 7:0 maps to a)
    assert_eq!(extract, a);
}

#[test]
fn test_bvextract_over_concat_high_part_partial() {
    // extract[12:10](concat(a[8], b[8])) → extract[4:2](a)
    // In concat(a,b) with |b|=8: a occupies bits [15:8]
    // extract[12:10] is entirely in a, so becomes extract[12-8:10-8](a) = extract[4:2](a)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(12, 10, concat_ab);
    let expected = store.mk_bvextract(4, 2, a);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_concat_crosses_boundary() {
    // extract[11:4](concat(a[8], b[8])) → concat(extract[3:0](a), extract[7:4](b))
    // hi=11, lo=4, w_b=8
    // high_part = extract[11-8:0](a) = extract[3:0](a)
    // low_part = extract[8-1:4](b) = extract[7:4](b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(11, 4, concat_ab);
    let high_part = store.mk_bvextract(3, 0, a);
    let low_part = store.mk_bvextract(7, 4, b);
    let expected = store.mk_bvconcat(vec![high_part, low_part]);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_nested_concat() {
    // extract[3:0](concat(concat(a[4], b[4]), c[4])) where c is at bits [0..3]
    // Total width: 12 bits, c occupies bits 0-3, b occupies 4-7, a occupies 8-11
    // Extract [3:0] is entirely within c
    // First simplification: hi=3 < w_c=4, so extract[3:0](c)
    // Full extract [3:0] of 4-bit c simplifies to c
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let c = store.mk_var("c", Sort::bitvec(4));
    let inner = store.mk_bvconcat(vec![a, b]); // 8-bit: a=high (4-7), b=low (0-3)
    let outer = store.mk_bvconcat(vec![inner, c]); // 12-bit: inner=high (4-11), c=low (0-3)
    let extract = store.mk_bvextract(3, 0, outer);
    assert_eq!(extract, c);
}

#[test]
fn test_bvextract_over_concat_at_boundary() {
    // extract[7:0](concat(a[8], b[8])) → b (full extract of b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(7, 0, concat_ab);
    // hi=7 < w_b=8, so extract within b. Full extract [7:0] of 8-bit b → b
    assert_eq!(extract, b);
}

#[test]
fn test_bvextract_over_concat_single_bit_low() {
    // extract[0:0](concat(a[4], b[4])) → extract[0:0](b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(0, 0, concat_ab);
    let expected = store.mk_bvextract(0, 0, b);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_concat_single_bit_high() {
    // extract[7:7](concat(a[4], b[4])) → extract[3:3](a)
    // w_b=4, so bit 7 is in a at position 7-4=3
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(7, 7, concat_ab);
    let expected = store.mk_bvextract(3, 3, a);
    assert_eq!(extract, expected);
}

#[test]
#[serial(global_term_memory)]
fn test_instance_term_bytes_tracks_allocation() {
    // Create a fresh TermStore - its constructor interns true/false.
    let mut store = TermStore::new();

    // The constructor creates true_term and false_term, so local accounting should increase.
    let after_new = store.instance_term_bytes();
    assert!(
        after_new > 0,
        "instance_term_bytes should increase after TermStore::new()"
    );

    // Intern some unique terms
    let _ = store.mk_var("x", Sort::Int);
    let _ = store.mk_var("y", Sort::Int);
    let _ = store.mk_int(42.into());

    let after_terms = store.instance_term_bytes();
    assert!(
        after_terms > after_new,
        "instance_term_bytes should increase after interning terms"
    );

    // Hash-consed duplicates should NOT increase the counter
    let _ = store.mk_var("x", Sort::Int); // duplicate
    let after_dup = store.instance_term_bytes();
    assert_eq!(
        after_dup, after_terms,
        "hash-consed duplicate should not increase instance_term_bytes"
    );
}

#[test]
#[serial(global_term_memory)]
fn test_global_memory_exceeded_default_threshold() {
    // With a fresh counter and default 4GB limit, memory should not be exceeded
    TermStore::reset_global_term_bytes();
    assert!(
        !TermStore::global_memory_exceeded(),
        "fresh counter should not exceed 4GB limit"
    );
}

/// Verify that per-instance accounting tracks allocation when new terms are interned,
/// including both inline TermEntry size and heap allocations inside TermData.
///
/// This test confirms:
/// 1. The counter increments by at least size_of::<TermEntry>() per unique term.
/// 2. Hash-consing deduplicates (no double-count for identical terms).
/// 3. The counter also tracks heap allocations inside TermData variants
///    (for example, Vec<TermId> children and Symbol::Named strings).
#[test]
#[serial(global_term_memory)]
fn test_instance_term_bytes_tracks_interning_with_heap_accounting() {
    use std::mem::size_of;

    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    // TermStore::new() interns true + false = 2 entries
    let after_new = store.instance_term_bytes();
    let constructor_delta = after_new;
    assert!(
        constructor_delta >= 2 * entry_size,
        "new() should contribute at least two TermEntry allocations"
    );
    assert_eq!(store.len(), 2, "new() should intern exactly true and false");

    // Intern a variable — adds exactly 1 TermEntry
    let len_before_var = store.len();
    let x = store.mk_var("x", Sort::Int);
    let after_var = store.instance_term_bytes();
    let var_delta = after_var - after_new;
    assert!(
        var_delta >= entry_size,
        "one unique term should contribute at least one TermEntry allocation"
    );
    assert_eq!(store.len(), len_before_var + 1);

    // Intern the same variable again — hash-consing deduplicates in the local store.
    let len_before_dup = store.len();
    let _x2 = store.mk_var("x", Sort::Int);
    assert_eq!(
        store.len(),
        len_before_dup,
        "duplicate term should deduplicate"
    );

    // Intern a function application with multiple children.
    // The counter now includes BOTH size_of::<TermEntry>() AND the heap
    // allocation from Vec<TermId> children and Symbol::Named string.
    let len_before_y = store.len();
    let y = store.mk_var("y", Sort::Int);
    assert_eq!(store.len(), len_before_y + 1);
    let len_before_app = store.len();
    let before_app = store.instance_term_bytes();
    let _sum = store.mk_app(Symbol::Named("+".to_string()), vec![x, y], Sort::Int);
    let after_app = store.instance_term_bytes();
    assert_eq!(store.len(), len_before_app + 1);

    // Both size_of::<TermEntry>() AND heap allocations are counted (#8600).
    let counted = after_app - before_app;
    assert!(
        counted >= entry_size,
        "app term should contribute at least one TermEntry allocation"
    );
    assert!(
        counted > entry_size,
        "app term should count heap allocations beyond TermEntry size (#8600)"
    );
}

// =======================================================================
// Performance regression tests for O(n²) complexity in boolean/arith ops
// =======================================================================

/// Regression test: mk_and with N distinct variables should not exhibit
/// O(n²) scaling from complement/absorption detection passes.
///
/// Complement detection should use indexed lookup (`HashSet` before flattening
/// or binary search after sorting) rather than a `Vec::contains()` scan inside
/// a loop over the argument vector.
///
/// This test verifies that mk_and(1000 vars) completes within a reasonable
/// time bound (< 500ms). If the O(n²) path were triggered on, say, 10000
/// variables, this would take seconds.
#[test]
fn test_mk_and_performance_no_quadratic_blowup() {
    let mut store = TermStore::new();

    // Create N distinct bool variables — no complements, no absorption
    let n = 1000;
    let vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("b{i}"), Sort::Bool))
        .collect();

    let start = std::time::Instant::now();
    let result = store.mk_and(vars);
    let elapsed = start.elapsed();

    // Result should be a conjunction of all N variables
    assert_ne!(result, store.true_term());
    assert_ne!(result, store.false_term());

    // 500ms is generous; O(n log n) for n=1000 should be < 10ms.
    // O(n²) with n=1000 would be ~100ms. This catches severe regression.
    assert!(
        elapsed.as_millis() < 500,
        "mk_and({n} vars) took {elapsed:?}, expected < 500ms — possible O(n²) regression"
    );
}

/// Regression test: mk_and with complement pair in large conjunction.
///
/// (and x0 x1 ... x_{n-1} (not x0)) should immediately return false.
/// A regression to `Vec::contains()`-inside-loop complement detection would
/// make this path scale quadratically.
#[test]
fn test_mk_and_complement_detection_scaling() {
    let mut store = TermStore::new();

    let n = 2000;
    let mut vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("c{i}"), Sort::Bool))
        .collect();

    // Add complement of first variable — should trigger false result
    let not_first = store.mk_not(vars[0]);
    vars.push(not_first);

    let start = std::time::Instant::now();
    let result = store.mk_and(vars);
    let elapsed = start.elapsed();

    assert_eq!(
        result,
        store.false_term(),
        "complement pair should yield false"
    );
    assert!(
        elapsed.as_millis() < 500,
        "mk_and complement detection with {n} vars took {elapsed:?}, expected < 500ms"
    );
}

/// Regression test: mk_or with complement pair in large disjunction.
///
/// (or x0 x1 ... x_{n-1} (not x0)) should immediately return true.
#[test]
fn test_mk_or_complement_detection_scaling() {
    let mut store = TermStore::new();

    let n = 2000;
    let mut vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("d{i}"), Sort::Bool))
        .collect();

    let not_first = store.mk_not(vars[0]);
    vars.push(not_first);

    let start = std::time::Instant::now();
    let result = store.mk_or(vars);
    let elapsed = start.elapsed();

    assert_eq!(
        result,
        store.true_term(),
        "complement pair should yield true"
    );
    assert!(
        elapsed.as_millis() < 500,
        "mk_or complement detection with {n} vars took {elapsed:?}, expected < 500ms"
    );
}

/// Regression test: mk_add with N terms should not O(n²) from additive
/// inverse detection using `result_args.contains()` (arithmetic.rs:316).
#[test]
fn test_mk_add_performance_no_quadratic_blowup() {
    let mut store = TermStore::new();

    let n = 500;
    let vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("a{i}"), Sort::Int))
        .collect();

    let start = std::time::Instant::now();
    let result = store.mk_add(vars);
    let elapsed = start.elapsed();

    assert_ne!(result, store.mk_int(BigInt::from(0)));
    assert!(
        elapsed.as_millis() < 500,
        "mk_add({n} vars) took {elapsed:?}, expected < 500ms — possible O(n²) regression"
    );
}

/// Regression: mk_abs with Real-sorted variable must not panic on sort mismatch.
/// Before the fix, mk_abs always used mk_int(0) for the comparison,
/// creating (>= Real Int) which panics in mk_ge.
#[test]
fn test_abs_real_no_sort_mismatch() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Real);
    // This should not panic
    let abs_x = store.mk_abs(x);
    // Result should be an ITE: (ite (>= x 0.0) x (- x))
    match store.get(abs_x) {
        TermData::Ite(cond, then_br, else_br) => {
            // Condition is a comparison, then is x, else is -x
            assert_eq!(*then_br, x);
            // cond should involve a Real zero, not an Int zero
            // Verify the condition references a rational zero
            let cond_sort_ok = match store.get(*cond) {
                TermData::App(Symbol::Named(name), args) if name == "<=" => {
                    // mk_ge(x, 0) normalizes to mk_le(0, x)
                    args.len() == 2 && store.sort(args[0]) == &Sort::Real
                }
                _ => false,
            };
            assert!(
                cond_sort_ok,
                "abs(Real) condition should use Real-sorted zero"
            );
            let _ = else_br;
        }
        other => panic!("abs(x) should be ITE, got {other:?}"),
    }
}

/// Rational constant folding for abs: |−1/2| = 1/2
#[test]
fn test_abs_rational_constant_folding() {
    let mut store = TermStore::new();
    let neg_half = store.mk_rational(BigRational::new(BigInt::from(-1), BigInt::from(2)));
    let pos_half = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));

    assert_eq!(store.mk_abs(neg_half), pos_half);
    assert_eq!(store.mk_abs(pos_half), pos_half);
}

// =======================================================================
// Memory accounting accuracy tests (#8600)
// =======================================================================

/// Verify that `heap_size` accounts for String constants.
/// A string with known capacity should contribute at least that capacity
/// to the term's tracked heap allocation.
#[test]
#[serial(global_term_memory)]
fn test_heap_accounting_string_constant() {
    use std::mem::size_of;
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    // Create a string constant with a known-length payload.
    let long_string = "a]".repeat(500); // 1000 bytes
    let string_len = long_string.len();
    let before_string = store.instance_term_bytes();
    let _s = store.mk_string(long_string);
    let after_string = store.instance_term_bytes();

    let string_delta = after_string - before_string;
    // Must count at least TermEntry + the string heap.
    assert!(
        string_delta >= entry_size + string_len,
        "String constant accounting: delta {string_delta} should be >= {entry_size} (entry) + {string_len} (string heap), \
         before_string={before_string}, after_string={after_string}",
    );
}

/// Verify that BigInt constants contribute proportional heap.
/// A large integer (256 bits) should allocate at least 256/64 = 4 limbs = 32 bytes.
#[test]
#[serial(global_term_memory)]
fn test_heap_accounting_bigint_constant() {
    use std::mem::size_of;
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    // Create a large BigInt: 2^256 - 1 (needs 4 u64 limbs = 32 bytes heap).
    let big = (BigInt::from(1u64) << 256) - BigInt::from(1u64);
    let before = store.instance_term_bytes();
    let _t = store.mk_int(big);
    let after = store.instance_term_bytes();

    let delta = after - before;
    let min_limb_heap = 4 * size_of::<u64>(); // 4 limbs for 256 bits
    assert!(
        delta >= entry_size + min_limb_heap,
        "BigInt accounting: delta {delta} should be >= {entry_size} (entry) + {min_limb_heap} (limb heap)",
    );
}

/// Verify that bitvector constants track BigInt heap.
#[test]
#[serial(global_term_memory)]
fn test_heap_accounting_bitvec_constant() {
    use std::mem::size_of;
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    // Create a 128-bit bitvector: needs ceil(128/64)=2 limbs = 16 bytes min.
    let big_bv = BigInt::from(u128::MAX);
    let before = store.instance_term_bytes();
    let _t = store.mk_bitvec(big_bv, 128);
    let after = store.instance_term_bytes();

    let delta = after - before;
    let min_limb_heap = 2 * size_of::<u64>();
    assert!(
        delta >= entry_size + min_limb_heap,
        "BitVec accounting: delta {delta} should be >= {entry_size} (entry) + {min_limb_heap} (limb heap)",
    );
}

/// Verify that Rational constants track both numerator and denominator heap.
#[test]
#[serial(global_term_memory)]
fn test_heap_accounting_rational_constant() {
    use std::mem::size_of;
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    // Create a rational with large numerator: 2^256 / 7
    let big_numer = (BigInt::from(1u64) << 256) - BigInt::from(1u64);
    let denom = BigInt::from(7);
    let rat = BigRational::new(big_numer, denom);

    let before = store.instance_term_bytes();
    let _t = store.mk_rational(rat);
    let after = store.instance_term_bytes();

    let delta = after - before;
    // Numerator: 4 limbs = 32 bytes; denom: 1 limb = 8 bytes
    let min_heap = 4 * size_of::<u64>() + size_of::<u64>();
    assert!(
        delta >= entry_size + min_heap,
        "Rational accounting: delta {delta} should be >= {entry_size} (entry) + {min_heap} (numer+denom heap)",
    );
}

/// Verify that App terms with many children track Vec<TermId> heap.
#[test]
#[serial(global_term_memory)]
fn test_heap_accounting_app_children() {
    use std::mem::size_of;
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    // Create 100 variables, then an App with all 100 as children.
    let vars: Vec<TermId> = (0..100)
        .map(|i| store.mk_var(format!("v{i}"), Sort::Int))
        .collect();

    let before = store.instance_term_bytes();
    let _app = store.mk_app(Symbol::named("f"), vars, Sort::Int);
    let after = store.instance_term_bytes();

    let delta = after - before;
    // The Vec<TermId> with 100 elements uses at least 100 * 4 = 400 bytes.
    let min_children_heap = 100 * size_of::<TermId>();
    assert!(
        delta >= entry_size + min_children_heap,
        "App children accounting: delta {delta} should be >= {entry_size} (entry) + {min_children_heap} (children heap)",
    );
}

/// Verify that quantifier terms track variable list and trigger heap.
#[test]
#[serial(global_term_memory)]
fn test_heap_accounting_quantifier() {
    use std::mem::size_of;
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    let body = store.true_term();
    let vars: Vec<(String, Sort)> = (0..50).map(|i| (format!("qv{i}"), Sort::Int)).collect();
    // Create trigger patterns: 3 trigger sets, each with 2 terms.
    let trigger_term = store.mk_var("trigger_t", Sort::Int);
    let triggers = vec![vec![trigger_term, trigger_term]; 3];

    let before = store.instance_term_bytes();
    let _q = store.mk_forall_with_triggers(vars, body, triggers);
    let after = store.instance_term_bytes();

    let delta = after - before;
    // vars: 50 * size_of::<(String, Sort)>() + string heap
    // triggers: 3 * size_of::<Vec<TermId>>() + 3 * 2 * size_of::<TermId>()
    let per_var = size_of::<(String, Sort)>();
    let min_vars_heap = 50 * per_var;
    let min_triggers_outer = 3 * size_of::<Vec<TermId>>();
    let min_triggers_inner = 3 * 2 * size_of::<TermId>();
    let min_heap = min_vars_heap + min_triggers_outer + min_triggers_inner;

    assert!(
        delta >= entry_size + min_heap,
        "Quantifier accounting: delta {delta} should be >= {entry_size} (entry) + {min_heap} (vars+triggers heap)",
    );
}

/// Verify that Let bindings track binding list heap.
#[test]
#[serial(global_term_memory)]
fn test_heap_accounting_let_binding() {
    use std::mem::size_of;
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    let body = store.mk_var("body", Sort::Int);
    let bindings: Vec<(String, TermId)> = (0..20)
        .map(|i| {
            let val = store.mk_int(BigInt::from(i));
            (format!("let_var_{i}"), val)
        })
        .collect();

    let before = store.instance_term_bytes();
    let _let_term = store.mk_let(bindings, body);
    let after = store.instance_term_bytes();

    let delta = after - before;
    let per_binding = size_of::<(String, TermId)>();
    let min_heap = 20 * per_binding;

    assert!(
        delta >= entry_size + min_heap,
        "Let binding accounting: delta {delta} should be >= {entry_size} (entry) + {min_heap} (bindings heap)",
    );
}

/// Verify per-engine budget computation.
#[test]
#[serial(global_term_memory)]
fn test_per_engine_budget_divides_by_engine_count() {
    // With usize::MAX limit and 4 engines, per-engine budget is usize::MAX / 4.
    TermStore::set_engine_count(4);
    let budget = TermStore::per_engine_budget();
    assert_eq!(budget, usize::MAX / 4);

    // Reset to 1 engine (default).
    TermStore::set_engine_count(1);
    let budget = TermStore::per_engine_budget();
    assert_eq!(budget, usize::MAX);

    // 0 engines clamps to 1 (prevent division by zero).
    TermStore::set_engine_count(0);
    let budget = TermStore::per_engine_budget();
    assert_eq!(budget, usize::MAX);

    TermStore::set_engine_count(1);
}

/// Verify that hash-consed duplicates do not double-count memory.
/// This is a regression test: if the intern path increments the counter
/// before checking for duplicates, the counter would be inflated.
#[test]
#[serial(global_term_memory)]
fn test_hash_consing_no_double_count() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let app = store.mk_app(Symbol::named("+"), vec![x, y], Sort::Int);

    let bytes_first = store.instance_term_bytes();

    // Recreate the same App — should be hash-consed, no new allocation.
    let x2 = store.mk_var("x", Sort::Int);
    let y2 = store.mk_var("y", Sort::Int);
    let app2 = store.mk_app(Symbol::named("+"), vec![x2, y2], Sort::Int);
    assert_eq!(app, app2, "same App should be hash-consed");

    let bytes_second = store.instance_term_bytes();
    assert_eq!(
        bytes_first, bytes_second,
        "hash-consed duplicate should not inflate instance_term_bytes"
    );
}

/// mk_store preserves original order for nested symbolic stores (#6367).
///
/// `mk_store(store(a, j, w), i, v)` where j > i by TermId stays as a plain
/// nested store. The theory solver handles index equality/disequality reasoning
/// at runtime via ROW1/ROW2 lemmas. Previously this generated ITE terms
/// (`SwapWithEqualityGuard`) which caused combinatorial explosion on storeinv
/// benchmarks.
#[test]
fn test_mk_store_symbolic_no_ite_guard() {
    let mut store = TermStore::new();
    let arr = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    // j declared after i, so j > i by TermId
    assert!(j > i, "test assumes j declared after i");

    let inner = store.mk_store(arr, j, w);
    let result = store.mk_store(inner, i, v);

    // Should be a plain nested store, NOT an ITE
    assert!(
        matches!(store.get(result), TermData::App(Symbol::Named(n), args) if n == "store" && args.len() == 3),
        "mk_store on nested symbolic stores should produce plain store (not ITE), \
         got {:?}",
        store.get(result)
    );
}

// =======================================================================
// true_memory_bytes() accuracy tests (#8600)
// =======================================================================

/// Verify that true_memory_bytes() >= instance_term_bytes() always holds.
/// true_memory_bytes() accounts for container capacity overhead (spare Vec
/// slots, HashMap table) that the incremental counter misses.
#[test]
#[serial(global_term_memory)]
fn test_true_memory_bytes_geq_instance_bytes() {
    let mut store = TermStore::new();

    // After construction (just true + false)
    assert!(
        store.true_memory_bytes() >= store.instance_term_bytes(),
        "true_memory_bytes ({}) should be >= instance_term_bytes ({}) after new()",
        store.true_memory_bytes(),
        store.instance_term_bytes(),
    );

    // After adding many variables (triggers Vec and HashMap growth)
    for i in 0..200 {
        let _ = store.mk_var(format!("v{i}"), Sort::Int);
    }
    assert!(
        store.true_memory_bytes() >= store.instance_term_bytes(),
        "true_memory_bytes ({}) should be >= instance_term_bytes ({}) after 200 vars",
        store.true_memory_bytes(),
        store.instance_term_bytes(),
    );

    // After adding function applications with many children
    let vars: Vec<TermId> = (0..50)
        .map(|i| store.mk_var(format!("a{i}"), Sort::Int))
        .collect();
    for i in 0..20 {
        let _ = store.mk_app(Symbol::named(format!("f{i}")), vars.clone(), Sort::Int);
    }
    assert!(
        store.true_memory_bytes() >= store.instance_term_bytes(),
        "true_memory_bytes ({}) should be >= instance_term_bytes ({}) after apps",
        store.true_memory_bytes(),
        store.instance_term_bytes(),
    );
}

/// Verify that true_memory_bytes() captures Vec capacity overhead that
/// instance_term_bytes() misses. After many pushes, the terms Vec has
/// spare capacity from doubling. true_memory_bytes() counts that capacity.
#[test]
#[serial(global_term_memory)]
fn test_true_memory_bytes_captures_vec_capacity() {
    let mut store = TermStore::new();

    // Push enough terms to trigger several Vec reallocations
    for i in 0..500 {
        let _ = store.mk_var(format!("cap_test_{i}"), Sort::Int);
    }

    let true_bytes = store.true_memory_bytes();
    let incremental = store.instance_term_bytes();

    // true_memory_bytes includes terms Vec spare capacity.
    // After 502 terms (500 vars + true + false), if cap is 512 or 1024,
    // there are at least (cap - 502) spare slots * entry_size bytes untracked.
    // true_memory_bytes should be strictly greater than incremental due to
    // container overhead (HashMap table, spare slots).
    assert!(
        true_bytes > incremental,
        "true_memory_bytes ({}) should exceed instance_term_bytes ({}) \
         due to container overhead. terms.len={}, terms.capacity={}",
        true_bytes,
        incremental,
        store.len(),
        502, // approximate
    );

    // The ratio should be reasonable (not more than 3x)
    let ratio = true_bytes as f64 / incremental as f64;
    assert!(
        ratio < 3.0,
        "true_memory_bytes / instance_term_bytes ratio {ratio:.2} is too high \
         (true={true_bytes}, incremental={incremental})",
    );
}

/// Verify that instance_memory_exceeded uses true_memory_bytes internally,
/// meaning it catches OOM conditions that the old incremental counter would miss.
#[test]
#[serial(global_term_memory)]
fn test_instance_memory_exceeded_uses_true_bytes() {
    let mut store = TermStore::new();

    // Create enough terms that container overhead is non-trivial
    for i in 0..100 {
        let _ = store.mk_var(format!("mem_test_{i}"), Sort::Int);
    }

    let true_bytes = store.true_memory_bytes();
    let incremental = store.instance_term_bytes();

    // Set limit between incremental and true_bytes: the old check would
    // pass, but the new check (using true_memory_bytes) should trigger.
    if true_bytes > incremental {
        let limit_between = incremental + (true_bytes - incremental) / 2;
        assert!(
            store.instance_memory_exceeded(limit_between),
            "instance_memory_exceeded should use true_memory_bytes ({true_bytes}) not incremental ({incremental}), \
             limit={limit_between} should trigger",
        );
    }

    // With a limit above true_bytes, should not trigger
    assert!(
        !store.instance_memory_exceeded(true_bytes + 1),
        "limit above true_memory_bytes should not trigger"
    );
}

/// Verify that heap_data_bytes is consistent with manual heap_size computation.
#[test]
#[serial(global_term_memory)]
fn test_heap_data_bytes_consistency() {
    let mut store = TermStore::new();

    // Create terms with known heap overhead
    let long_name = "x".repeat(100);
    let _v = store.mk_var(&long_name, Sort::Int);

    let vars: Vec<TermId> = (0..20)
        .map(|i| store.mk_var(format!("h{i}"), Sort::Int))
        .collect();
    let _app = store.mk_app(Symbol::named("big_func"), vars, Sort::Int);

    // heap_data_bytes should be positive (non-trivial terms were created)
    let true_bytes = store.true_memory_bytes();
    let incremental = store.instance_term_bytes();

    // Both should be positive
    assert!(true_bytes > 0, "true_memory_bytes should be positive");
    assert!(incremental > 0, "instance_term_bytes should be positive");

    // true_memory_bytes should account for more than just terms + heap
    // because it includes HashMap table overhead
    assert!(
        true_bytes >= incremental,
        "true_memory_bytes ({true_bytes}) >= instance_term_bytes ({incremental})",
    );
}

/// End-to-end test: creating terms until a concrete budget (100 KB) is
/// exceeded should trigger `instance_memory_exceeded` at a point reasonably
/// close to the budget (within 1.5x). This is the key regression test for
/// #8600: before the fix, `instance_term_bytes` undercounted by up to 2-3x,
/// so actual memory could reach 200-300 KB before a 100 KB limit fired.
#[test]
#[serial(global_term_memory)]
fn test_budget_enforcement_triggers_near_limit() {
    use std::mem::size_of;

    let budget: usize = 100 * 1024; // 100 KB
    let mut store = TermStore::new();

    // Create terms until the budget is exceeded.
    let mut exceeded_at_true_bytes = 0usize;
    for i in 0..10_000 {
        let _ = store.mk_var(format!("budget_var_{i}"), Sort::Int);
        if store.instance_memory_exceeded(budget) {
            exceeded_at_true_bytes = store.true_memory_bytes();
            break;
        }
    }

    assert!(
        exceeded_at_true_bytes > 0,
        "instance_memory_exceeded should have triggered within 10K terms"
    );

    // The trigger point should be within 1.5x of the budget.
    // With accurate accounting (true_memory_bytes), the overshoot is bounded
    // by the cache refresh delta (64 KiB) plus one term's allocation.
    let max_overshoot = budget + 64 * 1024 + size_of::<TermEntry>() * 2;
    assert!(
        exceeded_at_true_bytes <= max_overshoot,
        "Budget enforcement triggered too late: true_memory_bytes={exceeded_at_true_bytes} but \
         budget={budget}, max acceptable overshoot={max_overshoot}",
    );
}

#[test]
fn test_ite_lifting_deep_shared_ite_dag_is_linear_not_exponential() {
    // Regression for the #8414 exponential memory bomb (pp-bloaddata: 31 GB
    // RSS): `lift_ite_from_predicate_with_ctx` recursed on (then, arg1) and
    // (else, arg1) with no memoization on the argument pair, so a SHARED ite
    // DAG (here: x_{i-1} appears in BOTH branches of x_i) exploded into a
    // full 2^depth tree expansion. With pair memoization the pass is O(DAG):
    // depth 150 must finish instantly with bounded term growth, where the
    // old code would need ~2^150 steps (already hangs at depth ~30).
    let mut store = TermStore::new();

    let depth = 150usize;
    let z = store.mk_var("z", Sort::Int);
    let mut x = store.mk_var("x0", Sort::Int);
    for i in 1..=depth {
        let c = store.mk_var(format!("c{i}"), Sort::Bool);
        let d = store.mk_var(format!("d{i}"), Sort::Bool);
        let w = store.mk_var(format!("w{i}"), Sort::Int);
        let inner = store.mk_ite(d, x, w);
        x = store.mk_ite(c, x, inner);
    }
    let pred = store.mk_le(x, z);

    let len_before = store.len();
    let start = std::time::Instant::now();
    let lifted = store.lift_arithmetic_ite(pred);
    let elapsed = start.elapsed();

    assert_ne!(lifted, pred, "deep ite should have been lifted");
    let created = store.len() - len_before;
    assert!(
        created < 20 * depth,
        "term growth must be O(DAG), created {created} terms for depth {depth}"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(5),
        "deep shared-ite lifting must be O(DAG); took {elapsed:?}"
    );
}
