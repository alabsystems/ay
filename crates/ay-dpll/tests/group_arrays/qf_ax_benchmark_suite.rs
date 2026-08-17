// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AX benchmark suite — comprehensive array theory soundness tests (#4304).
//!
//! Each test corresponds to a benchmark in benchmarks/smt/QF_AX/.
//! Patterns tested:
//! - ROW1 (read-over-write same index)
//! - ROW2 (read-over-write different index)
//! - Extensionality (pointwise equal arrays must be equal)
//! - Store chain resolution (nested stores + equality chains)
//! - Conflicting stores (same base+index, different values)
//! - Store-select inverse (write-back identity)
//! - Diamond patterns (two stores from same base, then equated)
//! - Store equality implications (value and base congruence)

use ntest::timeout;

include!("qf_ax_benchmark_suite/core_axioms.rs");

// === Diamond patterns ===

#[test]
#[timeout(10_000)]
fn qf_ax_diamond_equality_sat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (declare-fun w () Element)
        (assert (= b (store a i v)))
        (assert (= c (store a j w)))
        (assert (not (= i j)))
        (assert (= b c))
        (assert (= v (select a i)))
        (assert (= w (select a j)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "sat", "diamond equality with consistent values");
}

#[test]
#[timeout(10_000)]
fn qf_ax_diamond_conflict() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (declare-fun w () Element)
        (assert (= b (store a i v)))
        (assert (= c (store a j w)))
        (assert (not (= i j)))
        (assert (= b c))
        (assert (not (= v (select a i))))
        (check-sat)
    "#,
    );
    assert_ne!(
        result[0], "sat",
        "diamond conflict: b=c but v != a[i] contradicts b = store(a,i,v) = c"
    );
}

// === SAT correctness (no false negatives) ===

#[test]
#[timeout(10_000)]
fn qf_ax_multiple_arrays_sat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (declare-fun w () Element)
        (assert (= a (store b i v)))
        (assert (= c (store b j w)))
        (assert (not (= i j)))
        (assert (= (select a j) w))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "sat", "multiple arrays with consistent stores");
}

#[test]
#[timeout(10_000)]
fn qf_ax_two_stores_same_base_sat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v1 () Element)
        (declare-fun v2 () Element)
        (assert (= b (store a i v1)))
        (assert (= c (store a j v2)))
        (assert (not (= i j)))
        (assert (= (select b j) (select a j)))
        (assert (= (select c i) (select a i)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "two stores to same base at different indices"
    );
}

// === Store idempotent ===

#[test]
#[timeout(10_000)]
fn qf_ax_store_idempotent() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (assert (not (= (select (store (store a i v) i v) j) (select (store a i v) j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "store idempotent: store(store(a,i,v),i,v) = store(a,i,v)"
    );
}

// === Write-write overwrite ===

#[test]
#[timeout(10_000)]
fn qf_ax_write_write_overwrite() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v1 () Element)
        (declare-fun v2 () Element)
        (assert (not (= i j)))
        (assert (not (= (select (store (store a i v1) i v2) j) (select (store a i v2) j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "write-write overwrite: store(store(a,i,v1),i,v2) at j = store(a,i,v2) at j"
    );
}

// === Nested store chain ===

#[test]
#[timeout(10_000)]
fn qf_ax_nested_store_chain() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun i3 () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (declare-fun e3 () Element)
        (assert (not (= i1 i2)))
        (assert (not (= i1 i3)))
        (assert (not (= i2 i3)))
        (assert (not (= (select (store (store (store a i1 e1) i2 e2) i3 e3) i1) e1)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "nested store chain: ROW2 skip + ROW1 match"
    );
}

// === Swap pattern ===

#[test]
#[timeout(10_000)]
fn qf_ax_swap_pattern() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (assert (not (= i j)))
        (assert (not (= (select (store (store a i (select a j)) j (select a i)) i) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "swap pattern");
}

// === Push/Pop incremental regression (#6726) ===

/// Regression test for phantom array axioms from popped scopes (#6726).
/// After push/pop, dead terms in the append-only TermStore caused the
/// array axiom fixpoint to generate phantom axioms, returning Unknown
/// instead of Sat.
#[test]
#[timeout(10_000)]
fn qf_ax_push_pop_phantom_axiom_regression_6726() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (check-sat)
        (push 1)
        (assert (= (select (store a 0 42) 0) 7))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "sat", "base scope before push");
    assert_eq!(result[1], "unsat", "inner scope: 42 != 7");
    assert_eq!(
        result[2], "sat",
        "after pop: must be sat, not unknown from phantom axioms"
    );
}

/// Nested push/pop with array terms: ensures axiom scoping works at
/// multiple depth levels.
#[test]
#[timeout(10_000)]
fn qf_ax_nested_push_pop_6726() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= (select a 0) 5))
        (check-sat)
        (push 1)
        (assert (= b (store a 1 42)))
        (assert (not (= (select b 1) 42)))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (= (select a 0) 5))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "sat", "scope 0 with one select assertion");
    assert_eq!(result[1], "unsat", "scope 1: store/select contradiction");
    assert_eq!(result[2], "sat", "back to scope 0 after first pop");
    assert_eq!(result[3], "sat", "scope 1 again with consistent assertion");
    assert_eq!(result[4], "sat", "back to scope 0 after second pop");
}
