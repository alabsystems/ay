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

// === ROW1 (read-over-write same index) ===

#[test]
#[timeout(10_000)]
fn qf_ax_row1_basic() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v () Element)
        (assert (not (= (select (store a i v) i) v)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "ROW1 basic");
}

#[test]
#[timeout(10_000)]
fn qf_ax_store_overwrite() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v1 () Element)
        (declare-fun v2 () Element)
        (assert (not (= (select (store (store a i v1) i v2) i) v2)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "store overwrite: last write wins");
}

// === ROW2 (read-over-write different index) ===

#[test]
#[timeout(10_000)]
fn qf_ax_row2_basic() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (assert (not (= i j)))
        (assert (not (= (select (store a i v) j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "ROW2 basic");
}

#[test]
#[timeout(10_000)]
fn qf_ax_double_store_row2() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun k () Index)
        (declare-fun v1 () Element)
        (declare-fun v2 () Element)
        (assert (not (= i j)))
        (assert (not (= i k)))
        (assert (not (= j k)))
        (assert (not (= (select (store (store a i v1) j v2) k) (select a k))))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "double store ROW2 skip");
}

#[test]
#[timeout(10_000)]
fn qf_ax_store_store_diff_idx() {
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
        (assert (not (= (select (store (store a i v1) j v2) i) v1)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "store at j preserves store at i");
}

// === Extensionality ===

#[test]
#[timeout(10_000)]
fn qf_ax_ext_basic_sat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (assert (not (= a b)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "sat", "extensionality: arrays can differ");
}

#[test]
#[timeout(10_000)]
fn qf_ax_ext_witness_sat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun k () Index)
        (assert (not (= a b)))
        (assert (= (select a k) (select b k)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "extensionality: can differ at other index"
    );
}

#[test]
#[timeout(10_000)]
fn qf_ax_ext_two_indices_sat() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (assert (not (= a b)))
        (assert (= (select a i) (select b i)))
        (assert (= (select a j) (select b j)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "extensionality: agree at two indices, differ at others"
    );
}

#[test]
#[timeout(10_000)]
fn qf_ax_write_back_identity() {
    // store(a, i, select(a, i)) = a  (extensionality + ROW1/ROW2)
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun i () Index)
        (assert (not (= (store a i (select a i)) a)))
        (check-sat)
    "#,
    );
    assert!(
        result[0] == "unknown" || result[0] == "unsat",
        "write-back identity: store(a,i,a[i]) = a must not return false SAT — got: {}",
        result[0]
    );
}

// === Store equality chain ===

#[test]
#[timeout(10_000)]
fn qf_ax_store_eq_transitivity() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e () Element)
        (assert (= b (store a i e)))
        (assert (not (= (select b i) e)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "store equality: b = store(a,i,e) => b[i] = e"
    );
}

#[test]
#[timeout(10_000)]
fn qf_ax_three_store_chain() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun d () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v () Element)
        (assert (= b (store a i v)))
        (assert (= c b))
        (assert (= d c))
        (assert (not (= (select d i) v)))
        (check-sat)
    "#,
    );
    assert_ne!(
        result[0], "sat",
        "three-hop equality chain: d = c = b = store(a,i,v)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_ax_eq_chain_four_arrays() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun c () (Array Index Element))
        (declare-fun d () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v () Element)
        (assert (= a b))
        (assert (= b (store c i v)))
        (assert (= c d))
        (assert (not (= (select a i) v)))
        (check-sat)
    "#,
    );
    assert_ne!(
        result[0], "sat",
        "four-array equality chain: a = b = store(c,i,v), c = d"
    );
}

// === Indirect store references ===

#[test]
#[timeout(10_000)]
fn qf_ax_indirect_store_row2() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (assert (= b (store a i v)))
        (assert (not (= i j)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
    "#,
    );
    assert_ne!(
        result[0], "sat",
        "indirect store ROW2: b = store(a,i,v), b[j] = a[j] when i != j"
    );
}

#[test]
#[timeout(10_000)]
fn qf_ax_store_eq_read_different() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (assert (= b (store a i v)))
        (assert (not (= i j)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
    "#,
    );
    assert_ne!(
        result[0], "sat",
        "store eq read different: same as indirect_store_row2"
    );
}

// === Conflicting stores ===

#[test]
#[timeout(10_000)]
fn qf_ax_conflicting_stores() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (not (= e1 e2)))
        (assert (= a (store b i e1)))
        (assert (= a (store b i e2)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "conflicting stores: same base+idx, different values"
    );
}

// === Congruence ===

#[test]
#[timeout(10_000)]
fn qf_ax_ext_congruence() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v () Element)
        (assert (= a b))
        (assert (not (= (store a i v) (store b i v))))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "EUF congruence on store");
}

#[test]
#[timeout(10_000)]
fn qf_ax_array_eq_select() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (assert (= a b))
        (assert (not (= (select a i) (select b i))))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "array equality implies select equality");
}

// === Store equality implications ===

#[test]
#[timeout(10_000)]
fn qf_ax_store_eq_implies_select_eq() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v () Element)
        (declare-fun w () Element)
        (assert (= (store a i v) (store b i w)))
        (assert (not (= v w)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "store(a,i,v) = store(b,i,w) implies v = w"
    );
}

#[test]
#[timeout(10_000)]
fn qf_ax_store_eq_implies_base_eq_at_other() {
    let result = crate::common::solve_vec(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a () (Array Index Element))
        (declare-fun b () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun j () Index)
        (declare-fun v () Element)
        (declare-fun w () Element)
        (assert (= (store a i v) (store b i w)))
        (assert (not (= i j)))
        (assert (not (= (select a j) (select b j))))
        (check-sat)
    "#,
    );
    assert_ne!(
        result[0], "sat",
        "store(a,i,v) = store(b,i,w), j != i => a[j] = b[j]"
    );
}

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
