// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `qf_ax_benchmark_suite` to preserve test FQNs.

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
