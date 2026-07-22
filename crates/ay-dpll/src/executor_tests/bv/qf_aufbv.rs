// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// QF_AUFBV (Quantifier-Free Arrays + UF + Bitvectors) tests
// =========================================================================

#[test]
fn test_executor_qf_aufbv_simple_sat() {
    // Combine arrays and UF with bitvectors
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= (f (select a i)) #x42))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_uf_over_array_index_sat() {
    // Use UF to compute array index
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (assert (= (select a (f x)) #x42))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_array_store_with_uf_sat() {
    // Store value computed by UF
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const i (_ BitVec 8))
        (assert (= b (store a i (f x))))
        (assert (= (select b i) (f x)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_uf_congruence_with_array_unsat() {
    // x = y implies f(x) = f(y) even with array context
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (not (= (f x) (f y))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_array_select_same_index_unsat() {
    // Same as QF_ABV but in QF_AUFBV context
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= (select a i) #x05))
        (assert (= (select a i) #x06))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_combined_constraints_sat() {
    // Complex combination of arrays, UF, and BV
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun g ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const ptr (_ BitVec 8))
        (declare-const val (_ BitVec 8))
        (assert (= ptr #x10))
        (assert (= val (select mem ptr)))
        (assert (= (f val) #x42))
        (assert (bvult (g ptr val) #x80))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_kani_memory_pattern_sat() {
    // Kani-like memory model pattern
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun ptr_to_idx ((_ BitVec 32)) (_ BitVec 32))
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const ptr1 (_ BitVec 32))
        (declare-const ptr2 (_ BitVec 32))
        (declare-const val (_ BitVec 32))
        (assert (= (ptr_to_idx ptr1) #x00000000))
        (assert (= (ptr_to_idx ptr2) #x00000001))
        (assert (= (select (store mem (ptr_to_idx ptr1) #x42424242) (ptr_to_idx ptr2))
                   (select mem (ptr_to_idx ptr2))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_zero_extend_index_alias_unsat() {
    // #4087: zext index aliases must activate ROW2 constraints.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const len (_ BitVec 32))
        (assert (not (= len #x00000000)))
        (assert (not (= (select (store a ((_ zero_extend 32) len) #x2A)
                               #x0000000000000000)
                        (select a ((_ zero_extend 32) #x00000000)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_row2_with_bvadd_zero_index_alias_unsat() {
    // #4087: bvadd j 0 is index-equivalent to j.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= i j)))
        (assert (not (= (select (store a i v) j)
                        (select a (bvadd j #x00)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_row2_with_bvadd_concrete_index_alias_unsat() {
    // #4087: constant-folded bvadd aliases must activate ROW2 constraints.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= i #x02)))
        (assert (not (= (select (store a i v) #x02)
                        (select a (bvadd #x01 #x01)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_row2_with_bvsub_zero_index_alias_unsat() {
    // #4087: bvsub j 0 is index-equivalent to j.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= i j)))
        (assert (not (= (select (store a i v) j)
                        (select a (bvsub j #x00)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_row2_with_bvsub_concrete_index_alias_unsat() {
    // #4087: constant-folded bvsub aliases must activate ROW2 constraints.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= i #x02)))
        (assert (not (= (select (store a i v) #x02)
                        (select a (bvsub #x05 #x03)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_row1_with_uf_sat() {
    // select(store(a, i, v), i) = v with UF context
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= v (f i)))
        (assert (= (select (store a i v) i) v))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_32bit_sat() {
    // 32-bit bitvectors with arrays and UF
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 32)) (_ BitVec 32))
        (declare-const a (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const i (_ BitVec 32))
        (assert (= i #x00000005))
        (assert (bvult (f (select a i)) #x00000100))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_nested_uf_array_sat() {
    // Nested UF and array operations
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (assert (= b (store a x (f (select a x)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// =========================================================================
// Variable substitution + array/UF axiom interaction tests (#8283).
// These exercise the Phase 0 (early) preprocessing path that runs for
// QF_AUFBV before array axiom generation. Both array and UF axioms must
// operate correctly on post-substitution terms.
// =========================================================================

#[test]
fn test_executor_qf_aufbv_var_subst_uf_array_unsat() {
    // After substituting x for y (or vice versa), f(x) and f(y) become
    // the same UF application. Array axioms and UF congruence both see
    // post-substitution terms.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (= (f (select a x)) #xAA))
        (assert (= (f (select a y)) #xBB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_aufbv_value_propagation_array_index_sat() {
    // PropagateValues should replace `idx` with `#x10`. Store and select
    // at the same concrete index must connect via ROW1 axiom.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (assert (= idx #x10))
        (assert (= (select (store a idx #xAB) idx) #xAB))
        (assert (= (f (select a idx)) (f (select a #x10))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_flatten_and_with_array_uf_sat() {
    // FlattenAnd should break up nested and. Array axioms and UF congruence
    // must still work after assertions are flattened.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (and (= i #x05) (= v #x42) (= (select (store a i v) i) v)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_aufbv_var_subst_store_index_unsat() {
    // Variable substitution replaces `i` with `j`. After substitution,
    // store and select at the same index, but conflicting values.
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (assert (= i j))
        (assert (= (select (store a i #xAA) j) #xBB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
