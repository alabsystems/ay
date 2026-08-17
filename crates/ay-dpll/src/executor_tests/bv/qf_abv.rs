// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn optional_qf_abv_benchmark(name: &str) -> Option<String> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smtcomp/QF_ABV")
        .join(name);
    match std::fs::read_to_string(&path) {
        Ok(input) => Some(input),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "skipping optional QF_ABV benchmark fixture {}: {}",
                path.display(),
                error
            );
            None
        }
        Err(error) => panic!(
            "failed to read optional QF_ABV benchmark fixture {}: {}",
            path.display(),
            error
        ),
    }
}

// =========================================================================
// QF_ABV (Quantifier-Free Arrays + Bitvectors) tests
// =========================================================================

#[test]
fn test_executor_qf_abv_simple_sat() {
    // Simple array with bitvector index and value
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= v (select a i)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_store_select_same_index() {
    // select(store(a, i, v), i) = v (ROW1 axiom)
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= (select (store a i v) i) v))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_store_different_value_unsat() {
    // select(store(a, i, v1), i) = v2 where v1 != v2 is unsat
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= (select (store a i #x05) i) #x06))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_bv_constraints_sat() {
    // Array with bitvector operations on indices/values
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= i #x05))
        (assert (= v (select a i)))
        (assert (bvult v #x10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_bvult_array_skips_pre_quantifier_bv_lia_bridge() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 32) (_ BitVec 8)))
        (assert (bvult (concat #x000000 (select a #x00000000)) #x00000100))
        (assert (bvult (concat #x000000 (select a #x00000001)) #x00000100))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.bv_lia_bridge.pre_quantifier_runs")
            .unwrap_or(0),
        0,
        "pure QF_ABV bvult/array formula must not run the pre-quantifier BV-LIA bridge; statistics={:?}",
        exec.statistics()
    );
    assert_eq!(
        exec.statistics().get_string("solver.logic_category"),
        Some("QfAbv")
    );
}

#[test]
fn test_executor_qf_abv_multiple_stores_sat() {
    // Multiple stores to same array
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= b (store (store a #x00 #x01) #x01 #x02)))
        (assert (= (select b #x00) #x01))
        (assert (= (select b #x01) #x02))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_contradictory_values_unsat() {
    // Same index, different values - contradiction
    let input = r#"
        (set-logic QF_ABV)
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
fn test_executor_qf_abv_bv_arithmetic_on_values() {
    // BV arithmetic on array values
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (assert (= (bvadd (select a i) (select a j)) #x0a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_32bit_sat() {
    // 32-bit bitvectors (common for Kani workloads)
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const i (_ BitVec 32))
        (declare-const v (_ BitVec 32))
        (assert (= i #x00000005))
        (assert (= v (select a i)))
        (assert (bvult v #x00000100))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_memory_model_sat() {
    // Memory model pattern: store then select at different index
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const ptr1 (_ BitVec 8))
        (declare-const ptr2 (_ BitVec 8))
        (declare-const val (_ BitVec 8))
        (assert (= ptr1 #x10))
        (assert (= ptr2 #x20))
        (assert (= val #x42))
        (assert (= (select (store mem ptr1 val) ptr2) (select mem ptr2)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_overwrite_sat() {
    // Store overwrites previous value at same index
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= b (store (store a #x05 #x01) #x05 #x02)))
        (assert (= (select b #x05) #x02))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// Tests for variable substitution + array axiom interaction (#8140).
// These exercise the early preprocessing path (Phase 0) that runs
// before array axiom generation, ensuring substitutions don't break
// array ROW/congruence axioms.

#[test]
fn test_executor_qf_abv_var_subst_index_sat() {
    // Variable substitution should replace `i` with `j` or vice versa.
    // Array axiom fixpoint must still generate correct ROW axioms.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (assert (= i j))
        (assert (= (select a i) #x42))
        (assert (= (select a j) #x42))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_index_unsat() {
    // After substituting `i` for `j`, select(a, i) and select(a, j)
    // become the same term. The conflicting values should produce UNSAT.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (assert (= i j))
        (assert (= (select a i) #x42))
        (assert (= (select a j) #x43))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_value_propagation() {
    // PropagateValues should replace `idx` with `#x10`.
    // The store at concrete index and select at the same concrete
    // index must be connected via ROW1 axiom.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (assert (= idx #x10))
        (assert (= (select (store a idx #xAB) idx) #xAB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_store_row2_unsat() {
    // After propagating `i = #x05` and `j = #x06`, the ROW2 axiom
    // should fire: select(store(a, #x05, v), #x06) = select(a, #x06).
    // With select(a, #x06) = #xAA, the result of select(store(a, #x05, v), #x06)
    // must also be #xAA, contradicting the assertion of #xBB.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= i #x05))
        (assert (= j #x06))
        (assert (= (select a j) #xAA))
        (assert (= (select (store a i v) j) #xBB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_ssa_chain_collapse_sat() {
    // SSA-chain collapse pattern (#8140): a sequence of array store operations
    // creates SSA-form definitions like:
    //   mem1 = store(mem0, #x00, #x01)
    //   mem2 = store(mem1, #x01, #x02)
    //   mem3 = store(mem2, #x02, #x03)
    //
    // Variable substitution should replace mem1 with store(mem0, ...), then
    // mem2 with store(store(mem0, ...), ...), etc. This collapses the chain
    // into a single compound term, enabling expand_select_store to resolve
    // selects at compile time rather than generating O(N^2) axiom clauses.
    //
    // This is the pattern where Yices2 excels on bubble_sort-like benchmarks.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem0 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const mem1 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const mem3 (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= mem1 (store mem0 #x00 #x01)))
        (assert (= mem2 (store mem1 #x01 #x02)))
        (assert (= mem3 (store mem2 #x02 #x03)))
        (assert (= (select mem3 #x00) #x01))
        (assert (= (select mem3 #x01) #x02))
        (assert (= (select mem3 #x02) #x03))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_ssa_chain_collapse_unsat() {
    // Same SSA-chain pattern but with a contradictory read.
    // After variable substitution collapses mem3 to store(store(store(mem0, ...
    // select(mem3, #x01) should resolve to #x02 (via ROW2 and ROW1), not #xFF.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem0 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const mem1 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const mem3 (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= mem1 (store mem0 #x00 #x01)))
        (assert (= mem2 (store mem1 #x01 #x02)))
        (assert (= mem3 (store mem2 #x02 #x03)))
        (assert (= (select mem3 #x01) #xFF))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // select(mem3, #x01) = select(store(mem2, #x02, #x03), #x01)
    // Since #x02 != #x01, by ROW2: = select(mem2, #x01)
    // = select(store(mem1, #x01, #x02), #x01)
    // Since #x01 == #x01, by ROW1: = #x02
    // But #x02 != #xFF, so UNSAT.
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_array_sort_substitution_sat() {
    // Test that Array-sort variables are properly substituted (#8140).
    // When (= arr1 arr2) is asserted, variable substitution should
    // unify arr1 and arr2 so that select(arr1, i) and select(arr2, i)
    // become the same term after substitution.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const arr1 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const arr2 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= arr1 arr2))
        (assert (= (select arr1 i) #x42))
        (assert (= (select arr2 i) #x42))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_array_equality_unsat() {
    // Test that after Array-sort substitution, conflicting reads
    // through the unified array produce UNSAT.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const arr1 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const arr2 (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= arr1 arr2))
        (assert (= (select arr1 i) #x42))
        (assert (= (select arr2 i) #x43))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // arr1 = arr2, so select(arr1, i) = select(arr2, i), but #x42 != #x43.
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_var_subst_ite_wrapped_equality_sat() {
    // Test ITE-wrapped equality recovery (#8140).
    // mk_eq expands (= v (ite c a b)) for non-Bool sorts into
    // (ite c (= v a) (= v b)). The variable substitution pass
    // must recognize this and recover v -> ite(c, a, b).
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (declare-const c (_ BitVec 8))
        (assert (= idx #x10))
        (assert (= v (ite (= c #x00) #xAA #xBB)))
        (assert (= (select (store a idx v) idx) (ite (= c #x00) #xAA #xBB)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// =========================================================================
// Delayed BV internalization + array theory interaction tests (#8142)
// =========================================================================

#[test]
fn test_executor_qf_abv_delayed_mul_as_index_sat() {
    // 32-bit variable*variable multiplication used as an array index.
    // The mul should be eagerly internalized because it feeds into
    // a select index, ensuring array functional-consistency axioms
    // get fully constrained bits.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000003))
        (assert (= y #x00000004))
        (assert (= (select mem (bvmul x y)) #x0000002A))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_delayed_two_mul_addresses_sat() {
    // Two bvmul-computed addresses that must be distinct.
    // This is the original regression pattern: array functional
    // consistency requires i!=j -> select(store(a,i,v),j)=select(a,j),
    // which needs fully constrained index bits from mul.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (declare-const c (_ BitVec 32))
        (declare-const d (_ BitVec 32))
        (assert (= a #x00000002))
        (assert (= b #x00000003))
        (assert (= c #x00000005))
        (assert (= d #x00000007))
        (assert (= (select (store mem (bvmul a b) #x000000FF) (bvmul c d)) #x00000000))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // store at 2*3=6, select at 5*7=35 — different indices, so
    // select returns original mem value (unconstrained, can be 0).
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_delayed_mul_store_contradiction_unsat() {
    // Store at a mul-computed index, then read conflicting values.
    // The mul feeds a store/select index and must be eagerly constrained.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000003))
        (assert (= y #x00000004))
        (declare-const mem2 (Array (_ BitVec 32) (_ BitVec 32)))
        (assert (= mem2 (store mem (bvmul x y) #x000000AA)))
        (assert (= (select mem2 (bvmul x y)) #x000000BB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // store at 3*4=12, select at 3*4=12 — ROW1 says value is #xAA,
    // contradicts assertion of #xBB.
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_delayed_data_path_mul_sat() {
    // Data-path mul stored as a VALUE (not index) alongside a constant
    // index.  The mul does NOT feed any array index, so it CAN be
    // delayed.  This tests that we don't over-eagerly force everything.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= x #x00000003))
        (assert (= y #x00000004))
        (assert (= (select (store mem #x00000000 (bvmul x y)) #x00000000) #x0000000C))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // store(mem, 0, 3*4=12) then select at 0 should be 12 = #xC
    assert_eq!(outputs, vec!["sat"]);
}

// =========================================================================
// FC base-grouped optimization tests (#8286)
// =========================================================================

#[test]
fn test_executor_qf_abv_cross_base_fc_unsat_8286() {
    // Two different pointer bases where the pointers happen to be equal.
    // This tests that cross-base FC axioms are still generated (not dropped).
    // If p0 == p1, then select(mem, p0+0) must equal select(mem, p1+0).
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const p0 (_ BitVec 8))
        (declare-const p1 (_ BitVec 8))
        (assert (= p0 p1))
        (assert (not (= (select mem (bvadd p0 #x00)) (select mem (bvadd p1 #x00)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // p0 == p1 implies p0+0 == p1+0, so the selects must be equal.
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_same_base_byte_load_unsat_8286() {
    // Same-base byte-level accesses with contradictory read.
    // Store #x10 at p+0, then assert select at p+0 is #x20.
    // Since p+0 addresses are the same, ROW1 says value is #x10 — contradiction.
    // Tests that same-base FC axioms are correctly generated.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const p (_ BitVec 8))
        (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= mem2 (store mem (bvadd p #x00) #x10)))
        (assert (= (select mem2 (bvadd p #x00)) #x20))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_multi_base_aliasing_unsat_8286() {
    // Three pointer bases where two alias. FC axioms must be generated
    // across bases to detect the contradiction.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const p0 (_ BitVec 8))
        (declare-const p1 (_ BitVec 8))
        (declare-const p2 (_ BitVec 8))
        (assert (= p0 #x10))
        (assert (= p1 #x10))
        (assert (= p2 #x20))
        (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= mem2 (store mem p0 #xAA)))
        (assert (= (select mem2 p1) #xBB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // p0 == p1 == #x10, so store(mem, p0, #xAA) read at p1 must be #xAA,
    // contradicts #xBB assertion.
    assert_eq!(outputs, vec!["unsat"]);
}

// =========================================================================
// CEGAR array FC refinement tests (#8510)
// =========================================================================

#[test]
fn test_executor_qf_abv_cegar_fc_cross_base_budget_overflow_unsat_8510() {
    // Regression test for #8510: when the eager FC cross-base budget
    // (FC_CROSS_BASE_BUDGET_PER_ARRAY = 200) is exhausted before generating
    // the critical FC axiom pair, the CEGAR refinement loop must catch the
    // violation.
    //
    // Strategy: create 23 symbolic-indexed selects on the same array (giving
    // C(23,2) = 253 cross-base pairs, exceeding the budget of 200). Then add
    // two more selects (via p and q where p == q) with contradictory values.
    // The (p, q) FC pair is generated LAST and falls outside the budget.
    // The CEGAR loop must detect the FC violation and add the missing axiom.
    use std::fmt::Write;
    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(smt, "(declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))").unwrap();

    // 23 symbolic variables with distinct base addresses
    for i in 0..23 {
        writeln!(smt, "(declare-const s{i} (_ BitVec 8))").unwrap();
    }

    // Assert all s_i are pairwise distinct (so the solver can't alias them)
    for i in 0..23 {
        for j in (i + 1)..23 {
            writeln!(smt, "(assert (distinct s{i} s{j}))").unwrap();
        }
    }

    // Assert select values for each s_i
    for i in 0..23 {
        writeln!(smt, "(assert (= (select mem s{i}) #x{i:02x}))").unwrap();
    }

    // Two more symbolic selects that must alias (p == q)
    // but have contradictory read values.
    writeln!(smt, "(declare-const p (_ BitVec 8))").unwrap();
    writeln!(smt, "(declare-const q (_ BitVec 8))").unwrap();
    writeln!(smt, "(assert (= p q))").unwrap();
    writeln!(smt, "(assert (= (select mem p) #xAA))").unwrap();
    writeln!(smt, "(assert (= (select mem q) #xBB))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // p == q means select(mem, p) must equal select(mem, q), but
    // #xAA != #xBB. This is UNSAT. If the FC budget was insufficient,
    // the CEGAR loop should catch this.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "expected unsat or unknown, got {outputs:?} — false SAT is a soundness bug"
    );
}

#[test]
fn test_executor_qf_abv_cegar_fc_basic_symbolic_aliasing_unsat_8510() {
    // Basic test: two symbolic selects on the same array that must be equal
    // (due to index equality) but have contradictory values.
    // This should be caught by eager FC axioms (within budget).
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const p (_ BitVec 8))
        (declare-const q (_ BitVec 8))
        (assert (= p q))
        (assert (= (select mem p) #xAA))
        (assert (= (select mem q) #xBB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_small_finite_array_extract_constant_fc_unsat_11936() {
    // ECC-like pattern: a small BV-index array is packed through constant
    // selects, while another read uses an extracted symbolic index. The
    // symbolic/constant FC pair must not be dropped by the cross-base budget.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 4) (_ BitVec 32)))
        (declare-const x (_ BitVec 32))
        (assert (= ((_ extract 3 0) x) #x3))
        (assert (= (select mem ((_ extract 3 0) x)) #x11111111))
        (assert (= (select mem #x3) #x22222222))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_nested_bv1_exact_closure_precedes_generic_extensionality() {
    // The owner route must establish recursively exact finite-domain coverage
    // before generic extensionality examines the outer disequality. Otherwise
    // its fresh outer witness exposes a redundant fourth array equality in
    // addition to the outer equality and its two concrete BV1 cells.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
        (declare-const b (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
        (assert (not (= a b)))
        (assert (= (select (select a #b0) #b0) (select (select b #b0) #b0)))
        (assert (= (select (select a #b0) #b1) (select (select b #b0) #b1)))
        (assert (= (select (select a #b1) #b0) (select (select b #b1) #b0)))
        (assert (= (select (select a #b1) #b1) (select (select b #b1) #b1)))
    "#;

    let commands = parse(input).expect("valid nested finite QF_ABV input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("nested finite QF_ABV input executes");

    assert!(outputs.is_empty(), "setup must not execute a public query");
    exec.begin_external_decision_query(false);
    exec.bind_materialized_public_query();
    let result = exec
        .solve_abv_owner_route_for_test()
        .expect("owned ABV route solves");
    assert!(
        result.is_unsat(),
        "the raw owner route must close the nested contradiction"
    );
    let a = exec.ctx.terms.lookup("a").expect("a declared");
    let b = exec.ctx.terms.lookup("b").expect("b declared");
    assert_eq!(
        exec.array_ext_witness_cache
            .pair_witness(&exec.ctx.terms, a, b),
        None,
        "exact outer coverage must suppress the generic difference Skolem"
    );
    let unique_candidates = exec
        .statistics()
        .get_int("smt.array.finite_ext.candidate_equalities")
        .expect("candidate telemetry published");
    let replayed_candidates = exec
        .statistics()
        .get_int("smt.array.finite_ext.already_covered_equalities")
        .expect("coverage telemetry published");
    assert_eq!(
        unique_candidates, 3,
        "the initial closure must discover exactly three query-unique obligations, not a fourth generic-witness cell"
    );
    assert_eq!(
        replayed_candidates, 3,
        "the final closure must replay all three live exact obligations without re-emission"
    );
    assert_eq!(
        unique_candidates + replayed_candidates,
        6,
        "the initial and final closures must account for six total obligation visits"
    );
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.emitted_equalities"),
        Some(3),
        "recursive closure must emit every nested finite equality"
    );
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(0)
    );
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.candidate_scan_truncated"),
        Some(0)
    );
    assert!(
        exec.finite_array_expansion.is_complete(),
        "the query-cumulative exact-closure ledger must remain complete"
    );
}

#[test]
fn test_executor_qf_abv_packed_lookup_lshr_matches_symbolic_select_11936() {
    // A packed word assembled from all finite constant-index reads must agree
    // with the symbolic read selected by the same shift index.
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-fun i () (_ BitVec 1))
        (define-fun pack () (_ BitVec 2) (concat (select a #b1) (select a #b0)))
        (define-fun got () (_ BitVec 1) ((_ extract 0 0) (bvlshr pack ((_ zero_extend 1) i))))
        (assert (not (= got (select a i))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_lowered_packed_bitmux_matches_symbolic_select_11936() {
    // Constant-shift lowering can turn a packed lookup into an ITE of extracted
    // constant-lane bits. The lowered mux still has to agree with select(a,i).
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 2)))
        (declare-fun i () (_ BitVec 1))

        (define-fun pack () (_ BitVec 4)
          (concat (select a #b1) (select a #b0)))

        (define-fun got () (_ BitVec 1)
          (ite (= i #b1)
               ((_ extract 0 0) (bvlshr pack #b0010))
               ((_ extract 0 0) (bvlshr pack #b0000))))

        (assert (not (= ((_ extract 0 0) (select a i)) got)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_lowered_packed_bv32_mux_output_matches_symbolic_select_11936() {
    // Positive asserted (= out mux) lets the packed-mux bridge connect every
    // output bit to the symbolic select under the decoded mux path.
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 32)))
        (declare-fun i () (_ BitVec 1))
        (declare-fun out () (_ BitVec 32))

        (define-fun pack () (_ BitVec 64)
          (concat (select a #b1) (select a #b0)))

        (define-fun mux () (_ BitVec 32)
          (ite (= i #b1)
               ((_ extract 63 32) pack)
               ((_ extract 31 0) pack)))

        (assert (= out mux))
        (assert (= (select a i) #x12345678))
        (assert (not (= out #x12345678)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_packed_mux_high_half_carry_equivalence_11936() {
    // ECC lowers the same value through a symbolic select on one side and a
    // packed mux on the other, then compares high halves after zero-extension.
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 32)))
        (declare-fun i () (_ BitVec 1))
        (declare-fun base () (_ BitVec 64))
        (declare-fun out () (_ BitVec 32))

        (define-fun pack () (_ BitVec 64)
          (concat (select a #b1) (select a #b0)))

        (define-fun mux () (_ BitVec 32)
          (ite (= i #b1)
               ((_ extract 63 32) pack)
               ((_ extract 31 0) pack)))

        (assert (= out mux))

        (define-fun selected () (_ BitVec 32) (select a i))
        (define-fun lhs_arg () (_ BitVec 64)
          (bvand ((_ sign_extend 32) selected) #x00000000ffffffff))
        (define-fun rhs_arg () (_ BitVec 64)
          (concat #x00000000 out))

        (define-fun lhs () (_ BitVec 64)
          (bvlshr (bvadd base lhs_arg) #x0000000000000020))
        (define-fun rhs () (_ BitVec 64)
          (concat #x00000000 ((_ extract 63 32) (bvadd base rhs_arg))))

        (assert (not (= lhs rhs)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_lowered_packed_bv32_mux_output_rejects_negative_context_11936() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 32)))
        (declare-fun i () (_ BitVec 1))
        (declare-fun out () (_ BitVec 32))

        (define-fun pack () (_ BitVec 64)
          (concat (select a #b1) (select a #b0)))

        (define-fun mux () (_ BitVec 32)
          (ite (= i #b1)
               ((_ extract 63 32) pack)
               ((_ extract 31 0) pack)))

        (assert (not (= out mux)))
        (assert (= (select a i) #x11111111))
        (assert (= out #x22222222))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_lowered_packed_bv32_mux_output_rejects_or_context_11936() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 32)))
        (declare-fun i () (_ BitVec 1))
        (declare-fun out () (_ BitVec 32))
        (declare-fun p () Bool)

        (define-fun pack () (_ BitVec 64)
          (concat (select a #b1) (select a #b0)))

        (define-fun mux () (_ BitVec 32)
          (ite (= i #b1)
               ((_ extract 63 32) pack)
               ((_ extract 31 0) pack)))

        (assert (or (= out mux) p))
        (assert p)
        (assert (= (select a i) #x11111111))
        (assert (= out #x22222222))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_packed_mux_rejects_unrelated_path_guard_11936() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 32)))
        (declare-fun i () (_ BitVec 1))
        (declare-fun j () (_ BitVec 1))
        (declare-fun out () (_ BitVec 32))

        (define-fun pack () (_ BitVec 64)
          (concat (select a #b1) (select a #b0)))

        (define-fun lane0 () (_ BitVec 32) ((_ extract 31 0) pack))
        (define-fun lane1 () (_ BitVec 32) ((_ extract 63 32) pack))
        (define-fun mux () (_ BitVec 32)
          (ite (= j #b0)
               (ite (= i #b1) lane1 lane0)
               (ite (= i #b1) lane0 lane1)))

        (assert (= out mux))
        (assert (= j #b1))
        (assert (= i #b1))
        (assert (= (select a #b0) #x11111111))
        (assert (= (select a #b1) #x22222222))
        (assert (= (select a i) #x22222222))
        (assert (= out #x11111111))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_packed_mux_rejects_wide_false_eq_guard_11936() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 2) (_ BitVec 32)))
        (declare-fun i () (_ BitVec 2))
        (declare-fun out () (_ BitVec 32))

        (define-fun pack () (_ BitVec 128)
          (concat (select a #b11)
          (concat (select a #b10)
          (concat (select a #b01) (select a #b00)))))

        (define-fun lane0 () (_ BitVec 32) ((_ extract 31 0) pack))
        (define-fun lane1 () (_ BitVec 32) ((_ extract 63 32) pack))
        (define-fun mux () (_ BitVec 32)
          (ite (= i #b00) lane1 lane0))

        (assert (= out mux))
        (assert (= i #b01))
        (assert (= (select a #b00) #x11111111))
        (assert (= (select a #b01) #x22222222))
        (assert (= (select a i) #x22222222))
        (assert (= out #x11111111))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_small_finite_array_extract_fc_ignores_cross_budget_11936() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const mem (Array (_ BitVec 4) (_ BitVec 32)))"
    )
    .unwrap();

    for i in 0..16u8 {
        writeln!(
            smt,
            "(assert (= (select mem #x{i:x}) #x{:08x}))",
            u32::from(i) + 1
        )
        .unwrap();
    }

    for i in 0..220u16 {
        writeln!(smt, "(declare-const p{i} (_ BitVec 4))").unwrap();
        writeln!(
            smt,
            "(assert (= (select mem p{i}) #x{:08x}))",
            0x1000u32 + u32::from(i)
        )
        .unwrap();
    }

    writeln!(smt, "(declare-const x (_ BitVec 32))").unwrap();
    writeln!(smt, "(assert (= ((_ extract 3 0) x) #x3))").unwrap();
    writeln!(
        smt,
        "(assert (= (select mem ((_ extract 3 0) x)) #x22222222))"
    )
    .unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
#[ntest::timeout(10_000)]
fn test_executor_qf_abv_cegar_fc_row2_aliasing_unsat_8510() {
    // ROW2 aliasing test: store at index i, read at index j where BV
    // antisymmetry forces i == j. Expressing that fact as two inequalities is
    // intentional: a direct `(= i j)` is eliminated by Phase-0 substitution
    // and folds the select before the array route, making the test vacuous.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 16) (_ BitVec 8)))
        (declare-const i (_ BitVec 16))
        (declare-const j (_ BitVec 16))
        (assert (bvule i j))
        (assert (bvule j i))
        (assert (= (select (store mem i #xAA) j) #xBB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // UNSAT: i <= j <= i means select(store(mem, i, #xAA), j) = #xAA, not #xBB.
    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    for (key, expected) in [
        ("smt.array.finite_ext.candidate_equalities", 0),
        ("smt.array.finite_ext.emitted_equalities", 0),
        ("smt.array.finite_ext.budget_deferred_equalities", 0),
        ("smt.abv.array_fixpoint.complex_selects", 1),
        ("smt.abv.array_fixpoint.runs", 1),
        ("smt.abv.array_fixpoint.skips", 0),
        ("smt.abv.array_fc_cegar.refinement_rounds", 0),
    ] {
        assert_eq!(
            stats.get_int(key),
            Some(expected),
            "unexpected {key} statistic: {stats:?}"
        );
    }
}

#[test]
fn test_executor_qf_abv_many_constant_selects_with_symbolic_contradiction_unsat_8510() {
    // Pattern from csplit benchmarks: many constant-indexed selects on the
    // same array, plus two symbolic selects that must alias but have
    // contradictory values. Tests that FC axioms cover the critical pair
    // even when many constant-symbolic pairs consume the budget.
    use std::fmt::Write;
    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const mem (Array (_ BitVec 16) (_ BitVec 8)))"
    )
    .unwrap();

    // 100 constant-indexed selects
    for i in 0..100u16 {
        writeln!(
            smt,
            "(assert (= (select mem #x{i:04x}) #x{:02x}))",
            (i % 256) as u8
        )
        .unwrap();
    }

    // Two symbolic selects that must be equal
    writeln!(smt, "(declare-const p (_ BitVec 16))").unwrap();
    writeln!(smt, "(declare-const q (_ BitVec 16))").unwrap();
    writeln!(smt, "(assert (= p q))").unwrap();
    writeln!(smt, "(assert (= (select mem p) #xAA))").unwrap();
    writeln!(smt, "(assert (= (select mem q) #xBB))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // UNSAT: p == q means select(mem, p) == select(mem, q), but 0xAA != 0xBB.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "expected unsat or unknown, got {outputs:?} — false SAT is a soundness bug"
    );
}

#[test]
fn test_executor_qf_abv_store_chain_constant_selects_symbolic_contradiction_unsat_8510() {
    // Pattern from csplit benchmarks: a store chain builds up a memory image
    // by writing known values at known addresses. Many constant-indexed selects
    // read those values back. Two symbolic selects at aliasing indices must
    // have equal values but don't.
    //
    // This specifically tests the case where selects read through store chains
    // (not a plain declared array), which exercises the expand_select_store
    // and ROW axiom paths alongside FC axioms.
    use std::fmt::Write;
    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const mem0 (Array (_ BitVec 16) (_ BitVec 8)))"
    )
    .unwrap();

    // Build a store chain: mem0 -> mem1 -> mem2 -> ... -> memN
    // storing known bytes at known addresses (like initializing memory).
    let n_stores = 50;
    for i in 0..n_stores {
        writeln!(
            smt,
            "(declare-const mem{} (Array (_ BitVec 16) (_ BitVec 8)))",
            i + 1
        )
        .unwrap();
        writeln!(
            smt,
            "(assert (= mem{} (store mem{} #x{:04x} #x{:02x})))",
            i + 1,
            i,
            i,
            (i * 3 + 7) % 256
        )
        .unwrap();
    }

    let final_mem = format!("mem{n_stores}");

    // Read back many constant-indexed values through the final store chain
    for i in 0..n_stores {
        writeln!(
            smt,
            "(assert (= (select {final_mem} #x{:04x}) #x{:02x}))",
            i,
            (i * 3 + 7) % 256
        )
        .unwrap();
    }

    // Two symbolic pointers that must alias, reading contradictory values
    writeln!(smt, "(declare-const p (_ BitVec 16))").unwrap();
    writeln!(smt, "(declare-const q (_ BitVec 16))").unwrap();
    writeln!(smt, "(assert (= p q))").unwrap();
    writeln!(smt, "(assert (= (select {final_mem} p) #xAA))").unwrap();
    writeln!(smt, "(assert (= (select {final_mem} q) #xBB))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // UNSAT: p == q means select(memN, p) == select(memN, q), but 0xAA != 0xBB.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "expected unsat or unknown, got {outputs:?} — false SAT is a soundness bug (#8510)"
    );
}

#[test]
fn test_executor_qf_abv_csplit_like_many_constant_selects_deep_chain_unsat_8510() {
    // More realistic csplit pattern: a large memory array with a deep store chain,
    // hundreds of constant-indexed reads, and symbolic pointer constraints.
    // The FC axiom budget (200) is insufficient for the cross-base pairs between
    // hundreds of constant selects and the symbolic selects.
    use std::fmt::Write;
    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const mem (Array (_ BitVec 16) (_ BitVec 8)))"
    )
    .unwrap();

    // Build a store chain with symbolic index writes (mimicking KLEE memory ops)
    let n_sym_stores = 6;
    let mut current_mem = "mem".to_string();
    for i in 0..n_sym_stores {
        writeln!(smt, "(declare-const si{i} (_ BitVec 16))").unwrap();
        writeln!(smt, "(declare-const sv{i} (_ BitVec 8))").unwrap();
        let next_mem = format!("mem_s{i}");
        writeln!(
            smt,
            "(declare-const {next_mem} (Array (_ BitVec 16) (_ BitVec 8)))"
        )
        .unwrap();
        writeln!(
            smt,
            "(assert (= {next_mem} (store {current_mem} si{i} sv{i})))"
        )
        .unwrap();
        current_mem = next_mem;
    }

    // Many constant-indexed selects on the final memory
    // (reading back a string or buffer byte-by-byte)
    let n_const_selects = 150;
    for i in 0..n_const_selects {
        // Constrain each byte to a specific value
        let addr = 0x1000u16 + i;
        let val = ((i * 7 + 13) % 256) as u8;
        writeln!(
            smt,
            "(assert (= (select {current_mem} #x{addr:04x}) #x{val:02x}))"
        )
        .unwrap();
    }

    // Two symbolic pointers that alias but read contradictory values.
    // This pair's FC axiom might not be generated eagerly if the budget
    // is exhausted by constant-symbolic cross-base pairs.
    writeln!(smt, "(declare-const ptr_a (_ BitVec 16))").unwrap();
    writeln!(smt, "(declare-const ptr_b (_ BitVec 16))").unwrap();
    writeln!(smt, "(assert (= ptr_a ptr_b))").unwrap();
    writeln!(smt, "(assert (= (select {current_mem} ptr_a) #xFE))").unwrap();
    writeln!(smt, "(assert (= (select {current_mem} ptr_b) #xFD))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // UNSAT: ptr_a == ptr_b means the selects must agree, but 0xFE != 0xFD.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "expected unsat or unknown, got {outputs:?} — false SAT is a soundness bug (#8510)"
    );
}

#[test]
fn test_executor_qf_abv_indirect_pointer_equality_unsat_8510() {
    // The pointer equality is NOT a direct assertion (= p q) but is
    // implied through BV constraints: both p and q are forced to the
    // same concrete value by range constraints.
    //
    // This is the pattern in csplit benchmarks: symbolic pointers are
    // constrained by path conditions from KLEE, not by direct equalities.
    // Variable substitution preprocessing does NOT unify them, so the
    // FC axiom between select(mem, p) and select(mem, q) is needed.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const p (_ BitVec 8))
        (declare-const q (_ BitVec 8))
        ; p is forced to #x42 by bounds
        (assert (bvule #x42 p))
        (assert (bvule p #x42))
        ; q is forced to #x42 by bounds
        (assert (bvule #x42 q))
        (assert (bvule q #x42))
        ; But selects at p and q have contradictory values
        (assert (= (select mem p) #xAA))
        (assert (= (select mem q) #xBB))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // UNSAT: p = q = #x42, so select(mem, p) = select(mem, q), but 0xAA != 0xBB.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "expected unsat or unknown, got {outputs:?} — false SAT is a soundness bug (#8510)"
    );
}

#[test]
fn test_executor_qf_abv_indirect_equality_many_constants_unsat_8510() {
    // Like the indirect pointer equality test, but with many constant-indexed
    // selects to exhaust the FC cross-base budget. The critical pair (p, q) has
    // indirect equality via BV bounds, not via (= p q).
    use std::fmt::Write;
    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const mem (Array (_ BitVec 16) (_ BitVec 8)))"
    )
    .unwrap();

    // 250 constant-indexed selects to exhaust FC budget
    for i in 0..250u16 {
        writeln!(
            smt,
            "(assert (= (select mem #x{i:04x}) #x{:02x}))",
            (i % 256) as u8
        )
        .unwrap();
    }

    // Two symbolic pointers forced to same value by BV bounds (not direct equality)
    writeln!(smt, "(declare-const p (_ BitVec 16))").unwrap();
    writeln!(smt, "(declare-const q (_ BitVec 16))").unwrap();
    writeln!(smt, "(assert (bvule #x1000 p))").unwrap();
    writeln!(smt, "(assert (bvule p #x1000))").unwrap();
    writeln!(smt, "(assert (bvule #x1000 q))").unwrap();
    writeln!(smt, "(assert (bvule q #x1000))").unwrap();

    writeln!(smt, "(assert (= (select mem p) #xAA))").unwrap();
    writeln!(smt, "(assert (= (select mem q) #xBB))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // p = q = #x1000, select(mem,p) must equal select(mem,q), 0xAA != 0xBB → UNSAT.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "expected unsat or unknown, got {outputs:?} — false SAT is a soundness bug (#8510)"
    );
}

#[test]
#[ntest::timeout(10_000)]
fn test_executor_qf_abv_fixpoint_gate_skipped_fc_violation_unsat_8510() {
    // Regression for the old pre-dispatch finite-extensionality explosion.
    //
    // Four store-flat aliases over a BV5-indexed array used to be expanded into
    // 128 select pairs before route preprocessing. Those generated
    // terms retained every alias and multiplied later ROW/FC work. Exact
    // closure now belongs to the QF_ABV route after its own preprocessing; the
    // remaining live ROW surface stays bounded and the indirect equality is
    // solved exactly.
    use std::fmt::Write;
    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(smt, "(declare-const mem (Array (_ BitVec 5) (_ BitVec 8)))").unwrap();

    // Keep enough aliases to distinguish raw eager expansion from the bounded
    // post-route surface while leaving ample headroom under the test timeout.
    let n_stores = 4;
    let mut current_mem = "mem".to_string();
    for i in 0..n_stores {
        writeln!(smt, "(declare-const idx{i} (_ BitVec 5))").unwrap();
        writeln!(smt, "(declare-const val{i} (_ BitVec 8))").unwrap();
        let next_mem = format!("m{i}");
        writeln!(
            smt,
            "(declare-const {next_mem} (Array (_ BitVec 5) (_ BitVec 8)))"
        )
        .unwrap();
        writeln!(
            smt,
            "(assert (= {next_mem} (store {current_mem} idx{i} val{i})))"
        )
        .unwrap();
        current_mem = next_mem;
    }

    let n_reads = 2;
    for i in 0..n_reads {
        writeln!(smt, "(declare-const r{i} (_ BitVec 8))").unwrap();
        writeln!(smt, "(assert (= r{i} (select {current_mem} idx{i})))").unwrap();
    }

    // Two reads at pointers forced to be equal via BV bounds
    writeln!(smt, "(declare-const pa (_ BitVec 5))").unwrap();
    writeln!(smt, "(declare-const pb (_ BitVec 5))").unwrap();
    writeln!(smt, "(assert (bvule #b11111 pa))").unwrap();
    writeln!(smt, "(assert (bvule pa #b11111))").unwrap();
    writeln!(smt, "(assert (bvule #b11111 pb))").unwrap();
    writeln!(smt, "(assert (bvule pb #b11111))").unwrap();
    writeln!(smt, "(assert (= (select {current_mem} pa) #xAA))").unwrap();
    writeln!(smt, "(assert (= (select {current_mem} pb) #xBB))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // pa = pb = #b11111, so select(mem, pa) = select(mem, pb) → 0xAA != 0xBB.
    assert_eq!(outputs, vec!["unsat"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.route_deferrals"),
        Some(1),
        "the raw store-flat window must be deferred without traversing it"
    );
    let candidate_equalities = exec
        .statistics()
        .get_int("smt.array.finite_ext.candidate_equalities")
        .expect("finite closure must publish candidate telemetry");
    assert!(
        candidate_equalities < 48,
        "post-route closure must stay well below the 128 raw-alias expansion; got {candidate_equalities}"
    );
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(0)
    );
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.candidate_scan_truncated"),
        Some(0)
    );
    assert_eq!(
        exec.statistics().get_int("smt.abv.array_fixpoint.runs"),
        Some(1)
    );
    assert_eq!(
        exec.statistics().get_int("smt.abv.array_fixpoint.skips"),
        Some(0)
    );
}

#[test]
fn test_executor_qf_abv_dense_array_initializer_range_rewrite_unsat_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 12) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(
        smt,
        "(declare-const bytes (Array (_ BitVec 8) (_ BitVec 4)))"
    )
    .unwrap();

    for idx in 0..128u16 {
        writeln!(smt, "(assert (= (select table #b{idx:012b}) #x00))").unwrap();
    }

    // `select bytes #x00` ranges over 0..15. After zero-extension, appending
    // three zero bits, and adding seven, the table index ranges over 7..127.
    // Every byte in that interval is asserted to be zero, so this negated
    // equality is unsatisfiable without 128 functional-consistency pairs.
    writeln!(
        smt,
        "(assert (= false (= #x00 (select table (bvadd #b000000000111 (concat ((_ zero_extend 5) (select bytes #x00)) #b000))))))"
    )
    .unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.rewrites")
            .unwrap_or(0)
            > 0,
        "dense initializer range rewrite should fire; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_dense_array_sparse_predicate_rewrite_unsat_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(smt, "(declare-const idx (_ BitVec 8))").unwrap();

    for idx in 0..=255u16 {
        let value = if matches!(idx, 9 | 10 | 32) { 1 } else { 0 };
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x{value:02x}))").unwrap();
    }

    writeln!(smt, "(assert (= false (= #x00 (select table idx))))").unwrap();
    writeln!(smt, "(assert (not (= idx #x09)))").unwrap();
    writeln!(smt, "(assert (not (= idx #x0a)))").unwrap();
    writeln!(smt, "(assert (not (= idx #x20)))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.predicate_rewrites")
            .unwrap_or(0)
            > 0,
        "dense sparse-predicate rewrite should fire; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_dense_array_masked_concat_predicate_rewrite_unsat_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 32) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(
        smt,
        "(declare-const bytes (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();

    for idx in 0..=256u16 {
        let value = if matches!(idx, 10 | 33) { 0x20 } else { 0x00 };
        writeln!(
            smt,
            "(assert (= (select table (_ bv{idx} 32)) #x{value:02x}))"
        )
        .unwrap();
    }

    writeln!(
        smt,
        "(define-fun idx () (_ BitVec 32) ((_ zero_extend 24) (select bytes #x00)))"
    )
    .unwrap();
    writeln!(
        smt,
        "(assert (= false (= #x00000000 (bvand ((_ zero_extend 16) (concat (select table (bvadd #x00000001 idx)) (select table idx))) #x00002000))))"
    )
    .unwrap();
    writeln!(smt, "(assert (not (= (bvadd #x00000001 idx) (_ bv10 32))))").unwrap();
    writeln!(smt, "(assert (not (= (bvadd #x00000001 idx) (_ bv33 32))))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.predicate_rewrites")
            .unwrap_or(0)
            > 0,
        "dense masked-concat predicate rewrite should fire; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_finite_array_sparse_predicate_hole_fails_closed_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(smt, "(declare-const raw (_ BitVec 8))").unwrap();
    writeln!(smt, "(define-fun idx () (_ BitVec 8) (bvand raw #x03))").unwrap();

    for idx in [0u8, 2, 3] {
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x00))").unwrap();
    }
    writeln!(smt, "(assert (= false (= #x00 (select table idx))))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.abv.finite_array.predicate_rewrites")
            .unwrap_or(0),
        0,
        "sparse predicate rewrite must fail closed when any ranged index is undefined; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_finite_array_sparse_predicate_range_cap_fails_closed_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 16) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(smt, "(declare-const idx (_ BitVec 16))").unwrap();

    for idx in 0..16u16 {
        writeln!(smt, "(assert (= (select table (_ bv{idx} 16)) #x00))").unwrap();
    }
    writeln!(smt, "(assert (= false (= #x00 (select table idx))))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.abv.finite_array.predicate_rewrites")
            .unwrap_or(0),
        0,
        "sparse predicate rewrite must not enumerate ranges above the cap; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_finite_array_masked_concat_multi_leaf_fails_closed_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(smt, "(declare-const raw (_ BitVec 8))").unwrap();
    writeln!(smt, "(define-fun idx () (_ BitVec 8) (bvand raw #x03))").unwrap();

    for idx in 0..4u8 {
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x00))").unwrap();
    }
    writeln!(
        smt,
        "(assert (= #x0000 (bvand (concat (select table idx) (select table idx)) #x0101)))"
    )
    .unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.abv.finite_array.predicate_rewrites")
            .unwrap_or(0),
        0,
        "masked-concat predicate rewrite must reject masks spanning multiple concat leaves; statistics={:?}",
        exec.statistics()
    );
}

/// #retain-parsed-verdict-divergence — dropping the parsed AST must not
/// change a verdict.
///
/// `set_retain_parsed_assertions(false)` is a peak-RSS optimization the CLI
/// applies whenever no proof artifact can be emitted (`--no-proof`,
/// `--z3-mode`, competition mode). Before the fix in
/// `executor/proof_rewrite.rs`, `apply_input_syntax_rewrites_to_proof`
/// returned early on an empty parsed stack and so ALSO skipped the
/// assume-authorization tail; the QF_ABV dense finite-array rewrite's `assume`
/// leaf then stayed unauthorized and the mandatory UNSAT certificate rejected
/// the refutation with "assumes term outside the supplied problem obligation".
/// Measured at that commit: `ay --z3-mode` printed `unknown` on this exact
/// file where z3 5.0.0, `ay` default mode and the sibling test below all print
/// `unsat`.
///
/// `rewrites`/`exact_rewrites` are asserted too so this cannot pass vacuously
/// by some other route deciding the query while the dense pass stays dead.
#[test]
fn test_executor_qf_abv_exact_select_unsat_survives_dropped_parsed_ast_11928() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    for idx in 0..32u8 {
        let value = u8::from(idx == 9);
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x{value:02x}))").unwrap();
    }
    writeln!(smt, "(assert (= false (= #x01 (select table #x09))))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    // Exactly what `--no-proof` / `--z3-mode` / competition mode do.
    exec.set_retain_parsed_assertions(false);
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "the peak-RSS parsed-AST drop must not revoke a certified refutation; \
         unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.exact_rewrites")
            .unwrap_or(0)
            > 0,
        "the dense finite-array pass must still be the route under test; statistics={:?}",
        exec.statistics()
    );
}

/// Sibling of the test above for the SPARSE-PREDICATE rewrite shape, which
/// reaches the certificate through `build_index_membership` (a freshly minted
/// disjunction) rather than a constant substitution. Same invariant: the
/// parsed-AST retention flag is a memory knob, never a verdict knob.
#[test]
fn test_executor_qf_abv_sparse_predicate_unsat_survives_dropped_parsed_ast_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(smt, "(declare-const idx (_ BitVec 8))").unwrap();

    for idx in 0..=255u16 {
        let value = u16::from(matches!(idx, 9 | 10 | 32));
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x{value:02x}))").unwrap();
    }

    writeln!(smt, "(assert (= false (= #x00 (select table idx))))").unwrap();
    writeln!(smt, "(assert (not (= idx #x09)))").unwrap();
    writeln!(smt, "(assert (not (= idx #x0a)))").unwrap();
    writeln!(smt, "(assert (not (= idx #x20)))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(false);
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "the peak-RSS parsed-AST drop must not revoke a certified refutation; \
         unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.predicate_rewrites")
            .unwrap_or(0)
            > 0,
        "the dense sparse-predicate rewrite must still be the route under test; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_finite_array_exact_select_rewrite_unsat_11928() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    for idx in 0..32u8 {
        let value = if idx == 9 { 1 } else { 0 };
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x{value:02x}))").unwrap();
    }
    writeln!(smt, "(assert (= false (= #x01 (select table #x09))))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.exact_rewrites")
            .unwrap_or(0)
            > 0,
        "finite array exact select rewrite should fire; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_finite_array_exact_select_rewrite_sat_validates_11924() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    for idx in 0..32u8 {
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x00))").unwrap();
    }
    writeln!(smt, "(assert (= #x01 (bvadd #x01 (select table #x09))))").unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.exact_rewrites")
            .unwrap_or(0)
            > 0,
        "finite array exact direct-select rewrite should fire on SAT path; statistics={:?}",
        exec.statistics()
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation_failures")
            .unwrap_or(0),
        0,
        "SAT exact direct-select rewrite should validate; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_finite_array_exact_select_peels_disjoint_store_11928() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(smt, "(declare-const high (_ BitVec 4))").unwrap();
    for idx in 0..32u8 {
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x00))").unwrap();
    }
    writeln!(
        smt,
        "(assert (= false (= #x00 (select (store table (concat #b1111 high) #xff) #x09))))"
    )
    .unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.exact_rewrites")
            .unwrap_or(0)
            > 0,
        "finite array exact select rewrite should peel disjoint store; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_dense_array_range_select_peels_disjoint_store_11928() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(
        smt,
        "(declare-const table (Array (_ BitVec 8) (_ BitVec 8)))"
    )
    .unwrap();
    writeln!(
        smt,
        "(declare-const bytes (Array (_ BitVec 8) (_ BitVec 4)))"
    )
    .unwrap();
    for idx in 0..64u8 {
        writeln!(smt, "(assert (= (select table #x{idx:02x}) #x00))").unwrap();
    }
    writeln!(
        smt,
        "(assert (= false (= #x00 (select (store table #xff #x7f) ((_ zero_extend 4) (select bytes #x00))))))"
    )
    .unwrap();
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
    assert!(
        exec.statistics()
            .get_int("smt.abv.finite_array.rewrites")
            .unwrap_or(0)
            > 0,
        "dense array range rewrite should peel disjoint store; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_bv1_same_ite_alias_chain_model_recovery_11936() {
    use std::fmt::Write;

    let mut smt = String::new();
    writeln!(smt, "(set-logic QF_ABV)").unwrap();
    writeln!(smt, "(declare-fun c () (_ BitVec 1))").unwrap();
    writeln!(smt, "(assert (= c #b1))").unwrap();

    for idx in 0..24 {
        writeln!(smt, "(declare-fun v{idx} () (_ BitVec 1))").unwrap();
    }
    for idx in 0..24 {
        writeln!(smt, "(assert (= v{idx} (ite (= c #b1) #b1 #b0)))").unwrap();
    }
    writeln!(smt, "(check-sat)").unwrap();

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(
        exec.statistics()
            .get_int("model_validation_failures")
            .unwrap_or(0),
        0,
        ">10-deep same-ITE BV1 alias chain should validate after substitution model recovery; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_try_nested_bv1_select_wrapper_delegates_with_sources_9732() {
    let Some(input) = optional_qf_abv_benchmark(
        "try5_small_difret_functions_flanagansaxe_fmt.set_quoting_style.il.flanagansaxe.smt2",
    ) else {
        return;
    };

    let commands = parse(&input).expect("valid QF_ABV try input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_ABV try");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "QF_ABV try BV1 wrapper split into source-mapped covered BV roots should delegate; outputs={outputs:?}; unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation_failures")
            .unwrap_or(0),
        0,
        "source-covered BV1 wrapper should not fail model validation"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.restored_delegated_assertions"),
        Some(1),
        "the restored wrapper should be delegated only through explicit source coverage"
    );
}

#[test]
fn test_executor_qf_abv_try_nested_bv1_select_wrapper_validates_11920() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (forall ((i (_ BitVec 1))) (= (select a i) #b0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_ABV try input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_ABV try");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "QF_ABV BV1 universal select wrapper should return SAT once both finite-domain expansions have exact BV coverage; outputs={outputs:?}; unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation_failures")
            .unwrap_or(0),
        0,
        "independently validated QF_ABV SAT model must not be rejected"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.coverage_assertions"),
        Some(2),
        "BV1 has exactly two finite-domain instances"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.covered_assertions"),
        Some(2),
        "both finite-domain instances must be covered by the BV encoding"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.source_sets_present"),
        Some(1),
        "coverage must carry explicit source provenance"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.source_sets_valid"),
        Some(1),
        "source provenance must pass the structural validity gate"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.source_mapped_assertions"),
        Some(1),
        "both expansions must map back to their single preprocessed root"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.split_source_assertions"),
        Some(1),
        "the source ledger must record that the root split into two expansions"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.bv.restored_delegated_assertions"),
        Some(3),
        "the restored root and its two exact leaves must retain BV authority"
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation.checked")
            .unwrap_or(0),
        0,
        "quantified syntax must not be relabelled as generic evaluator evidence"
    );
    assert_eq!(
        exec.statistics().get_string("model_check_gate.result"),
        Some("confirmed-sat"),
        "exhaustive BV-domain coverage must certify the quantified root"
    );
    assert_eq!(
        exec.statistics()
            .get_string("model_check_gate.cannot_confirm_reason"),
        None,
        "an exactly certified BV quantifier must not retain a refusal reason"
    );
}

#[test]
fn test_executor_qf_abv_nested_bv1_direct_select_wrapper_keeps_unsat_9732() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= b (store a #x00 #x01)))
        (assert (= #b1 (bvand (ite (= (select b #x00) #x02) #b1 #b0) #b1)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid QF_ABV nested wrapper input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute QF_ABV nested wrapper input");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "source-covered BV1 wrappers must not hide a contradictory direct array select; outputs={outputs:?}; unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_dwp_current_bv_array_wrapper_delegates_11936() {
    let Some(input) = optional_qf_abv_benchmark(
        "try5_small_difret_functions_dwp_tty.close_stdout_set_file_name.il.dwp.smt2",
    ) else {
        return;
    };

    let commands = parse(&input).expect("valid QF_ABV DWP input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute QF_ABV DWP input");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "BV-covered current QF_ABV wrapper should validate via BV delegation; unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation_failures")
            .unwrap_or(0),
        0,
        "BV-covered current assertion should not fail model validation; statistics={:?}",
        exec.statistics()
    );
    assert!(
        exec.statistics()
            .get_int("model_validation.bv.restored_delegated_assertions")
            .unwrap_or(0)
            > 0,
        "current BV-covered assertion should be available to strict model validation; statistics={:?}",
        exec.statistics()
    );
}

#[test]
fn test_executor_qf_abv_no_init_multi_member_array_wrappers_delegate_11936() {
    let Some(input) = optional_qf_abv_benchmark("no_init_multi_member10.smt2") else {
        return;
    };

    let commands = parse(&input).expect("valid QF_ABV no-init input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute QF_ABV no-init input");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "covered current QF_ABV array wrappers should validate by BV delegation; unknown_reason={:?}; statistics={:?}",
        exec.unknown_reason(),
        exec.statistics()
    );
    assert_eq!(
        exec.statistics()
            .get_int("model_validation_failures")
            .unwrap_or(0),
        0,
        "covered no-init array wrapper should not fail model validation; statistics={:?}",
        exec.statistics()
    );
    assert!(
        exec.statistics()
            .get_int("model_validation.array_delegated")
            .unwrap_or(0)
            > 0,
        "no-init array wrappers should be delegated to the covered BV encoding; statistics={:?}",
        exec.statistics()
    );
}

// BV/LIA bridge shift coverage. These cases exercise the pure-BV translation
// used to justify integer bounds over `bv2nat`; the SAT cardinals ensure the
// bridge never manufactures a false upper bound.

#[test]
fn test_executor_bv_lia_bridge_lshr_upper_bound_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (assert (>= n 0))
        (assert (<= n 255))
        (assert (> (bv2nat (bvlshr ((_ int2bv 8) n) ((_ int2bv 8) 1))) 127))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse bvlshr upper-bound input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute bvlshr upper-bound input");
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_bv_lia_bridge_ashr_unsigned_range_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (assert (>= n 0))
        (assert (<= n 255))
        (assert (> (bv2nat (bvashr ((_ int2bv 8) n) ((_ int2bv 8) 1))) 255))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse bvashr range input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute bvashr range input");
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_bv_lia_bridge_shl_mask_upper_bound_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (assert (>= n 0))
        (assert (<= n 255))
        (assert (> (bv2nat (bvand (bvshl ((_ int2bv 8) n) ((_ int2bv 8) 4)) #x0f)) 0))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse bvshl mask input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute bvshl mask input");
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_bv_lia_bridge_lshr64_probe_upper_bound_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const v Int)
        (assert (>= v 0))
        (assert (<= v 18446744073709551615))
        (assert (> (bv2nat (bvlshr ((_ int2bv 64) v) ((_ int2bv 64) 32))) 4294967295))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse 64-bit bvlshr input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute 64-bit bvlshr input");
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_bv_lia_bridge_lshr_sat_bound_not_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (assert (>= n 0))
        (assert (<= n 255))
        (assert (> (bv2nat (bvlshr ((_ int2bv 8) n) ((_ int2bv 8) 1))) 50))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse satisfiable bvlshr input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute satisfiable bvlshr input");
    assert_ne!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_bv_lia_bridge_lshr_exact_boundary_sat_not_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (assert (>= n 0))
        (assert (<= n 255))
        (assert (> (bv2nat (bvlshr ((_ int2bv 8) n) ((_ int2bv 8) 1))) 126))
        (check-sat)
    "#;
    let commands = parse(input).expect("parse bvlshr boundary input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute bvlshr boundary input");
    assert_ne!(outputs, vec!["unsat"]);
}
