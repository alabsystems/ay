// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `array_soundness_4304` to preserve test FQNs.

// --- Regression tests for #4665: symbolic-index ROW2 with arithmetic disequality ---

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_arithmetic_disequality_4665() {
    // y = x + 1 implies x ≠ y, so select(store(a,x,42),y) = select(a,y).
    // Combined with select(store(a,x,42),y) = 42 and select(a,y) ≠ 42, this is unsat.
    // Previously returned false sat because the array solver didn't learn x ≠ y from LIA.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= y (+ x 1)))
        (assert (= (select (store a x 42) y) 42))
        (assert (not (= (select a y) 42)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "ROW2 + arithmetic disequality: y=x+1 implies select(store(a,x,42),y) = select(a,y)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_explicit_disequality_4665() {
    // Direct disequality i ≠ j + ROW2: select(store(a,i,42),j) must equal select(a,j).
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (not (= (select (store a i 42) j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "ROW2: i≠j → select(store(a,i,42),j) = select(a,j)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row2_intermediate_variable_4665() {
    // b = store(a,i,42), select(b,j) ≠ select(a,j) with i ≠ j: unsat by ROW2 + equality.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (= b (store a i 42)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "ROW2 through intermediate variable: b=store(a,i,42), i≠j → select(b,j) = select(a,j)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_row_symbolic_non_alias_sat_4665_matrix() {
    // Corrected #4665 SAT/UNSAT matrix: this symbolic ROW shape is SAT.
    // With i ≠ j, select(store(a,i,42),j) can still be 42 when a[j] = 42.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (not (= i j)))
        (assert (= (select (store a i 42) j) 42))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "sat",
        "symbolic non-alias read-over-write can be SAT when the base array already stores 42 at j"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflia_const_array_non_alias_unsat_4665() {
    // Reproducer for #4665:
    // domain = store(const 0, addr1, 1), addr1 ≠ addr2, select(domain, addr2) = 1.
    // Since addr2 reads the const default 0, this must be UNSAT.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const addr1 Int)
        (declare-const addr2 Int)
        (declare-const domain (Array Int Int))
        (assert (= domain (store ((as const (Array Int Int)) 0) addr1 1)))
        (assert (not (= addr1 addr2)))
        (assert (= (select domain addr2) 1))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "non-aliased read from store(const 0, addr1, 1) must return 0, not 1"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflra_row2_arithmetic_disequality_4665() {
    // Real-index variant of #4665: y = x + 0.5 implies x ≠ y.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLRA)
        (declare-fun a () (Array Real Real))
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (= y (+ x 0.5)))
        (assert (= (select (store a x 42.0) y) 42.0))
        (assert (not (= (select a y) 42.0)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "AUFLRA ROW2: y=x+0.5 implies select(store(a,x,42),y)=select(a,y)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_auflira_row2_arithmetic_disequality_4665() {
    // Mixed-theory variant: real array indices are solved via LRA in AUFLIRA.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIRA)
        (declare-fun a () (Array Real Real))
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (= y (+ x 1.5)))
        (assert (= (select (store a x 3.0) y) 3.0))
        (assert (not (= (select a y) 3.0)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "AUFLIRA ROW2: y=x+1.5 must force non-alias read-over-write"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_store_congruence_base_equality_5116() {
    // Store congruence: if a = b then store(a,i,v) = store(b,i,v).
    // Without add_array_congruence_axioms, the eager QF_ABV path treats
    // (= a b) as an opaque Tseitin atom with no connection to store terms.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun v () (_ BitVec 8))
        (assert (= a b))
        (assert (not (= (store a #x00 v) (store b #x00 v))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: a=b must imply store(a,i,v)=store(b,i,v)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_store_chain_congruence_5116() {
    // Multiple store operations on equal base arrays must produce equal results.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-fun v1 () (_ BitVec 8))
        (declare-fun v2 () (_ BitVec 8))
        (assert (= a b))
        (define-fun a1 () (Array (_ BitVec 4) (_ BitVec 8)) (store a #x0 v1))
        (define-fun b1 () (Array (_ BitVec 4) (_ BitVec 8)) (store b #x0 v1))
        (define-fun a2 () (Array (_ BitVec 4) (_ BitVec 8)) (store a1 #x1 v2))
        (define-fun b2 () (Array (_ BitVec 4) (_ BitVec 8)) (store b1 #x1 v2))
        (assert (not (= a2 b2)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: same store chains on equal arrays must be equal"
    );
}

// --- QF_ABV soundness regressions (#5083) ---
// The original #5083 false SATs on try5_small_difret_functions_ground_* benchmarks
// were caused by the array extensionality bug (#4304). These tests verify
// the fix holds for BV array combinations.

#[test]
#[timeout(10_000)]
fn qf_abv_extensionality_bv_arrays_5083() {
    // Two BV arrays that differ at a known index must not be equal.
    // Requires extensionality Skolem diff witness generation in the BV path.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= (select a #x05) #xFF))
        (assert (= (select b #x05) #x00))
        (assert (= a b))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: arrays differing at index #x05 cannot be equal"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_row2_symbolic_bv_index_5083() {
    // ROW2 with symbolic BV index: select(store(a,i,v),j) where i!=j.
    // The array solver must generate the disequality axiom.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun i () (_ BitVec 8))
        (declare-fun j () (_ BitVec 8))
        (assert (not (= i j)))
        (assert (not (= (select (store a i #x42) j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV ROW2: i!=j -> select(store(a,i,v),j) = select(a,j)"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_store_read_back_bv_5083() {
    // Store then read back pattern with BV arrays — must be SAT.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-fun addr () (_ BitVec 32))
        (declare-fun val () (_ BitVec 8))
        (assert (= (select (store mem addr val) addr) val))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "sat",
        "QF_ABV: store-then-read-back must be SAT"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_memory_store_chain_unsat_5083() {
    // Byte-addressable memory pattern (common in binary analysis).
    // Store 4 bytes at addr, then read back expecting wrong value — UNSAT.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-fun addr () (_ BitVec 32))
        (define-fun mem1 () (Array (_ BitVec 32) (_ BitVec 8))
            (store (store (store (store mem
                addr #xDE)
                (bvadd addr #x00000001) #xAD)
                (bvadd addr #x00000002) #xBE)
                (bvadd addr #x00000003) #xEF))
        (assert (not (= (select mem1 addr) #xDE)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: byte-store chain read-back at base addr must equal stored value"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_memory_store_chain_adjacent_read_5083() {
    // Store at addr, read at addr+1 must get the second byte, not the first.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-fun addr () (_ BitVec 32))
        (define-fun mem1 () (Array (_ BitVec 32) (_ BitVec 8))
            (store (store mem addr #xAA) (bvadd addr #x00000001) #xBB))
        (assert (= (select mem1 (bvadd addr #x00000001)) #xAA))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: reading addr+1 must get #xBB not #xAA"
    );
}

#[test]
#[timeout(10_000)]
fn qf_abv_extensionality_with_store_5083() {
    // After storing different values at the same index, arrays must differ.
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun i () (_ BitVec 8))
        (define-fun a1 () (Array (_ BitVec 8) (_ BitVec 8)) (store a i #x00))
        (define-fun a2 () (Array (_ BitVec 8) (_ BitVec 8)) (store a i #xFF))
        (assert (= a1 a2))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "QF_ABV: store(a,i,0) != store(a,i,0xFF) via extensionality"
    );
}
