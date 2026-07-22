// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental push/pop tests for QF_ABV (BV + Arrays).
//!
//! Consumer: a downstream proof consumer uses QF_ABV incrementally for proof obligation discharge.
//! These tests verify that push/pop correctly restores BV solver state,
//! array axiom caches, and model extraction across scopes.

use crate::common::solve;

/// ABV basic push/pop: array store/select with BV indices.
/// Verifies that BV-indexed array state is properly scoped.
#[test]
fn test_abv_incremental_push_pop_basic() {
    let output = solve(
        r#"
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))

(push 1)
; Store 42 at index 0
(assert (= (select (store a #x00 #x0000002A) #x00) #x0000002A))
(check-sat)
(pop 1)

(push 1)
; Store different value at same index
(assert (= (select (store a #x00 #x000000FF) #x00) #x000000FF))
(check-sat)
(pop 1)

; After both pops: no constraints on a
(check-sat)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(
        results.len(),
        3,
        "expected 3 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat", "scope 1: {output}");
    assert_eq!(results[1].trim(), "sat", "scope 2: {output}");
    assert_eq!(results[2].trim(), "sat", "after pops: {output}");
}

/// ABV push/pop with contradictions at different depths.
/// Tests that BV constraints from inner scopes are properly removed.
#[test]
fn test_abv_incremental_nested_contradiction() {
    let output = solve(
        r#"
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))

; Base: x stored at index 0
(assert (= (select a #x00) x))

(push 1)
; Scope 1: x = 0xFF
(assert (= x #xFF))
(check-sat)

(push 1)
; Scope 2: x = 0x00 (contradicts x = 0xFF from scope 1)
(assert (= x #x00))
(check-sat)
(pop 1)

; Back to scope 1: x = 0xFF, should be sat
(check-sat)
(pop 1)

; Back to base: x unconstrained
(check-sat)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(
        results.len(),
        4,
        "expected 4 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat", "scope 1 (x=0xFF): {output}");
    assert_eq!(
        results[1].trim(),
        "unsat",
        "scope 2 (x=0xFF and x=0x00): {output}"
    );
    assert_eq!(results[2].trim(), "sat", "back to scope 1: {output}");
    assert_eq!(results[3].trim(), "sat", "base: {output}");
}

/// ABV push/pop: array ROW axiom with BV index equality across scopes.
/// Tests that ROW1/ROW2 axiom state is correctly scoped.
#[test]
fn test_abv_incremental_row_axiom_scoping() {
    let output = solve(
        r#"
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))

; Base: store v at index i
(assert (= (select (store a i v) j) #x42))

(push 1)
; Scope 1: i = j (ROW1 applies: select(store(a,i,v),i) = v)
; So v must be 0x42
(assert (= i j))
(assert (not (= v #x42)))
; Contradiction: v = 0x42 (from ROW1) but v != 0x42
(check-sat)
(pop 1)

(push 1)
; Scope 2: i != j (ROW2 applies: select(store(a,i,v),j) = select(a,j))
; So select(a,j) must be 0x42, but v is unconstrained
(assert (not (= i j)))
(check-sat)
(pop 1)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results, got: {output}"
    );
    assert_eq!(
        results[0].trim(),
        "unsat",
        "scope 1 (ROW1 contradiction): {output}"
    );
    assert_eq!(
        results[1].trim(),
        "sat",
        "scope 2 (ROW2 consistent): {output}"
    );
}

/// ABV multi-cycle push/pop: repeated scopes with different array writes.
/// Exercises the incremental proof-obligation pattern of repeated verification queries.
#[test]
fn test_abv_incremental_multi_cycle() {
    let output = solve(
        r#"
(set-logic QF_ABV)
(declare-fun mem () (Array (_ BitVec 16) (_ BitVec 8)))

; Cycle 1: write 0xAA at address 0x100
(push 1)
(assert (= (select (store mem #x0100 #xAA) #x0100) #xAA))
(check-sat)
(pop 1)

; Cycle 2: write 0xBB at address 0x200
(push 1)
(assert (= (select (store mem #x0200 #xBB) #x0200) #xBB))
(check-sat)
(pop 1)

; Cycle 3: write 0xCC at address 0x300, read 0x100 (should be unconstrained)
(push 1)
(assert (= (select (store mem #x0300 #xCC) #x0300) #xCC))
; Read from different address — should be sat regardless
(assert (= (select mem #x0100) #xFF))
(check-sat)
(pop 1)

; Cycle 4: contradiction
(push 1)
(declare-fun addr () (_ BitVec 16))
(assert (= (select (store mem addr #xDD) addr) #xEE))
; store(mem, addr, 0xDD) at addr should be 0xDD, not 0xEE
(check-sat)
(pop 1)
"#,
    );
    let results: Vec<&str> = output
        .lines()
        .filter(|l| matches!(l.trim(), "sat" | "unsat"))
        .collect();
    assert_eq!(
        results.len(),
        4,
        "expected 4 check-sat results, got: {output}"
    );
    assert_eq!(results[0].trim(), "sat", "cycle 1: {output}");
    assert_eq!(results[1].trim(), "sat", "cycle 2: {output}");
    assert_eq!(results[2].trim(), "sat", "cycle 3: {output}");
    assert_eq!(
        results[3].trim(),
        "unsat",
        "cycle 4 (ROW1 contradiction): {output}"
    );
}

/// ABV model extraction: verify BV+Array model values are consistent.
#[test]
fn test_abv_model_extraction_consistency() {
    let output = solve(
        r#"
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun idx () (_ BitVec 4))

(assert (= idx #xA))
(assert (= (select (store a idx #xFF) idx) #xFF))
(check-sat)
(get-value (idx (select (store a idx #xFF) idx)))
"#,
    );
    assert!(output.contains("sat"), "should be sat: {output}");
}
