// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for assumption-aware array axiom generation (#6736).
//!
//! When `check-sat-assuming` is used in incremental mode (after push/pop),
//! array axiom generation scopes its reachable set to terms in
//! `ctx.assertions`. Assumption-only array terms (store/select appearing
//! only in assumptions) must also be included in the reachable set,
//! otherwise their ROW/congruence/extensionality axioms are not generated.
//!
//! These tests place the critical store/select operations exclusively in
//! assumptions to verify that axiom generation covers them.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

// === QF_AUFLIA: assumption-only store requires ROW1 axiom ===

/// ROW1 via assumption: store(a, 0, 99) appears only in the assumption.
/// select(store(a, 0, 99), 0) must equal 99 by ROW1, contradicting
/// the assertion select(a, 0) = 42 combined with b = store(a, 0, 99)
/// and select(b, 0) = 42.
#[test]
#[timeout(30_000)]
fn test_auflia_assumption_only_store_row1_unsat_6736() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (push 1)
        (assert (distinct 42 99))
        (check-sat-assuming (
            (= b (store a 0 99))
            (= (select b 0) 42)
        ))
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "expected unsat: ROW1 on assumption-only store; got {outputs:?}"
    );
}

/// SAT control: same pattern but the read-back value matches the stored value.
#[test]
#[timeout(30_000)]
fn test_auflia_assumption_only_store_row1_sat_6736() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (push 1)
        (assert (>= (select a 0) 0))
        (check-sat-assuming (
            (= b (store a 0 99))
            (= (select b 0) 99)
        ))
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs.iter().any(|o| o == "sat"),
        "expected sat: ROW1 stores 99, reads 99; got {outputs:?}"
    );
}

/// SAT regression for #6731 on the assumption path: combined AUFLIA must not
/// degrade to unknown while temporary preprocessed assertions are installed.
#[test]
#[timeout(30_000)]
fn test_auflia_assumption_store_select_sat_keeps_reason_unknown_clear_6731() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (= (store a i 42) b))
        (check-sat-assuming ((= (select b i) 42)))
    "#;

    let commands = parse(smt).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
    assert!(
        exec.unknown_reason().is_none(),
        "AUFLIA assumption-side SAT must not leave reason-unknown set: {:?}",
        exec.unknown_reason()
    );
}

/// ROW2 via assumption: store at index 0, read at index 1.
/// select(store(a, 0, v), 1) = select(a, 1) by ROW2 when 0 ≠ 1.
/// Combined with assertion select(a, 1) = 7 and assumption select(b, 1) ≠ 7,
/// this should be UNSAT.
#[test]
#[timeout(30_000)]
fn test_auflia_assumption_only_store_row2_unsat_6736() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (push 1)
        (assert (= (select a 1) 7))
        (check-sat-assuming (
            (= b (store a 0 99))
            (not (= (select b 1) 7))
        ))
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "expected unsat: ROW2 on assumption-only store at different index; got {outputs:?}"
    );
}

// === QF_AUFLIRA: assumption-only store with mixed Int/Real ===

/// AUFLIRA variant: assumption-only store with Real-indexed array.
/// store(a, 0, 3.0) read back at index 0 must return 3.0 by ROW1.
#[test]
#[timeout(30_000)]
fn test_auflira_assumption_only_store_row1_unsat_6736() {
    let smt = r#"
        (set-logic QF_AUFLIRA)
        (declare-fun a () (Array Int Real))
        (declare-fun b () (Array Int Real))
        (push 1)
        (assert (distinct 3.0 5.0))
        (check-sat-assuming (
            (= b (store a 0 3.0))
            (= (select b 0) 5.0)
        ))
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "expected unsat: AUFLIRA ROW1 on assumption-only store; got {outputs:?}"
    );
}

// === QF_AX: assumption-only store (non-incremental path, control) ===

/// QF_AX uses the assumption_solving.rs path which does not have the
/// incremental scope filter. This test confirms that path is already correct.
#[test]
#[timeout(30_000)]
fn test_qf_ax_assumption_only_store_row1_unsat_6736() {
    let smt = r#"
        (set-logic QF_AX)
        (declare-sort Idx 0)
        (declare-sort Elm 0)
        (declare-fun a () (Array Idx Elm))
        (declare-fun b () (Array Idx Elm))
        (declare-fun i () Idx)
        (declare-fun v1 () Elm)
        (declare-fun v2 () Elm)
        (push 1)
        (assert (distinct v1 v2))
        (check-sat-assuming (
            (= b (store a i v1))
            (= (select b i) v2)
        ))
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "expected unsat: QF_AX ROW1 on assumption-only store; got {outputs:?}"
    );
}

// === QF_ABV: assumption-only store with bitvector arrays ===

/// QF_ABV variant: assumption-only store on a (_ BitVec 8) array.
/// store(a, #x00, #xFF) read back at index #x00 must return #xFF by ROW1.
#[test]
#[timeout(30_000)]
fn test_qf_abv_assumption_only_store_row1_unsat_6736() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
        (push 1)
        (assert (distinct #xFF #x00))
        (check-sat-assuming (
            (= b (store a #x00 #xFF))
            (= (select b #x00) #x00)
        ))
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs.iter().any(|o| o == "unsat"),
        "expected unsat: QF_ABV ROW1 on assumption-only store; got {outputs:?}"
    );
}

// === Multi check-sat-assuming: axioms regenerated per call ===

/// Two consecutive check-sat-assuming calls with different assumption stores.
/// Each call must independently generate axioms for its assumption terms.
#[test]
#[timeout(30_000)]
fn test_auflia_multi_assume_different_stores_6736() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun c () (Array Int Int))
        (push 1)
        (assert (= (select a 0) 10))
        (check-sat-assuming (
            (= b (store a 0 20))
            (= (select b 0) 10)
        ))
        (check-sat-assuming (
            (= c (store a 0 30))
            (= (select c 0) 30)
        ))
        (pop 1)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs.iter().filter(|o| *o == "unsat").count(),
        1,
        "first call unsat (ROW1: 20≠10), second sat (ROW1: 30=30); got {outputs:?}"
    );
    assert_eq!(
        outputs.iter().filter(|o| *o == "sat").count(),
        1,
        "first call unsat, second sat; got {outputs:?}"
    );
}
