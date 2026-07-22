// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! ABV array axiom soundness tests for incremental (push/pop) mode.
//!
//! These tests verify that QF_ABV and QF_AUFBV correctly handle array axioms
//! (ROW1, ROW2, extensionality) when operating in incremental mode via push/pop.
//!
//! Background (#6727): The non-incremental BV path generates array axioms eagerly
//! by scanning all TermStore terms. In incremental mode, this scans dead terms from
//! popped scopes, generating phantom axioms. The fix must either:
//! (a) Generate axioms from scoped assertions only, or
//! (b) Use a DPLL(T)-style array theory solver in the incremental BV path.
//!
//! Simply disabling array axioms (array_axioms: false) without providing an
//! alternative is UNSOUND — formulas requiring ROW2 reasoning return false SAT.
//!
//! Part of #6727.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Run a raw SMT-LIB script and extract check-sat results.
fn run_smt(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT:\n{smt}"));
    let mut exec = Executor::new();
    let output = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT:\n{smt}"))
        .join("\n");
    output
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .map(ToOwned::to_owned)
        .collect()
}

/// QF_ABV ROW1 axiom soundness in incremental mode.
///
/// ROW1: `select(store(a, i, v), i) = v`.
/// Without array axiom generation, the BV solver treats `select(store(a,i,v),i)`
/// and `v` as unrelated terms and could return SAT (false positive) instead of UNSAT.
///
/// Note: ROW1 may be handled directly by the BV bitblaster for the direct-index
/// case, so this test may pass even without explicit array axiom generation.
/// The ROW2 test below is the critical one.
#[test]
#[timeout(10_000)]
fn abv_row1_incremental_soundness() {
    let result = run_smt(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= i #x00))
        (check-sat)
        (push 1)
        ; ROW1: select(store(a, i, v), i) MUST equal v
        ; Negating this should be UNSAT
        (assert (not (= (select (store a i v) i) v)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat", "unsat", "sat"]);
}

/// QF_ABV ROW2 axiom soundness in incremental mode (CRITICAL).
///
/// ROW2: when `i != j`, `select(store(a, i, v), j) = select(a, j)`.
/// This axiom cannot be handled by simple bitblasting — it requires explicit
/// array axiom generation or a theory solver.
///
/// Without array axioms in the incremental BV path, this returns SAT (false
/// positive) because `select(store(a, i, v), j)` and `select(a, j)` are
/// treated as independent uninterpreted BV terms.
#[test]
#[timeout(10_000)]
fn abv_row2_incremental_soundness() {
    let result = run_smt(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= i j)))
        (check-sat)
        (push 1)
        ; ROW2: i != j implies select(store(a, i, v), j) = select(a, j)
        ; Negating this should be UNSAT
        (assert (not (= (select (store a i v) j) (select a j))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat", "unsat", "sat"]);
}

/// QF_ABV ROW2 without push/pop (non-incremental baseline).
///
/// Verifies that ROW2 works correctly in the non-incremental path.
/// This serves as a baseline: if this passes but the incremental version
/// fails, the incremental path is missing array axiom generation.
#[test]
#[timeout(10_000)]
fn abv_row2_non_incremental_baseline() {
    let result = run_smt(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= i j)))
        ; ROW2: i != j implies select(store(a, i, v), j) = select(a, j)
        (assert (not (= (select (store a i v) j) (select a j))))
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["unsat"]);
}

/// QF_AUFBV ROW2 axiom soundness in incremental mode.
///
/// Same as the ABV ROW2 test but for the AUFBV logic which also uses the
/// BV incremental path with array axioms.
#[test]
#[timeout(10_000)]
fn aufbv_row2_incremental_soundness() {
    let result = run_smt(
        r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= i j)))
        (check-sat)
        (push 1)
        ; ROW2 + UF: i != j, so select(store(a,i,v),j) = select(a,j)
        ; and f applied to both sides should also be equal
        (assert (not (= (select (store a i v) j) (select a j))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat", "unsat", "sat"]);
}

/// QF_UFBV congruence axiom soundness in incremental mode.
///
/// Verifies that UF congruence axioms (f(x) = f(y) when x = y) work
/// correctly in the incremental BV path with push/pop scoping.
#[test]
#[timeout(10_000)]
fn ufbv_congruence_incremental_soundness() {
    let result = run_smt(
        r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (check-sat)
        (push 1)
        ; Congruence: x = y implies f(x) = f(y)
        ; Negating this should be UNSAT
        (assert (distinct (f x) (f y)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat", "unsat", "sat"]);
}

/// QF_UFBV congruence with complex BV args in incremental mode.
///
/// Verifies congruence axioms fire correctly when UF arguments are
/// complex BV expressions (bvadd, nested ops) in the incremental path.
#[test]
#[timeout(10_000)]
fn ufbv_complex_arg_congruence_incremental_soundness() {
    let result = run_smt(
        r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (check-sat)
        (push 1)
        ; x = y implies bvadd(x, 1) = bvadd(y, 1) implies f(bvadd(x,1)) = f(bvadd(y,1))
        (assert (distinct (f (bvadd x #x01)) (f (bvadd y #x01))))
        (check-sat)
        (pop 1)
        ; After pop, the distinct assertion is gone; should be SAT again
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat", "unsat", "sat"]);
}

/// QF_UFBV Bool-return UF congruence in incremental mode.
///
/// This exercises the non-BV-return congruence path used for predicate-like
/// UFs where the result is represented by Tseitin variables instead of BV bits.
#[test]
#[timeout(10_000)]
fn ufbv_bool_return_congruence_incremental_soundness() {
    let result = run_smt(
        r#"
        (set-logic QF_UFBV)
        (declare-fun p ((_ BitVec 8)) Bool)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (check-sat)
        (push 1)
        ; x = y implies p(x) = p(y); xor must therefore be false.
        (assert (xor (p x) (p y)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
    );
    assert_eq!(result, vec!["sat", "unsat", "sat"]);
}
