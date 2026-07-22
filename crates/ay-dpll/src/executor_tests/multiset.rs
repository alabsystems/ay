// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end executor tests for the native multiset (bag) theory.
//!
//! These drive full SMT-LIB through `parse` + `Executor::execute_all`, so they
//! exercise the whole wired path: `(Multiset T)` sort + `multiset.*`
//! elaboration → logic routing (`QF_MSLIA`) → `UfMultisetLiaSolver` → verdict.
//! They assert that previously-MBQI-needing count facts now decide, and that
//! out-of-fragment obligations fail closed to `unknown` (never a guessed
//! sat/unsat).

use crate::Executor;
use ay_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn verdict(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

// ---------------------------------------------------------------------------
// In-fragment count facts decide without MBQI.
// ---------------------------------------------------------------------------

/// `count(empty, e) = 0`: asserting `count(e, empty) = 2` is UNSAT (const-0
/// array read-through, array-decided).
#[test]
fn count_empty_is_zero() {
    let smt = r#"
(set-logic QF_MSLIA)
(assert (= (multiset.count 3 (as multiset.empty (Multiset Int))) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `count(insert(empty, e), e) = 1`: asserting it is NOT 1 is UNSAT. This is the
/// previously-MBQI-needing multiset fact — the store read-through plus the
/// const-0 base decide it with no quantifier instantiation.
#[test]
fn count_of_insert_into_empty_is_one() {
    let smt = r#"
(set-logic QF_MSLIA)
(assert (not (= (multiset.count 4 (multiset.insert 4 (as multiset.empty (Multiset Int)))) 1)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `count(insert(m, e), e) = count(m, e) + 1`: asserting the contrary is UNSAT.
#[test]
fn count_of_insert_is_predecessor_plus_one() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset Int))
(assert (not (= (multiset.count 7 (multiset.insert 7 m))
                (+ (multiset.count 7 m) 1))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `count(m, e) >= 0` is injected for every count read: asserting `count = -1`
/// is UNSAT (multiplicities are never negative).
#[test]
fn count_is_nonnegative() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset Int))
(assert (= (multiset.count 2 m) (- 1)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `count(remove(m, e), e) = max(count(m, e) - 1, 0)` clamps at 0: removing from
/// an empty multiset keeps the count at 0, so asserting it is 1 is UNSAT.
#[test]
fn count_of_remove_from_empty_clamps_at_zero() {
    let smt = r#"
(set-logic QF_MSLIA)
(assert (= (multiset.count 1 (multiset.remove 1 (as multiset.empty (Multiset Int)))) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// A consistent count constraint is SAT.
#[test]
fn count_positive_is_sat() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset Int))
(assert (= (multiset.count 5 m) 3))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

// ---------------------------------------------------------------------------
// Subset reasoning.
// ---------------------------------------------------------------------------

/// `m subset m` is valid: its negation is UNSAT (reflexivity, no MBQI).
#[test]
fn subset_self_negation_is_unsat() {
    let smt = r#"
(set-logic QF_MULTISET)
(declare-const m (Multiset Int))
(assert (not (multiset.subset m m)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `count(m, e) > count(n, e)` for a present element, yet `subset(m, n)`
/// asserted — UNSAT via one ground witness count obligation.
#[test]
fn subset_refuted_by_count_witness_is_unsat() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset Int))
(declare-const n (Multiset Int))
(assert (multiset.subset m n))
(assert (= (multiset.count 9 m) 2))
(assert (= (multiset.count 9 n) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `subset(m, n)` with `count(m, e) <= count(n, e)` over the present witness is
/// consistent — SAT.
#[test]
fn subset_consistent_with_count_witness_is_sat() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset Int))
(declare-const n (Multiset Int))
(assert (multiset.subset m n))
(assert (= (multiset.count 9 m) 1))
(assert (= (multiset.count 9 n) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// Auto-detected logic (no explicit set-logic) routes multiset ops to the
/// multiset solver when a surviving `multiset.*` symbol is present. Here
/// `multiset.subset` survives elaboration (count/insert/remove/empty reduce to
/// array ops), triggering `has_multiset_ops` → QF_MSLIA routing, so the
/// injected `count >= 0` refutes the count-witness conflict.
#[test]
fn auto_detected_logic_routes_to_multiset_solver() {
    let smt = r#"
(declare-const m (Multiset Int))
(declare-const n (Multiset Int))
(assert (multiset.subset m n))
(assert (= (multiset.count 9 m) 2))
(assert (= (multiset.count 9 n) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// Multiset ops over BitVector-sorted elements route to the native theory.
//
// A multiset over BV elements is carried as `Array(BV32 -> Int)`. The carrier
// makes `has_arrays`, `has_int`, and `has_bv` all true; before the multiset-op
// precedence these auto-detect to QF_ABV/QF_AUFBV and the count/subset symbols
// degrade to opaque UF. They must instead route to QF_MSLIA and decide.
// ---------------------------------------------------------------------------

/// `count(m, e) >= 0` over BV(32)-element multisets: asserting `count = -1` is
/// UNSAT via the injected non-negativity. The surviving `multiset.subset`
/// reflexive atom triggers QF_MSLIA routing over the BV carrier; the count read
/// is `select` over `Array(BV -> Int)`, decided by the array solver and bridged
/// to LIA with `count >= 0`.
#[test]
fn bv_element_count_nonnegative() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset (_ BitVec 32)))
(assert (= (multiset.count (_ bv7 32) m) (- 1)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `m subset m` over BV(32)-element multisets is valid: its negation is UNSAT.
/// No explicit set-logic — exercises the auto-detection path (`infer_logic`)
/// over the BV carrier, which must route to QF_MSLIA, not QF_ABV.
#[test]
fn bv_element_subset_self_negation_is_unsat() {
    let smt = r#"
(declare-const m (Multiset (_ BitVec 32)))
(assert (not (multiset.subset m m)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// Fail-closed: out-of-fragment obligations return unknown, never guessed.
// ---------------------------------------------------------------------------

/// `multiset.union` (count = max) has no sound ground count semantics yet →
/// unknown.
#[test]
fn union_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset Int))
(declare-const n (Multiset Int))
(assert (= (multiset.count 1 (multiset.union m n)) 3))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

/// `multiset.map` (polymorphic image) → unknown (fail-closed).
#[test]
fn map_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_MSLIA)
(declare-const m (Multiset Int))
(declare-const f (Array Int Int))
(assert (= (multiset.count 0 (multiset.map f m)) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}
