// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end executor tests for the native finite-map (dictionary) theory.
//!
//! These drive full SMT-LIB through `parse` + `Executor::execute_all`, so they
//! exercise the whole wired path: `(Map K V)` sort + `map.*` elaboration →
//! logic routing (`QF_MAPLIA`) → `UfMapLiaSolver` → verdict. They assert that
//! previously-MBQI-needing get/dom facts now decide natively, and that
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
// In-fragment get/dom facts decide without MBQI (store/const read-through).
// ---------------------------------------------------------------------------

/// `get(insert(m, k, v), k) = v`: asserting it is NOT v is UNSAT. This is the
/// previously-MBQI-needing map fact — the value-carrier store read-through
/// decides it with no quantifier instantiation.
#[test]
fn get_of_insert_at_same_key_is_value() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const v Int)
(assert (not (= (map.get (map.insert m 5 v) 5) v)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `get(insert(m, k, v), k) = v` is consistent — a matching assertion is SAT.
#[test]
fn get_of_insert_at_same_key_is_sat_when_consistent() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const v Int)
(assert (= (map.get (map.insert m 5 v) 5) v))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// `get(insert(m, k1, v), k2) = get(m, k2)` for distinct keys: the read at the
/// untouched key sees the original map (store read-through over a distinct
/// index). Asserting they differ while k1 != k2 is UNSAT.
#[test]
fn get_of_insert_at_other_key_is_unchanged() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const v Int)
(assert (not (= (map.get (map.insert m 1 v) 2) (map.get m 2))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `contains_key(insert(m, k, v), k) = true`: asserting it is false is UNSAT.
/// The domain carrier is `store(dom(m), k, true)`; the read-through decides it.
#[test]
fn contains_key_after_insert_is_true() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const v Int)
(assert (not (map.contains_key (map.insert m 7 v) 7)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `contains_key(insert(empty, k, v), k) = true`: the previously-MBQI-needing
/// fact over the empty map. dom(empty)=const-false, then store(_, k, true)
/// read-through gives true at k. Asserting false is UNSAT.
#[test]
fn contains_key_of_insert_into_empty_is_true() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const v Int)
(assert (not (map.contains_key (map.insert (as map.empty (Map Int Int)) 4 v) 4)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `get(insert(empty, k, v), k) = v`: the value-carrier store read-through over
/// the empty map. Asserting it is NOT v is UNSAT.
#[test]
fn get_of_insert_into_empty_is_value() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const v Int)
(assert (not (= (map.get (map.insert (as map.empty (Map Int Int)) 4 v) 4) v)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `contains_key(empty, k) = false`: the empty map has empty domain. Asserting
/// it contains a key is UNSAT (const-false dom read-through).
#[test]
fn empty_map_contains_no_key() {
    let smt = r#"
(set-logic QF_MAPLIA)
(assert (map.contains_key (as map.empty (Map Int Int)) 3))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `contains_key(remove(m, k), k) = false`: removing a key drops it from the
/// domain (store(dom(m), k, false)). Asserting it is still present is UNSAT.
#[test]
fn contains_key_after_remove_is_false() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(assert (map.contains_key (map.remove m 8) 8))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// A consistent get constraint over a fresh map is SAT.
#[test]
fn get_constraint_is_sat() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(assert (= (map.get m 5) 3))
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
(set-logic QF_MAP)
(declare-const m (Map Int Int))
(assert (not (map.subset m m)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `contains_key(m, k)` but `not contains_key(n, k)`, yet `subset(m, n)`
/// asserted — UNSAT via the per-witness subset↔dom obligation.
#[test]
fn subset_refuted_by_domain_witness_is_unsat() {
    let smt = r#"
(set-logic QF_MAP)
(declare-const m (Map Int Int))
(declare-const n (Map Int Int))
(assert (map.subset m n))
(assert (map.contains_key m 9))
(assert (not (map.contains_key n 9)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `subset(m, n)` with `contains_key(m, k)` and a differing value at a present
/// key — UNSAT via the per-witness subset↔value obligation.
#[test]
fn subset_refuted_by_value_witness_is_unsat() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const n (Map Int Int))
(assert (map.subset m n))
(assert (map.contains_key m 9))
(assert (map.contains_key n 9))
(assert (= (map.get m 9) 1))
(assert (= (map.get n 9) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `subset(m, n)` consistent with the present witnesses (same value, both
/// contain the key) is SAT.
#[test]
fn subset_consistent_with_witness_is_sat() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const n (Map Int Int))
(assert (map.subset m n))
(assert (map.contains_key m 9))
(assert (map.contains_key n 9))
(assert (= (map.get m 9) 5))
(assert (= (map.get n 9) 5))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// Auto-detected logic (no explicit set-logic) routes map ops to the map solver
/// when a surviving `map.*` symbol is present. Here `map.subset`/`map.dom`
/// survive elaboration, triggering `has_map_ops` → QF_MAPLIA routing.
#[test]
fn auto_detected_logic_routes_to_map_solver() {
    let smt = r#"
(declare-const m (Map Int Int))
(declare-const n (Map Int Int))
(assert (map.subset m n))
(assert (map.contains_key m 9))
(assert (not (map.contains_key n 9)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// A separate domain array bridged to `(map.dom m)` by equality, with
/// membership read through `(select (map.dom m) k)`, still fires the native
/// subset↔dom witness obligation. This mirrors the deductive-checks encoding (which
/// tracks its own per-map domain array but reads membership through the
/// `(map.dom m)` projection it bridges to that array), confirming the bridge
/// keeps subset reasoning MBQI-free and sound.
#[test]
fn bridged_dom_subset_witness_is_unsat() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const n (Map Int Int))
(declare-const dm (Array Int Bool))
(declare-const dn (Array Int Bool))
(assert (= (map.dom m) dm))
(assert (= (map.dom n) dn))
(assert (map.subset m n))
(assert (select (map.dom m) 5))
(assert (not (select (map.dom n) 5)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// Map ops over BitVector-sorted keys route to the native theory (QF_MAPLIA).
//
// A map over BV keys is carried as `Array(BV32 -> Int)`. The carrier makes
// `has_arrays`, `has_int`, and `has_bv` all true; before the map-op precedence
// these auto-detect to QF_ABV/QF_AUFBV and map symbols degrade to opaque UF.
// They must instead route to QF_MAPLIA and decide.
// ---------------------------------------------------------------------------

/// `contains_key(insert(m, k, v), k) = true` over BV(32)-keyed maps: asserting
/// false is UNSAT via the domain store read-through. No explicit set-logic —
/// exercises the auto-detection path (`infer_logic`) over the BV carrier, which
/// must route to QF_MAPLIA, not QF_ABV.
#[test]
fn bv_key_contains_after_insert_is_true() {
    let smt = r#"
(declare-const m (Map (_ BitVec 32) Int))
(declare-const v Int)
(assert (not (map.contains_key (map.insert m (_ bv7 32) v) (_ bv7 32))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `m subset m` over BV(32)-keyed maps is valid: its negation is UNSAT.
#[test]
fn bv_key_subset_self_negation_is_unsat() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map (_ BitVec 32) Int))
(assert (not (map.subset m m)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// Fail-closed: out-of-fragment obligations return unknown, never guessed.
// ---------------------------------------------------------------------------

/// `map.values` (image / comprehension) has no sound ground semantics yet →
/// unknown.
#[test]
fn values_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(assert (= (map.get (map.values m) 0) 3))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

/// `map.map_values` (polymorphic image) → unknown (fail-closed).
#[test]
fn map_values_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_MAPLIA)
(declare-const m (Map Int Int))
(declare-const f (Array Int Int))
(assert (= (map.get (map.map_values f m) 0) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}
