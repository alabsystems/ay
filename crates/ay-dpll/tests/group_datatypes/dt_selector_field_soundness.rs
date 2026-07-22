// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Soundness regression tests for the datatype-field oracle.
//!
//! These guard a family of wrong-SAT bugs where a String / BV / arithmetic /
//! recognizer predicate is taken over a value reached through a datatype
//! SELECTOR (or a `select`-produced datatype value) whose field the candidate
//! model leaves unconstrained. Previously AY accepted a self-contradicting model
//! (e.g. reporting `(s d) = ""` while claiming `(str.++ (s d) "x") = "yz"`). The
//! `DtFieldOracle` re-evaluates such assertions against the model's materialized
//! field values and degrades SAT -> Unknown when the model genuinely falsifies
//! them. All of these are truly UNSAT, so the only sound answers are `unsat` or
//! `unknown` — NEVER `sat`.

use ntest::timeout;

fn assert_not_sat(smt: &str, label: &str) {
    let result = crate::common::solve(smt);
    let line = crate::common::sat_result(&result).unwrap_or("<none>");
    assert!(
        line == "unsat" || line == "unknown",
        "{label}: expected unsat/unknown (truly UNSAT), got `{line}`\n{smt}"
    );
}

fn assert_sat_or_unknown(smt: &str, label: &str) {
    let result = crate::common::solve(smt);
    let line = crate::common::sat_result(&result).unwrap_or("<none>");
    assert!(
        line == "sat" || line == "unknown",
        "{label}: expected sat/unknown (genuinely SAT, must NOT be broken to unsat), got `{line}`\n{smt}"
    );
}

/// BUG A: a String-typed selector value disconnected from the string theory.
/// `"" ++ "x" = "x" != "yz"`, so this is UNSAT; the model's defaulted `(s d)=""`
/// falsifies the assertion.
#[test]
#[timeout(60_000)]
fn dt_string_selector_concat_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (= (str.++ (s d) "x") "yz"))
        (check-sat)
        "#,
        "bugA: str.++ over string selector",
    );
}

/// BUG A (variant): str.< is irreflexive, so `(str.< (s d) (s d))` is UNSAT.
#[test]
#[timeout(60_000)]
fn dt_string_selector_lt_irreflexive_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (str.< (s d) (s d)))
        (check-sat)
        "#,
        "bugA2: irreflexive str.< over string selector",
    );
}

/// BUG B: a sole-constructor recognizer over a `select`-produced datatype value.
/// `c2` is the only constructor, so `(_ is c2)` is a tautology and its negation
/// is UNSAT.
#[test]
#[timeout(60_000)]
fn dt_select_sole_constructor_recognizer_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype D1 ((c2 (sel4 Int))))
        (declare-const v6 (Array Int D1))
        (assert (not ((_ is c2) (select v6 0))))
        (check-sat)
        "#,
        "bugB: sole-constructor recognizer over select",
    );
}

/// BUG C: a BV field not propagated through a deep (2-layer) selector chain.
/// `v0 = (tnode (ileaf #x4))` fixes `(ib (tm v0)) = #x4`, so `!= #x4` is UNSAT.
#[test]
#[timeout(60_000)]
fn dt_nested_selector_chain_bv_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatypes ((Inner 0)) (((ileaf (ib (_ BitVec 4))))))
        (declare-datatypes ((Top 0)) (((tnode (tm Inner)))))
        (declare-const v0 Top)
        (assert (= v0 (tnode (ileaf #x4))))
        (assert (not (= (ib (tm v0)) #x4)))
        (check-sat)
        "#,
        "bugC: nested selector chain BV field",
    );
}

/// BUG C (variant): a 4-bit field is always <= #xf, so `(bvugt (mb m) #xf)` is
/// UNSAT.
#[test]
#[timeout(60_000)]
fn dt_mixed_field_bv_range_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatypes ((Mid 0)) (((mkMid (mi1 Int) (mb (_ BitVec 4))))))
        (declare-const m Mid)
        (assert (and (>= (mi1 m) 0) (bvugt (mb m) #xf)))
        (check-sat)
        "#,
        "bugC2: BV4 field out of range",
    );
}

/// BUG D: `str.prefixof "ab" (s d)` requires `|(s d)| >= 2`, but `(str.len (s d)) = 0`
/// forces it empty. UNSAT; the materialized re-eval over the printed `(s d)=""`
/// catches it through the FULL string evaluator (the prior op-by-op materializer
/// missed predicates like prefixof/suffixof/contains over selectors).
#[test]
#[timeout(60_000)]
fn dt_string_selector_prefixof_len_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (str.prefixof "ab" (s d)))
        (assert (= (str.len (s d)) 0))
        (check-sat)
        "#,
        "bugD: prefixof over string selector vs len 0",
    );
}

/// BUG E: `(str.contains (s d) (s d2))` with `(s d) = ""` and `(s d2) != ""`:
/// the empty string cannot contain a nonempty one. UNSAT.
#[test]
#[timeout(60_000)]
fn dt_string_selector_contains_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (declare-const d2 P)
        (assert (str.contains (s d) (s d2)))
        (assert (= (s d) ""))
        (assert (not (= (s d2) "")))
        (check-sat)
        "#,
        "bugE: contains over string selectors",
    );
}

/// BUG F: `(str.suffixof "z" (s d))` with `(s d) = "a"`: "a" does not end with "z".
/// UNSAT.
#[test]
#[timeout(60_000)]
fn dt_string_selector_suffixof_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (str.suffixof "z" (s d)))
        (assert (= (s d) "a"))
        (check-sat)
        "#,
        "bugF: suffixof over string selector",
    );
}

/// BUG G: a plain string variable contradiction that includes a selector term:
/// `(str.++ u0 "b" (s d)) = u0` is length-impossible for any `u0`. The printed
/// model defaults the unconstrained `u0` to "" and `(s d)` to "", which falsifies
/// the equality. UNSAT.
#[test]
#[timeout(60_000)]
fn dt_string_selector_concat_var_len_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (declare-const u0 String)
        (assert (= (str.++ u0 "b" (s d)) u0))
        (check-sat)
        "#,
        "bugG: concat length contradiction with selector + plain var",
    );
}

/// BUG H: `str.<=` over a selector — `(str.<= "b" (s d))` with `(s d) = "a"` is
/// false because "b" > "a". UNSAT.
#[test]
#[timeout(60_000)]
fn dt_string_selector_le_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (str.<= "b" (s d)))
        (assert (= (s d) "a"))
        (check-sat)
        "#,
        "bugH: str.<= over string selector",
    );
}

/// BUG I: `str.substr` over a selector — `(str.substr (s d) 0 1)` with `(s d) = ""`
/// yields "", so `= "a"` is false. UNSAT. Exercises the full evaluator's substr
/// path (never covered by the old op-by-op materializer).
#[test]
#[timeout(60_000)]
fn dt_string_selector_substr_unsat() {
    assert_not_sat(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (= (s d) ""))
        (assert (= (str.substr (s d) 0 1) "a"))
        (check-sat)
        "#,
        "bugI: substr over string selector",
    );
}

// ===== Genuine-SAT preservation: these must NOT be broken to unsat. =====

/// Genuine SAT: `(s d) = "a"` witnesses `(str.++ (s d) "x") = "ax"`. AY may
/// report sat or (acceptably) unknown, but never unsat.
#[test]
#[timeout(60_000)]
fn dt_string_selector_concat_genuine_sat() {
    assert_sat_or_unknown(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (= (str.++ (s d) "x") "ax"))
        (check-sat)
        "#,
        "genA: satisfiable str.++ over string selector",
    );
}

/// Genuine SAT: a 4-bit field can be < #xf.
#[test]
#[timeout(60_000)]
fn dt_mixed_field_bv_range_genuine_sat() {
    assert_sat_or_unknown(
        r#"
        (set-logic ALL)
        (declare-datatypes ((Mid 0)) (((mkMid (mi1 Int) (mb (_ BitVec 4))))))
        (declare-const m Mid)
        (assert (bvult (mb m) #xf))
        (check-sat)
        "#,
        "genC: satisfiable BV4 field",
    );
}

/// Genuine SAT: the nested BV chain is consistent with `(ib (tm v0)) = #x4`.
#[test]
#[timeout(60_000)]
fn dt_nested_selector_chain_genuine_sat() {
    assert_sat_or_unknown(
        r#"
        (set-logic ALL)
        (declare-datatypes ((Inner 0)) (((ileaf (ib (_ BitVec 4))))))
        (declare-datatypes ((Top 0)) (((tnode (tm Inner)))))
        (declare-const v0 Top)
        (assert (= v0 (tnode (ileaf #x4))))
        (assert (= (ib (tm v0)) #x4))
        (check-sat)
        "#,
        "genD: consistent nested BV chain",
    );
}

/// Genuine SAT: an Int selector value pinned by an asserted equality must not be
/// over-demoted (the field IS constrained, so re-eval reads the real value).
#[test]
#[timeout(60_000)]
fn dt_int_selector_constrained_genuine_sat() {
    assert_sat_or_unknown(
        r#"
        (set-logic ALL)
        (declare-datatype P ((mk (s String) (n Int))))
        (declare-const d P)
        (assert (= (n d) 7))
        (check-sat)
        "#,
        "genG: constrained int selector stays sat",
    );
}
