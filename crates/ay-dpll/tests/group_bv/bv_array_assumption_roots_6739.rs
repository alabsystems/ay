// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #6739: BV array axiom generation must see
//! assumption roots in check-sat-assuming.
//!
//! The BV pipeline's `materialize_array_bv_terms` and `generate_array_bv_axioms`
//! previously scanned only `ctx.assertions`. When array select/store terms appear
//! only inside assumption expressions (not in any permanent assertion), the axiom
//! generator missed them, potentially producing wrong-SAT results.
//!
//! These tests use ROW2 axioms (different indices) which require axiom generation
//! — ROW1 with syntactically equal indices is handled by mk_select rewriting and
//! would pass even without the fix.

use ntest::timeout;

/// QF_ABV ROW2 regression: assumption-only select/store with different indices.
///
/// ROW2: (i != j) → select(store(a, i, v), j) = select(a, j)
///
/// The select and store terms appear ONLY in the assumption. Without the fix,
/// `generate_array_bv_axioms` does not see them, so no ROW2 axiom is generated,
/// and the solver may return SAT (wrong).
#[test]
#[timeout(60_000)]
fn test_qf_abv_check_sat_assuming_row2_assumption_only_6739() {
    let smt = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (distinct i j))
        (check-sat-assuming ((not (= (select (store a i v) j) (select a j)))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// QF_AUFBV ROW2 regression: same pattern with UF present.
///
/// The contradiction depends on array axioms (ROW2), not UF congruence.
/// A harmless UF equality keeps the mixed AUFBV route exercised without
/// becoming the reason the formula is UNSAT.
#[test]
#[timeout(60_000)]
fn test_qf_aufbv_check_sat_assuming_row2_assumption_only_6739() {
    let smt = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (distinct i j))
        (assert (= (f i) v))
        (check-sat-assuming ((not (= (select (store a i v) j) (select a j)))))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}
