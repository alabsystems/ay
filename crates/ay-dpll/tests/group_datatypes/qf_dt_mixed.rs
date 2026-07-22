// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! ALL logic DT+Int/Real integration, DT+arithmetic acyclicity,
//! check-sat-assuming + DT, and cross-tester/logic upgrade tests.
//! Split from qf_dt_integration.rs — Part of #7229.

use ntest::timeout;

// ========================== ALL Logic DT Integration Tests ==========================
// Issue: #1749 - ALL logic does not auto-detect DT theory usage
//
// When (set-logic ALL) is used with datatypes, AY currently short-circuits
// ALL+DT to QF_DT, ignoring integer constraints.

/// UNSAT: ALL logic with DT and Int must enforce integer constraints.
///
/// Regression test for #1749: x > 5 AND x < 3 is UNSAT regardless of datatypes.
/// Z3 returns UNSAT. AY incorrectly returns SAT (ignores Int constraints).
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_constraints_enforced() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-const x Int)
        (assert (> x 5))
        (assert (< x 3))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Bug #1749: ALL logic with DT should still enforce integer constraints.
    // Z3: unsat, AY: sat (INCORRECT - ignores integer theory)
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1749: ALL logic must enforce integer constraints even with datatypes"
    );
}

/// SAT: ALL logic with DT and satisfiable Int constraints.
///
/// Sanity check that when Int constraints ARE satisfiable, the result is SAT.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_constraints_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-const x Int)
        (assert (> x 3))
        (assert (< x 10))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "ALL logic with satisfiable Int constraints should be SAT"
    );
}

// ========================== DT+Arithmetic Acyclicity Tests ==========================
// Issue: #1764 - DT acyclicity for DT+arithmetic combined solver paths
//
// When (set-logic ALL) is used with datatypes AND arithmetic (Int or Real),
// AY routes to _DT_AUFLIA / _DT_AUFLRA which must enforce acyclicity.
// Pure QF_DT uses DtSolver's occurs-check (#1733), but combined paths need
// depth function axioms to encode acyclicity into arithmetic constraints.

/// UNSAT: Direct self-cycle x = cons(n, x) under ALL logic with arithmetic.
///
/// Regression test for #1764: the combined DT+arithmetic path must detect cycles.
/// This is the canonical reproducer from the issue description.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_acyclicity_direct_cycle() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const n Int)
        (assert (> n 0))
        (assert (= x (cons n x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Bug #1764: DT+AUFLIA path must enforce acyclicity via depth axioms.
    // x = cons(n, x) implies depth(x) > depth(x), which is impossible.
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1764: Direct cycle x = cons(n, x) with Int constraints must be UNSAT"
    );
}

/// UNSAT: Indirect two-step cycle under ALL logic with arithmetic.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_acyclicity_indirect_cycle_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const y List)
        (declare-const a Int)
        (declare-const b Int)
        (assert (> a 0))
        (assert (> b 0))
        (assert (= x (cons a y)))
        (assert (= y (cons b x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1764: Indirect DT cycles must be UNSAT under DT+AUFLIA"
    );
}

/// SAT: Finite list with Int constraints is satisfiable.
///
/// Sanity check: no cycle, so the formula should be SAT.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_acyclicity_finite_list() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const n Int)
        (assert (> n 0))
        (assert (= x (cons n nil)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Finite list with Int constraints should be SAT"
    );
}

/// Direct self-cycle with Real arithmetic (AUFLRA path).
///
/// Tests that _DT_AUFLRA also enforces acyclicity via depth axioms.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_real_acyclicity_direct_cycle() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Real) (tl List))))
        (declare-const x List)
        (declare-const r Real)
        (assert (> r 0.0))
        (assert (= x (cons r x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1776: DT+AUFLRA must detect direct datatype cycles"
    );
}

// ========================== check-sat-assuming + DT Tests ==========================
// Issue: #1768 - DT+arith check-sat-assuming ignores assumptions in axiom generation
//
// When using check-sat-assuming with DT+arithmetic, equalities in assumptions must
// also be processed for DT selector and depth axioms. Otherwise cycles introduced
// only via assumptions may not be detected.

/// SAT/UNSAT/SAT: check-sat-assuming must preserve SAT on empty assumptions.
///
/// Regression test for #1771: After an UNSAT check-sat-assuming call, a subsequent
/// check-sat-assuming with an empty assumption set must still return SAT (not unknown).
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_check_sat_assuming_empty_after_unsat_is_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const n Int)
        (declare-const a Bool)
        (assert (> n 0))
        (assert (or (not a) (= x (cons n x))))
        (check-sat)
        (check-sat-assuming (a))
        (check-sat-assuming ())
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat\nunsat\nsat",
        "Bug #1771: expected sat/unsat/sat, got: {result}"
    );
}

/// Stress test: #1771 Heisenbug was caused by non-deterministic HashMap
/// iteration order in model equality discovery. A single run might pass by
/// luck; running 20 iterations in-process ensures the stale model equality
/// suppression fix is robust across different hash seeds.
#[test]
#[timeout(120_000)]
fn test_all_logic_dt_int_check_sat_assuming_1771_stress() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const n Int)
        (declare-const a Bool)
        (assert (> n 0))
        (assert (or (not a) (= x (cons n x))))
        (check-sat)
        (check-sat-assuming (a))
        (check-sat-assuming ())
    "#;
    for iteration in 0..20 {
        let result = crate::common::solve(smt);
        assert_eq!(
            result.trim(),
            "sat\nunsat\nsat",
            "Bug #1771 stress: iteration {iteration} got: {result}"
        );
    }
}

/// UNSAT: Direct cycle via assumption only (not asserted).
///
/// Regression test for #1768: DT axiom generation must consider assumptions.
/// The cycle `x = cons(n, x)` is passed as an assumption, not asserted.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_check_sat_assuming_cycle_in_assumption() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const n Int)
        (assert (> n 0))
        (check-sat-assuming ((= x (cons n x))))
    "#;
    let result = crate::common::solve(smt);
    // Bug #1768: The cycle is in the assumption, not the assertions.
    // DT axiom generation must include assumptions to detect this cycle.
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1768: Cycle in assumption must be detected"
    );
}

/// UNSAT: Direct cycle via assumption only (constructor on LHS).
///
/// Regression test for #1768: DT depth axiom generation must handle either equality ordering
/// in assumptions: `(= x (cons n x))` and `(= (cons n x) x)` are equivalent.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_check_sat_assuming_cycle_in_assumption_ctor_lhs() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const n Int)
        (assert (> n 0))
        (check-sat-assuming ((= (cons n x) x)))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1768: Cycle in assumption must be detected (ctor on LHS)"
    );
}

/// UNSAT: Selector axiom via assumption only.
///
/// Regression test for #1768: selector axioms must be generated for assumption equalities.
/// The equality `p = mk-pair(x, y)` is passed as an assumption.
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_check_sat_assuming_selector_in_assumption() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-const p Pair)
        (declare-const x Int)
        (declare-const y Int)
        (check-sat-assuming ((= p (mk-pair x y)) (distinct (fst p) x)))
    "#;
    let result = crate::common::solve(smt);
    // Bug #1768: p = mk-pair(x, y) in assumption should generate selector axiom fst(p) = x.
    // This makes (distinct (fst p) x) unsatisfiable.
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1768: Selector axiom from assumption equality"
    );
}

/// Multi-hop cycle split between assertion and assumption.
///
/// Regression test for #1776: multi-hop cycles spanning assertions/assumptions must be UNSAT.
/// `x = cons(n, y)` in assertion, `y = cons(m, x)` in assumption.
/// Neither is a direct cycle, but together they form one.
///
/// Z3 returns: unsat
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_check_sat_assuming_multi_hop_cycle() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const y List)
        (declare-const n Int)
        (declare-const m Int)
        (assert (= x (cons n y)))
        (check-sat-assuming ((= y (cons m x))))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1776: multi-hop cycles spanning assertions/assumptions must be UNSAT"
    );
}

/// Multiple assumptions with transitive cycle.
///
/// Regression test for #1776: transitive cycles across assumptions must be UNSAT.
/// Neither assumption alone creates a cycle.
///
/// Z3 returns: unsat
#[test]
#[timeout(60_000)]
fn test_all_logic_dt_int_check_sat_assuming_transitive_cycle() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype List ((nil) (cons (hd Int) (tl List))))
        (declare-const x List)
        (declare-const y List)
        (declare-const z List)
        (declare-const n Int)
        (declare-const m Int)
        (declare-const k Int)
        (assert (> n 0))
        (check-sat-assuming ((= x (cons n y)) (= y (cons m z)) (= z (cons k x))))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1776: transitive cycles across assumptions must be UNSAT"
    );
}

/// UNSAT: Cross-tester reasoning for non-nullary constructors (#2766).
///
/// Asserting `is-Err(x)` should imply `¬is-Ok(x)` for a two-constructor datatype.
/// The expected derivation path:
/// 1. Exhaustiveness: (or (is-Ok x) (is-Err x))
/// 2. Constructor axiom: (=> (is-Err x) (= x (Err (sel-err x))))
/// 3. Tester evaluation: is-Ok(Err(...)) = false
/// Combined: is-Err(x) → x = Err(...) → is-Ok(x) = false
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_cross_tester_non_nullary() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype ResultIntInt (
            (Ok (sel-ok Int))
            (Err (sel-err Int))
        ))
        (declare-fun x () ResultIntInt)
        (assert (is-Err x))
        (assert (ite (is-Ok x) (not (= (sel-ok x) 0)) false))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Bug #2766: is-Err(x) should derive ¬is-Ok(x), making the ITE take the false branch → UNSAT.
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2766: is-Err(x) should imply not(is-Ok(x)) [QF_DT]"
    );
}

/// UNSAT: Cross-tester reasoning under ALL logic with DT+Int (#2766).
///
/// Same scenario as test_qf_dt_unsat_cross_tester_non_nullary but using
/// `(set-logic ALL)`, which routes through DT+AUFLIA combined solver.
/// The cross-tester derivation must work in the combined theory path.
#[test]
#[timeout(60_000)]
fn test_all_logic_unsat_cross_tester_non_nullary() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype ResultIntInt (
            (Ok (sel-ok Int))
            (Err (sel-err Int))
        ))
        (declare-fun x () ResultIntInt)
        (assert (is-Err x))
        (assert (not (= (ite (is-Ok x) (sel-ok x) 0) 0)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2766: is-Err(x) should imply not(is-Ok(x)) [ALL logic]"
    );
}

/// UNSAT: Cross-tester reasoning via check-sat-assuming under ALL logic (#2766).
///
/// The check-sat-assuming path has separate axiom generation code (executor.rs:1503-1529)
/// that includes assumptions in the base_set before calling dt_selector_axioms().
/// This test verifies axiom (B') works in that path too.
#[test]
#[timeout(60_000)]
fn test_all_logic_unsat_cross_tester_check_sat_assuming() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype ResultIntInt (
            (Ok (sel-ok Int))
            (Err (sel-err Int))
        ))
        (declare-fun x () ResultIntInt)
        (assert (not (= (ite (is-Ok x) (sel-ok x) 0) 0)))
        (check-sat-assuming ((is-Err x)))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2766: is-Err(x) via assumption should imply not(is-Ok(x)) [ALL logic, check-sat-assuming]"
    );
}

/// UNSAT: DT tester axiom under explicit UFLIA logic (#3223).
///
/// When `(set-logic UFLIA)` is used with datatypes, `dt_selector_axioms()` must still
/// generate tester evaluation axioms. Previously, UFLIA routed to `solve_auf_lia()` which
/// does not generate DT axioms, causing `NOT(is-Some(result))` to be satisfiable when
/// `result = Some(1)` is asserted.
#[test]
#[timeout(60_000)]
fn test_uflia_dt_tester_axiom_propagated() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-datatype OptionInt (
            (None)
            (Some (option_some_value Int))
        ))
        (declare-fun result () OptionInt)
        (declare-fun one () Int)
        (assert (= one 1))
        (assert (= result (Some one)))
        (assert (not (is-Some result)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #3223: is-Some(result) must be true when result = Some(1) under UFLIA logic"
    );
}

/// UNSAT: DT selector axiom under explicit UFLIA logic (#3223).
///
/// When `(set-logic UFLIA)` is used with datatypes, `dt_selector_axioms()` must still
/// generate selector collapse axioms. Previously, `option_some_value(Some(1)) = 1` was
/// not derived because the axiom was never generated.
#[test]
#[timeout(60_000)]
fn test_uflia_dt_selector_axiom_propagated() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-datatype OptionInt (
            (None)
            (Some (option_some_value Int))
        ))
        (declare-fun result () OptionInt)
        (declare-fun one () Int)
        (assert (= one 1))
        (assert (= result (Some one)))
        (assert (not (= (option_some_value result) 1)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #3223: option_some_value(result) must equal 1 when result = Some(1) under UFLIA logic"
    );
}

/// UNSAT: DT tester axiom under explicit QF_AUFLIA logic (#3223).
///
/// Same as the UFLIA test but with QF_AUFLIA — both should be upgraded to DtAuflia
/// when datatypes are declared.
#[test]
#[timeout(60_000)]
fn test_qf_auflia_dt_tester_axiom_propagated() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-datatype OptionInt (
            (None)
            (Some (option_some_value Int))
        ))
        (declare-fun result () OptionInt)
        (assert (= result (Some 1)))
        (assert (not (is-Some result)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #3223: is-Some(result) must be true when result = Some(1) under QF_AUFLIA logic"
    );
}

/// UNSAT: DT axiom under explicit QF_UFLIA with check-sat-assuming (#3223).
///
/// Verifies the fix also applies to the check-sat-assuming path.
#[test]
#[timeout(60_000)]
fn test_qf_uflia_dt_axiom_check_sat_assuming() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-datatype OptionInt (
            (None)
            (Some (option_some_value Int))
        ))
        (declare-fun result () OptionInt)
        (assert (= result (Some 1)))
        (check-sat-assuming ((not (is-Some result))))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #3223: DT axioms in check-sat-assuming under QF_UFLIA"
    );
}
