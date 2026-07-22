// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Selector axiom variable indirection and chained/nested selector tests for QF_DT.
//! Split from qf_dt_integration.rs — Part of #7229.

use ntest::timeout;

// ========================== Selector Axiom Variable Indirection Tests ==========================
// Fixed: #1740 - Selector axiom not propagated through variable equality
//
// When `p = C(a_1, ..., a_n)` is asserted (where p is a variable, not a constructor),
// selector axioms `sel_i(p) = a_i` must be generated for soundness.

/// UNSAT: Selector axiom through variable indirection - (fst p) must equal x when p = (mk-pair x y).
///
/// Regression test for #1740: selector axiom not propagated through variable equality.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_through_variable() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun p () Pair)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= p (mk-pair x y)))
        (assert (not (= (fst p) x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Selector axiom fst(p) = x must hold when p = (mk-pair x y)"
    );
}

/// UNSAT: Selector axiom through variable indirection - (snd p) must equal y.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_snd_through_variable() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun p () Pair)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= p (mk-pair x y)))
        (assert (not (= (snd p) y)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Selector axiom snd(p) = y must hold when p = (mk-pair x y)"
    );
}

/// UNSAT: Selector axiom through variable indirection - (value o) must equal x when o = (Some x).
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_option_through_variable() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-fun o () Option)
        (declare-fun x () Int)
        (assert (= o (Some x)))
        (assert (not (= (value o) x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Selector axiom value(o) = x must hold when o = (Some x)"
    );
}

/// UNSAT: nested selectors must resolve correctly when selector names are reused
/// across datatypes.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_overloaded_nested_selectors() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Inner 0) (Outer 0))
            (((Inner_mk (fld_0 Int) (fld_1 Bool)))
             ((Outer_mk (fld_0 Inner) (fld_1 Int)))))
        (assert (not (= (fld_0 (fld_0 (Outer_mk (Inner_mk 42 true) 7))) 42)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Nested overloaded selectors should project through both datatype layers"
    );
}

/// SAT: Selector axiom through variable indirection - the constraint is satisfiable.
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_selector_through_variable_sanity() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun p () Pair)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= p (mk-pair x y)))
        (assert (= (fst p) x))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Selector axiom satisfied - should be sat"
    );
}

/// UNSAT: Selector axiom through variable indirection - reversed equality (mk-pair x y) = p.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_through_variable_reversed_eq() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun p () Pair)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (mk-pair x y) p))
        (assert (not (= (fst p) x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Selector axiom must work with reversed equality"
    );
}

// Fixed: #1741 - Transitive equality selector propagation

/// UNSAT: Selector axiom through transitive variable equality.
///
/// Regression test for soundness bug #1741 (FIXED): p = q and q = C(args) should
/// propagate selector axioms to p.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_through_transitive_equality() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun p () Pair)
        (declare-fun q () Pair)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= p q))
        (assert (= q (mk-pair x y)))
        (assert (not (= (fst p) x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Selector axiom must propagate through transitive equality p = q = C(args)"
    );
}

/// SAT: Selector axioms must NOT be generated for equalities inside disjunctions.
///
/// Regression test for soundness bug found in #1740 self-audit: if the equality
/// `p = C(args)` appears inside a disjunction (not directly asserted), generating
/// `sel_i(p) = args[i]` is unsound because the equality might not hold.
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_selector_axiom_not_for_disjunction() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun p () Pair)
        (declare-fun q () Pair)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        ; This is a disjunction - p = mk-pair(x, y) might NOT be true
        (assert (or (= p (mk-pair x y)) (= q (mk-pair z z))))
        ; If we incorrectly assume p = mk-pair(x, y), this would be UNSAT
        ; But it's actually SAT: choose p != mk-pair(x, y), q = mk-pair(z, z)
        (assert (not (= (fst p) x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Selector axiom should NOT be generated for equality inside disjunction"
    );
}

/// UNSAT: Selector congruence through variable equality (#1737).
///
/// Regression test for soundness bug: `x = C(args)` implies `sel_i(x) = args[i]`.
/// Z3 returns UNSAT. See the development design notes
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_selector_congruence_variable_equality() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))
        (declare-fun x () Pair)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (= x (mk-pair a b)))
        (assert (distinct (fst x) a))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Regression test for #1737: selector congruence through variable equality.
    // Fixed by equality→tester axiom (E) in executor.rs.
    assert_eq!(
        result.trim(),
        "unsat",
        "#1737: x = C(a,b) should imply fst(x) = a"
    );
}

/// UNSAT: Tester exhaustiveness (#1738).
///
/// Regression test for soundness bug: x must satisfy at least one tester.
/// Z3 returns UNSAT. See the development design notes
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_tester_exhaustiveness() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-fun x () Option)
        (assert (not (is-None x)))
        (assert (not (is-Some x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Regression test for #1738: exhaustiveness axiom.
    // Fixed by exhaustiveness axiom (D) in executor.rs.
    assert_eq!(
        result.trim(),
        "unsat",
        "#1738: x must be None or Some, cannot be neither"
    );
}

/// UNSAT: Nullary constructor tester evaluation (#1745).
///
/// For a nullary constructor `C`, `is-C(C)` must be true.
/// This tests recognizer evaluation on nullary constructors specifically.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_nullary_tester_evaluation() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (assert (not (is-None None)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Bug #1745: is-None(None) = true, so not(is-None(None)) should be UNSAT.
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1745: Tester is-None(None) must be true"
    );
}

/// UNSAT: Nullary constructor cross-tester (#1745).
///
/// For a nullary constructor `C`, `is-C'(C)` must be false for other constructors.
/// This tests recognizer evaluation on nullary constructors specifically.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_nullary_cross_tester() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (assert (is-Some None))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Bug #1745: is-Some(None) = false, so asserting it should be UNSAT.
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1745: Tester is-Some(None) must be false"
    );
}

/// SAT: Nullary constructor tester positive case (#1745).
///
/// is-None(None) = true, so this should be satisfiable.
/// This is a sanity test for the nullary recognizer issue.
#[test]
#[timeout(60_000)]
fn test_qf_dt_sat_nullary_tester_positive() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Option ((None) (Some (value Int))))
        (assert (is-None None))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Tester is-None(None) = true should be SAT"
    );
}

// ========================== Chained/Nested Selector Tests ==========================
// Issue: #1739 - Chained selectors not correctly handled
//
// When a selector is applied to a selector application (nested selectors), the
// result may semantically equal a constructor application, but the solver must
// chain the axioms correctly.

/// UNSAT: Chained selectors - value(fst(mk-pair (Some x) 0)) must equal x.
///
/// Regression test for #1739: the selector axiom chain should derive:
/// - fst(mk-pair (Some x) 0) = (Some x)     [outer axiom]
/// - value((Some x)) = x                     [inner axiom]
/// - Therefore value(fst(mk-pair ...)) = x   [composition]
///
/// Z3 returns UNSAT. AY incorrectly returns SAT.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_chained_selector_value_of_fst() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-datatype Pair ((mk-pair (fst Option) (snd Int))))
        (declare-fun x () Int)
        (assert (not (= (value (fst (mk-pair (Some x) 0))) x)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // Bug #1739: Chained selectors should derive the equality transitively.
    // Z3: unsat, AY: sat (INCORRECT)
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1739: Chained selectors value(fst(mk-pair (Some x) 0)) must equal x"
    );
}

/// UNSAT: Nested selector on same datatype - f(f(c(c(base)))) must equal base.
///
/// Simplified test case from commit 7aa6066f self-audit.
/// Two levels of nested selector application on recursive structure.
#[test]
#[timeout(60_000)]
fn test_qf_dt_unsat_nested_selector_resolution() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Wrapper ((base) (c (f Wrapper))))
        (assert (not (= (f (f (c (c base)))) base)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    // f(c(base)) = base by selector axiom
    // f(c(c(base))) = c(base) by selector axiom
    // f(f(c(c(base)))) = f(c(base)) = base
    // So not(f(f(c(c(base)))) = base) is UNSAT.
    assert_eq!(
        result.trim(),
        "unsat",
        "Nested selector f(f(c(c(base)))) must resolve to base"
    );
}
