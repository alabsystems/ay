// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! SMT-LIB 2.6 `(match ...)` desugaring soundness (#match-soundness, Part 2).
//!
//! `match` is desugared in the elaborator to nested `ite` guarded by datatype
//! testers, with each constructor-pattern field binder bound to the
//! corresponding selector applied to the scrutinee. Before this support existed
//! a `(match ...)` failed to parse, the offending `assert` was silently dropped,
//! and `check-sat` answered on the incomplete remainder — a wrong `sat` on a
//! truly-`unsat` problem. These cases lock in the desugaring (all pattern kinds,
//! nested, monomorphic + parametric) against the executor.

use ntest::timeout;

/// The canonical wrong-direction repro: `a = (cns 5 nl)` and the head of `a`
/// asserted to be 6. True answer UNSAT; before the fix AY answered `sat`.
#[test]
#[timeout(60_000)]
fn test_match_head_mismatch_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (declare-const a L)
        (assert (= a (cns 5 nl)))
        (assert (= (match a ((nl 0) ((cns h t) h))) 6))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Same shape, head asserted to its true value 5: SAT.
#[test]
#[timeout(60_000)]
fn test_match_head_equals_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (declare-const a L)
        (assert (= a (cns 5 nl)))
        (assert (= (match a ((nl 0) ((cns h t) h))) 5))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// Nullary-constructor case selected: `match nl` takes the `nl` arm.
#[test]
#[timeout(60_000)]
fn test_match_nullary_branch_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (declare-const a L)
        (assert (= a nl))
        (assert (= (match a ((nl 0) ((cns h t) h))) 1))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Wildcard `_` default case: `a = nl` falls through to the default value 99.
#[test]
#[timeout(60_000)]
fn test_match_wildcard_default_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (declare-const a L)
        (assert (= a nl))
        (assert (= (match a (((cns h t) h) (_ 99))) 99))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// Variable (non-constructor symbol) default binds the WHOLE scrutinee.
#[test]
#[timeout(60_000)]
fn test_match_variable_default_binds_scrutinee_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (declare-const a L)
        (assert (= a (cns 7 nl)))
        (assert (= (match a ((nl nl) (x x))) a))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// Nested match: project the head of the tail of `a`.
#[test]
#[timeout(60_000)]
fn test_match_nested_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (declare-const a L)
        (assert (= a (cns 1 (cns 2 nl))))
        (assert (= (match a ((nl 0) ((cns h t) (match t ((nl h) ((cns h2 t2) h2)))))) 2))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_match_nested_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (declare-const a L)
        (assert (= a (cns 1 (cns 2 nl))))
        (assert (= (match a ((nl 0) ((cns h t) (match t ((nl h) ((cns h2 t2) h2)))))) 9))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Parametric datatype: match resolves the per-instance constructor/selector.
#[test]
#[timeout(60_000)]
fn test_match_parametric_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 1)) ((par (T) ((lnil) (lcons (lhd T) (ltl (Lst T)))))))
        (declare-const a (Lst Int))
        (assert (= a (lcons 5 (as lnil (Lst Int)))))
        (assert (= (match a ((lnil 0) ((lcons h t) h))) 6))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

#[test]
#[timeout(60_000)]
fn test_match_parametric_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 1)) ((par (T) ((lnil) (lcons (lhd T) (ltl (Lst T)))))))
        (declare-const a (Lst Int))
        (assert (= a (lcons 5 (as lnil (Lst Int)))))
        (assert (= (match a ((lnil 0) ((lcons h t) h))) 5))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// `match` on a literal constructor folds directly to the stored field.
#[test]
#[timeout(60_000)]
fn test_match_on_literal_constructor_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
        (assert (= (match (cns 3 nl) ((nl 0) ((cns h t) h))) 4))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}
