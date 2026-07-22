// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4052: contains transitivity inference.
//!
//! Verifies that AY detects contradictions arising from transitive
//! `str.contains` chains of arbitrary length.

use ntest::timeout;

/// Basic 1-hop: contains(x,y) AND contains(y,"abc") AND NOT contains(x,"abc").
#[test]
#[timeout(10_000)]
fn contains_transitivity_1hop_unsat() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x y))
(assert (str.contains y "abc"))
(assert (not (str.contains x "abc")))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "1-hop contains transitivity should be UNSAT"
    );
}

/// 2-hop chain: a⊇b⊇c⊇"xyz", ¬(a⊇"xyz").
#[test]
#[timeout(10_000)]
fn contains_transitivity_2hop_unsat() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(assert (str.contains a b))
(assert (str.contains b c))
(assert (str.contains c "xyz"))
(assert (not (str.contains a "xyz")))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "2-hop contains transitivity should be UNSAT"
    );
}

/// 3-hop chain: a⊇b⊇c⊇d⊇"x", ¬(a⊇"x").
#[test]
#[timeout(10_000)]
fn contains_transitivity_3hop_unsat() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(assert (str.contains a b))
(assert (str.contains b c))
(assert (str.contains c d))
(assert (str.contains d "x"))
(assert (not (str.contains a "x")))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "3-hop contains transitivity should be UNSAT"
    );
}

/// EQC-based chain: contains(a,b), b=c, contains(c,d), contains(d,"t"),
/// ¬contains(a,"t"). The b=c merge should allow the chain to connect.
#[test]
#[timeout(10_000)]
fn contains_transitivity_eqc_chain_unsat() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(assert (= b c))
(assert (str.contains a b))
(assert (str.contains c d))
(assert (str.contains d "test"))
(assert (not (str.contains a "test")))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "EQC-based contains transitivity should be UNSAT"
    );
}

/// SAT case: contains(x,y) AND contains(y,"abc") AND contains(x,"abc").
/// No contradiction — should be SAT.
#[test]
#[timeout(10_000)]
fn contains_transitivity_sat_no_conflict() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains x y))
(assert (str.contains y "abc"))
(assert (str.contains x "abc"))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "consistent contains chain should be SAT"
    );
}

/// Self-containment negation: ¬contains(x,x) is trivially UNSAT.
#[test]
#[timeout(10_000)]
fn self_contains_negation_unsat() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (not (str.contains x x)))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "negated self-containment should be UNSAT"
    );
}

/// Equal-after-substitution inference:
/// x = "a" ++ z, y = "a" ++ ("" ++ z), and not(to_upper(x)=to_upper(y)).
/// The two extf terms should unify after substitution, so this is UNSAT.
#[test]
#[timeout(10_000)]
fn equal_after_substitution_unsat() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x (str.++ "a" z)))
(assert (= y (str.++ "a" (str.++ "" z))))
(assert (not (= (str.to_upper x) (str.to_upper y))))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "equal-after-substitution should force extf equality and UNSAT"
    );
}

/// Extended equality rewriter inference:
/// x = y, str.replace(x,y,z) = "target", and z != "target" is contradictory.
#[test]
#[timeout(10_000)]
fn extended_equality_rewriter_replace_identity_unsat() {
    let output = crate::common::solve(
        r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= x y))
(assert (= (str.replace x y z) "target"))
(assert (not (= z "target")))
(check-sat)
"#,
    );
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "replace identity rewrite should infer z=\"target\" and conflict"
    );
}
