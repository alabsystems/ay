// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;

#[test]
fn test_propagate_simple_ground_equality() {
    let mut terms = TermStore::new();

    // Create: (= (f 0) 42)
    let zero = terms.mk_int(BigInt::from(0));
    let fortytwo = terms.mk_int(BigInt::from(42));
    let f_0 = terms.mk_app(Symbol::Named("f".to_string()), vec![zero], Sort::Int);
    let eq = terms.mk_eq(f_0, fortytwo);

    // Create: (= x (+ (f 0) 1))
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let f0_plus_1 = terms.mk_add(vec![f_0, one]);
    let eq2 = terms.mk_eq(x, f0_plus_1);

    let mut assertions = vec![eq, eq2];
    let mut pass = PropagateValues::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "pass should modify assertions");

    // The first assertion (= (f 0) 42) is a defining equality — preserved.
    // The second assertion should become (= x (+ 42 1)) = (= x 43)
    // after constant folding by mk_add.
    assert_eq!(
        assertions.len(),
        2,
        "defining equality preserved + rewritten"
    );

    // The defining equality is preserved unchanged
    assert_eq!(assertions[0], eq, "defining equality preserved");

    // Check that the second assertion references the constant 43
    let fortythree = terms.mk_int(BigInt::from(43));
    let expected_eq = terms.mk_eq(x, fortythree);
    assert!(
        assertions.contains(&expected_eq),
        "should contain (= x 43) after value propagation and constant folding"
    );
}

#[test]
fn test_propagate_no_ground_equalities() {
    let mut terms = TermStore::new();

    // Create: (= x y) — no constants, nothing to propagate
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let mut assertions = vec![eq];
    let mut pass = PropagateValues::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(
        !modified,
        "pass should not modify when no ground equalities"
    );
    assert_eq!(assertions.len(), 1);
}

#[test]
fn test_propagate_cascading_through_fixed_point() {
    let mut terms = TermStore::new();

    // Create lookup table: (= (Succ 0) 1), (= (Succ 1) 2)
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let succ_0 = terms.mk_app(Symbol::Named("Succ".to_string()), vec![zero], Sort::Int);
    let succ_1 = terms.mk_app(Symbol::Named("Succ".to_string()), vec![one], Sort::Int);
    let eq1 = terms.mk_eq(succ_0, one);
    let eq2 = terms.mk_eq(succ_1, two);

    // Create: (= x (Succ (Succ 0)))
    // Because the value_map contains both (Succ 0) -> 1 and (Succ 1) -> 2,
    // the bottom-up rewrite resolves the full chain in a single pass:
    //   rewrite(Succ(Succ(0))) -> rewrite inner: Succ(0) -> 1
    //   -> rebuild Succ(1) -> hash-consed to succ_1 -> value_map -> 2
    let x = terms.mk_var("x", Sort::Int);
    let succ_succ_0 = terms.mk_app(Symbol::Named("Succ".to_string()), vec![succ_0], Sort::Int);
    let eq3 = terms.mk_eq(x, succ_succ_0);

    let mut assertions = vec![eq1, eq2, eq3];
    let mut pass = PropagateValues::new();

    // Single iteration resolves the full cascade via bottom-up rewriting
    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);

    // eq1 and eq2 are defining equalities — preserved unchanged.
    // eq3 becomes (= x 2) via cascading substitution.
    assert_eq!(assertions.len(), 3, "defining equalities preserved");
    assert_eq!(assertions[0], eq1, "first defining equality preserved");
    assert_eq!(assertions[1], eq2, "second defining equality preserved");
    let expected_eq = terms.mk_eq(x, two);
    assert_eq!(
        assertions[2],
        expected_eq,
        "should contain (= x 2) after value propagation; got {:?}",
        terms.get(assertions[2])
    );
}

// ---------------------------------------------------------------------------
// Goal mode (`apply_goal`) — z3's `propagate-values` GOAL semantics, used by
// the `(apply propagate-values)` tactic surface. Every expectation below was
// byte-verified against z3 4.15.4 goal output.
// ---------------------------------------------------------------------------

#[test]
fn goal_mode_propagates_asserted_bool_literal_and_folds_the_clause() {
    // (assert p) (assert (or (not p) q))  ->  goal (p q)   [z3-verified]
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not(p);
    let clause = terms.mk_or(vec![not_p, q]);

    let mut fs = vec![p, clause];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    assert!(changed, "goal mode must report the fold");
    assert_eq!(fs, vec![p, q], "clause must fold to q under p ↦ true");
}

#[test]
fn goal_mode_harvests_var_equality_and_drops_implied_atom() {
    // (assert (= x 5)) (assert (< 3 x))  ->  goal ((= x 5))   [z3-verified]
    // (`(> x 3)` parse-normalizes to `(< 3 x)`; `is_ground` would have
    // rejected the Var side in the solve pipeline — goal mode must not.)
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let lt = terms.mk_lt(three, x);

    let mut fs = vec![eq, lt];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    assert!(changed);
    assert_eq!(fs, vec![eq], "(< 3 5) folds to true and is dropped");
}

#[test]
fn goal_mode_conflicting_equalities_collapse_to_false() {
    // (assert (= x 5)) (assert (= x 6))  ->  goal (false)   [z3-verified]
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));
    let eq5 = terms.mk_eq(x, five);
    let eq6 = terms.mk_eq(x, six);

    let mut fs = vec![eq5, eq6];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    assert!(changed);
    assert_eq!(
        fs,
        vec![terms.false_term()],
        "a conflict must collapse the goal to the single literal false"
    );
}

#[test]
fn goal_mode_rewrites_later_definers_with_earlier_ones() {
    // (= (f 0) 1) (= (f (f 0)) 2)  ->  ((= (f 0) 1) (= (f 1) 2))  [z3-verified
    // shape; AY's mk_eq may canonicalize the rebuilt equality's arg order]
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let f_0 = terms.mk_app(Symbol::Named("f".to_string()), vec![zero], Sort::Int);
    let f_f_0 = terms.mk_app(Symbol::Named("f".to_string()), vec![f_0], Sort::Int);
    let eq1 = terms.mk_eq(f_0, one);
    let eq2 = terms.mk_eq(f_f_0, two);

    let mut fs = vec![eq1, eq2];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    let f_1 = terms.mk_app(Symbol::Named("f".to_string()), vec![one], Sort::Int);
    let expected = terms.mk_eq(f_1, two);
    assert!(changed);
    assert_eq!(
        fs,
        vec![eq1, expected],
        "the later definer must be rewritten by the earlier one (NOT frozen)"
    );
}

#[test]
fn goal_mode_harvests_non_ground_equalities() {
    // (= (f y) 3) (P (f y))  ->  ((= (f y) 3) (P 3))   [z3-verified]
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let f_y = terms.mk_app(Symbol::Named("f".to_string()), vec![y], Sort::Int);
    let eq = terms.mk_eq(f_y, three);
    let p_fy = terms.mk_app(Symbol::Named("P".to_string()), vec![f_y], Sort::Bool);

    let mut fs = vec![eq, p_fy];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    let p_3 = terms.mk_app(Symbol::Named("P".to_string()), vec![three], Sort::Bool);
    assert!(changed);
    assert_eq!(fs, vec![eq, p_3], "non-ground (f y) ↦ 3 must be harvested");
}

#[test]
fn goal_mode_backward_sweep_propagates_a_later_literal() {
    // (assert (or (not p) q)) (assert p)  ->  goal (q p)   [z3-verified]
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not(p);
    let clause = terms.mk_or(vec![not_p, q]);

    let mut fs = vec![clause, p];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    assert!(changed, "the BACKWARD sweep must see the later `p`");
    assert_eq!(fs, vec![q, p], "z3 goal order is (q p)");
}

#[test]
fn goal_mode_is_the_identity_when_nothing_propagates() {
    // (assert (<= x 5))  ->  unchanged, and NO progress reported (honesty).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let le = terms.mk_le(x, five);

    let mut fs = vec![le];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    assert!(!changed, "identity must report no progress");
    assert_eq!(fs, vec![le]);
}

#[test]
fn goal_mode_rewrites_nested_shared_occurrences() {
    // (assert p) (assert (= x (ite p 1 2)))  ->  (p (= x 1))   [z3-verified]
    // Locks in that the whole-formula `p ↦ true` harvest is applied to a
    // NESTED occurrence (an ite condition) and stays equivalence-preserving.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let ite = terms.mk_ite(p, one, two);
    let eq = terms.mk_eq(x, ite);

    let mut fs = vec![p, eq];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    let expected = terms.mk_eq(x, one);
    assert!(changed);
    assert_eq!(fs, vec![p, expected]);
}

#[test]
fn goal_mode_folds_a_repeated_defining_equality_to_true() {
    // (assert (= x 5)) (assert (or (= x 5) q))  ->  ((= x 5))   [z3-verified]
    // z3 maps the harvested equality atom itself to true; AY reaches the same
    // result through the reflexive fold ((= 5 5) → true after x ↦ 5) — this
    // test locks that equivalence in.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let q = terms.mk_var("q", Sort::Bool);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let clause = terms.mk_or(vec![eq, q]);

    let mut fs = vec![eq, clause];
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);

    assert!(changed);
    assert_eq!(fs, vec![eq], "(or true q) folds to true and is dropped");
}

#[test]
fn goal_mode_empty_goal_is_a_no_op() {
    let mut terms = TermStore::new();
    let mut fs: Vec<TermId> = Vec::new();
    let changed = PropagateValues::new().apply_goal(&mut terms, &mut fs);
    assert!(!changed);
    assert!(fs.is_empty());
}

#[test]
fn test_propagate_preserves_defining_equalities() {
    let mut terms = TermStore::new();

    // Create: (= (f 0) 5) and just that assertion
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));
    let f_0 = terms.mk_app(Symbol::Named("f".to_string()), vec![zero], Sort::Int);
    let eq = terms.mk_eq(f_0, five);

    let mut assertions = vec![eq];
    let mut pass = PropagateValues::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "should detect ground equality");

    // The defining equality is preserved (EUF needs it for congruence closure)
    assert_eq!(assertions.len(), 1, "defining equality preserved");
    assert_eq!(assertions[0], eq, "original equality unchanged");
}
