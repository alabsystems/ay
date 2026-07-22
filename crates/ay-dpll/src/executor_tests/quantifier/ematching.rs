// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test multi-round E-matching with chained triggers (#3994).
///
/// Round 1: P(0) matches pattern (P x), producing instantiation P(0) => Q(f(0)).
///          This introduces new ground term Q(f(0)).
/// Round 2: Q(f(0)) matches pattern (Q y), producing Q(f(0)) => false.
///          Combined with P(0) and round 1 result, this derives a contradiction.
///
/// Single-round E-matching cannot solve this because Q(f(0)) does not exist
/// as a ground term when the second quantifier is first processed.
#[test]
fn test_multiround_ematching_chained_trigger_unsat_3994() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int))
            (! (=> (P x) (Q (f x)))
               :pattern ((P x)))))
        (assert (forall ((y Int))
            (! (=> (Q y) false)
               :pattern ((Q y)))))
        (assert (P 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// Test 3-hop multi-round E-matching chain (#3994, sat-debuggability #4172).
///
/// This exercises all 3 rounds of MAX_EMATCHING_ROUNDS with a 3-step chain:
///
/// Round 1: A(0) matches pattern (A x), producing: A(x) => B(f(x)).
///          Introduces new ground term B(f(0)).
/// Round 2: B(f(0)) matches pattern (B y), producing: B(y) => C(g(y)).
///          Introduces new ground term C(g(f(0))).
/// Round 3: C(g(f(0))) matches pattern (C z), producing: C(z) => false.
///          Contradiction reached only if all 3 rounds fire.
///
/// With MAX_EMATCHING_ROUNDS < 3, this would return unknown instead of unsat.
#[test]
fn test_multiround_ematching_3hop_chain_unsat_3994() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun A (Int) Bool)
        (declare-fun B (Int) Bool)
        (declare-fun C (Int) Bool)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int))
            (! (=> (A x) (B (f x)))
               :pattern ((A x)))))
        (assert (forall ((y Int))
            (! (=> (B y) (C (g y)))
               :pattern ((B y)))))
        (assert (forall ((z Int))
            (! (=> (C z) false)
               :pattern ((C z)))))
        (assert (A 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // This requires 3 rounds of E-matching:
    // Round 1: A(0) => B(f(0))
    // Round 2: B(f(0)) => C(g(f(0)))
    // Round 3: C(g(f(0))) => false
    assert_eq!(outputs, vec!["unsat"]);
}
/// Test for #3325 Gap 2: multi-trigger E-matching with two independent patterns.
///
/// forall x y. p(f(x), g(y)) :pattern ((f x) (g y))
/// With ground terms f(a), g(b), the multi-trigger should fire with x=a, y=b.
/// Asserting NOT(p(f(a), g(b))) creates a contradiction with the instantiation.
#[test]
fn test_multi_trigger_two_patterns_unsat_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-fun p (S S) Bool)
        (declare-const a S)
        (declare-const b S)
        (assert (forall ((x S) (y S))
            (! (p (f x) (g y)) :pattern ((f x) (g y)))))
        (assert (not (p (f a) (g b))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // Multi-trigger [f(x), g(y)] matches with x=a, y=b.
    // Instantiation: p(f(a), g(b)). Combined with NOT(p(f(a), g(b))): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Multi-trigger should fire with x=a, y=b producing contradiction"
    );
}
/// Test for #3325 Gap 2: multi-trigger with shared variable across patterns.
///
/// forall x. q(f(x), g(x)) :pattern ((f x) (g x))
/// Ground terms f(a), g(a), g(b). Only x=a is consistent (both patterns agree).
#[test]
fn test_multi_trigger_shared_var_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-fun q (S S) Bool)
        (declare-const a S)
        (declare-const b S)
        (assert (forall ((x S))
            (! (q (f x) (g x)) :pattern ((f x) (g x)))))
        (assert (not (q (f a) (g a))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // Only x=a is consistent: f(a) matches f(x) with x=a, g(a) matches g(x) with x=a.
    // g(b) matches g(x) with x=b, but f(b) doesn't exist, so no f(x) match with x=b.
    // Instantiation: q(f(a), g(a)). With NOT(q(f(a), g(a))): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Multi-trigger with shared variable should find consistent binding x=a"
    );
}
/// Test for #3325 Gap 1: equality-aware E-matching.
///
/// Trigger pattern f(g(x)) should match ground term f(c) when (= (g a) c) is asserted.
/// Z3 solves this via E-graph congruence. AY now extracts equalities from assertions
/// and uses them during matching.
#[test]
fn test_equality_aware_matching_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-fun p (S) Bool)
        (declare-const a S)
        (declare-const c S)
        (assert (= (g a) c))
        (assert (forall ((x S)) (! (p (f (g x))) :pattern ((f (g x))))))
        (assert (not (p (f c))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // (g a) = c is asserted. f(c) should match f(g(x)) with x=a via equality.
    // Instantiation: p(f(g(a))) = p(f(c)). With NOT(p(f(c))): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Equality-aware matching should use (g a) = c to match f(c) against f(g(x))"
    );
}
/// Regression test for #3442: E-matching with user trigger on multi-argument function.
///
/// The trigger pattern `(index view i)` should match the ground term `(index view 0)`
/// with binding `i = 0`. After instantiation, the formula becomes a simple arithmetic
/// check that is satisfiable.
///
/// This tests the verification-consumer use case: element invariant with triggered forall.
#[test]
fn test_ematching_user_trigger_multiarg_3442() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun index (Int Int) Int)
        (declare-fun get_0 (Int) Int)
        (declare-fun get_1 (Int) Int)
        (declare-fun len (Int) Int)
        (declare-const view Int)
        (assert (= (len view) 1))
        (assert (forall ((i Int))
            (! (=> (and (>= i 0) (< i (len view)))
                   (= (+ (get_0 (index view i)) (get_1 (index view i))) 10))
               :pattern ((index view i)))))
        (assert (not (= (+ (get_0 (index view 0)) (get_1 (index view 0))) 20)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // The forall says get_0(index(view, i)) + get_1(index(view, i)) = 10 for valid indices.
    // The negated assertion says the sum != 20. Both can be satisfied (sum=10 != 20).
    // E-matching should trigger on (index view 0), binding i=0, instantiating the forall.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "E-matching should fire or return unknown for trigger (index view i): {outputs:?}"
    );
}
/// Regression test for #3442: E-matching trigger produces UNSAT via contradiction.
///
/// Same setup as test_ematching_user_trigger_multiarg_3442, but the negated assertion
/// contradicts the forall's instantiation: forall says sum=10 for valid indices,
/// but we assert NOT(sum=10) for index 0. E-matching must fire to derive the contradiction.
#[test]
fn test_ematching_user_trigger_multiarg_unsat_3442() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun index (Int Int) Int)
        (declare-fun get_0 (Int) Int)
        (declare-fun get_1 (Int) Int)
        (declare-fun len (Int) Int)
        (declare-const view Int)
        (assert (= (len view) 1))
        (assert (forall ((i Int))
            (! (=> (and (>= i 0) (< i (len view)))
                   (= (+ (get_0 (index view i)) (get_1 (index view i))) 10))
               :pattern ((index view i)))))
        (assert (>= 0 0))
        (assert (< 0 (len view)))
        (assert (not (= (+ (get_0 (index view 0)) (get_1 (index view 0))) 10)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // E-matching fires: (index view 0) matches trigger (index view i) with i=0.
    // Instantiation: (>= 0 0) AND (< 0 (len view)) => sum=10.
    // We also assert (>= 0 0), (< 0 (len view)), and NOT(sum=10).
    // Contradiction: implies both sum=10 and NOT(sum=10). UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "E-matching instantiation should derive contradiction"
    );
}
/// Regression test for #3325: binding save/restore in match_pattern_recursive.
///
/// This tests the specific fix where match_pattern_recursive_direct can
/// partially fill binding slots before failing, leaving dirty state that
/// breaks the equivalence class fallback.
///
/// Setup:
/// - Pattern: h(f(x, x)) — nested pattern requiring x bound consistently in both args
/// - Ground: h(f(a, b)) — only h-application, so only candidate for trigger
/// - Equality: f(a, b) = f(c, c) — provides eq-class alternative
///
/// Without the fix: direct match of f(x,x) against f(a,b) binds x=a then fails
/// (b ≠ a). binding[0]=Some(a) is dirty. Eq-class fallback tries f(c,c) but
/// sees binding[0]=Some(a), c ≠ a → fails. No match found.
///
/// With the fix: binding restored to clean state before eq-class loop.
/// f(c,c) matches with x=c. Instantiation: p(h(f(c,c))). Via congruence
/// h(f(a,b)) = h(f(c,c)), combined with ¬p(h(f(a,b))): UNSAT.
#[test]
fn test_ematching_binding_save_restore_3325() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (S S) S)
        (declare-fun h (S) S)
        (declare-fun p (S) Bool)
        (declare-const a S)
        (declare-const b S)
        (declare-const c S)
        (assert (distinct a b))
        (assert (distinct a c))
        (assert (distinct b c))
        (assert (= (f a b) (f c c)))
        (assert (forall ((x S)) (! (p (h (f x x))) :pattern ((h (f x x))))))
        (assert (not (p (h (f a b)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // The only h-application is h(f(a,b)). Pattern h(f(x,x)) must match via
    // eq-class: f(a,b) = f(c,c), so f(x,x) matches f(c,c) with x=c.
    // Requires clean binding state after failed direct match of f(x,x) on f(a,b).
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Binding save/restore must allow eq-class match after failed direct match"
    );
}
/// Regression: E-matching subst_vars must recurse into nested quantifier bodies.
///
/// Without the fix (subst_vars returning nested Forall/Exists unchanged), the outer
/// quantifier's variable `x` is NOT substituted inside the inner forall body.
/// This leaves `x` as a dangling free variable, preventing proper instantiation.
///
/// With the fix: outer instantiation x=a produces inner forall with (f a) replacing (f x).
/// Inner forall is then instantiated with y=5 (via E-matching on `p(y)` matching `p(5)`).
/// The ground formula (=> (= 5 (f a)) (p 5)) simplifies to (p 5), contradicting ¬(p 5).
#[test]
fn test_nested_forall_subst_vars_recurse() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun p (Int) Bool)
        (declare-const a Int)
        (assert (= (f a) 5))
        (assert (not (p 5)))
        (assert (forall ((x Int))
          (! (forall ((y Int)) (=> (= y (f x)) (p y)))
             :pattern ((f x)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // With nested substitution fix: UNSAT
    // Round 1: E-matching instantiates outer forall with x=a (trigger f(x) matches f(a)).
    //   Body becomes: forall y. (=> (= y (f a)) (p y))
    // Round 2: Inner forall instantiated with y=5 (trigger p(y) matches p(5)).
    //   Ground: (=> (= 5 (f a)) (p 5)) = (=> true (p 5)) = (p 5).
    //   Combined with ¬(p 5): UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Nested quantifier substitution must recurse into inner forall body"
    );
}
/// Test capture-avoidance: inner quantifier's bound variable shadows same-name outer variable.
/// Frontend renames to avoid this, but subst_vars must handle it correctly for API usage.
#[test]
fn test_nested_forall_capture_avoidance() {
    // forall x. (forall x. (= x 0)) is equivalent to forall y. true (inner x is independent).
    // The outer x has trigger f(x). Instantiating outer x=a should NOT affect inner x.
    // Inner forall (= x 0) is an equality constraint on x; CEGQI handles it.
    //
    // Note: The frontend renames inner x to x_0 (or similar), so in practice the names
    // don't collide. This test verifies correctness for direct API usage where names
    // could overlap.
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (= (f a) 5))
        (assert (forall ((x Int))
          (! (forall ((x Int)) (= x 0))
             :pattern ((f x)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // The inner forall (= x 0) says every Int is 0, which is false.
    // But AY may return unknown for this (CEGQI/enumerative limitation).
    // The key correctness requirement: outer x=a substitution must NOT
    // affect inner x. If it does, inner becomes (= a 0) which is satisfiable
    // (just set a=0), leading to an unsound SAT.
    // Accept either "unsat" or "unknown" - but NOT "sat"
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Must not return SAT (would indicate capture-avoidance failure): got {outputs:?}",
    );
}
/// #7883: verification-consumer's Seq concat-length axiom must match against ground Seq terms
/// in the E-matching pool.
///
/// The contradiction is only exposed if the trigger `(seq_concat s1 s2)`
/// matches the concrete ground term `(seq_concat a b)` and instantiates the
/// length equation for `a` and `b`.
#[test]
fn test_ematching_verification_consumer_seq_concat_len_pattern_unsat_7883() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort Seq 0)
        (declare-fun seq_len (Seq) Int)
        (declare-fun seq_concat (Seq Seq) Seq)
        (declare-const a Seq)
        (declare-const b Seq)
        (assert (forall ((s1 Seq) (s2 Seq))
            (! (= (seq_len (seq_concat s1 s2))
                  (+ (seq_len s1) (seq_len s2)))
               :pattern ((seq_concat s1 s2)))))
        (assert (= (seq_len a) 1))
        (assert (= (seq_len b) 2))
        (assert (not (= (seq_len (seq_concat a b)) 3)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Seq concat trigger should instantiate on the ground term (seq_concat a b)"
    );
}
/// #7883: verification-consumer's Seq index bridge trigger must match mixed Seq/Int ground terms.
///
/// The pattern `(seq_index_logic s i)` is the standard-library trigger shape
/// used by verification-consumer's array-backed sequence bridge. The formula is UNSAT only if
/// E-matching picks up the concrete ground term `(seq_index_logic a 0)`.
#[test]
fn test_ematching_verification_consumer_seq_index_logic_pattern_unsat_7883() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort Seq 0)
        (declare-fun seq_index_logic (Seq Int) Int)
        (declare-const a Seq)
        (assert (forall ((s Seq) (i Int))
            (! (= (seq_index_logic s i) i)
               :pattern ((seq_index_logic s i)))))
        (assert (not (= (seq_index_logic a 0) 0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Seq index trigger should instantiate on the ground term (seq_index_logic a 0)"
    );
}
/// Auto multi-trigger synthesis (#3325 item 2b): two disjoint-coverage patterns.
///
/// Formula:
///   (forall (x y) (=> (and (P x) (Q y)) (R x y)))
///   (P a)
///   (Q b)
///   (not (R a b))
///
/// No single auto-extracted pattern covers both x and y:
///   - P(x) covers {x}
///   - Q(y) covers {y}
///   - R(x,y) covers {x,y} but R is also under negation in the quantifier body
///
/// The auto multi-trigger synthesis should combine P(x) and Q(y) into a
/// multi-trigger group that covers both variables. The multi-trigger join
/// produces binding [x=a, y=b], and the instantiation contradicts (not (R a b)).
#[test]
fn test_auto_multi_trigger_synthesis_two_patterns() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun R (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U) (y U)) (=> (and (P x) (Q y)) (R x y))))
        (assert (P a))
        (assert (Q b))
        (assert (not (R a b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // With auto multi-trigger synthesis: P(x)+Q(y) triggers, binds [a,b], produces
    // (=> (and (P a) (Q b)) (R a b)), combined with P(a), Q(b), not(R a b) → UNSAT
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Auto multi-trigger synthesis should combine P(x) and Q(y) to derive UNSAT"
    );
}
/// Auto multi-trigger synthesis: full-coverage single pattern takes priority.
///
/// Formula:
///   (forall (x y) (=> (F x y) (G x y)))
///   (F a b)
///   (not (G a b))
///
/// F(x,y) covers both x and y — a single trigger suffices.
/// Multi-trigger synthesis should NOT be needed.
#[test]
fn test_auto_multi_trigger_full_coverage_single_preferred() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun F (U U) Bool)
        (declare-fun G (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U) (y U)) (=> (F x y) (G x y))))
        (assert (F a b))
        (assert (not (G a b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Single full-coverage trigger F(x,y) should suffice"
    );
}
/// Auto multi-trigger synthesis: three bound variables, three unary patterns.
///
/// Formula:
///   (forall (x y z) (=> (and (P x) (Q y) (S z)) (R x y z)))
///   (P a) (Q b) (S c)
///   (not (R a b c))
///
/// No single pattern covers all three vars. Synthesis combines P(x)+Q(y)+S(z)
/// into a triple multi-trigger.
#[test]
fn test_auto_multi_trigger_synthesis_three_vars() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun S (U) Bool)
        (declare-fun R (U U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (assert (forall ((x U) (y U) (z U)) (=> (and (P x) (Q y) (S z)) (R x y z))))
        (assert (P a))
        (assert (Q b))
        (assert (S c))
        (assert (not (R a b c)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Triple multi-trigger P(x)+Q(y)+S(z) should combine to derive UNSAT"
    );
}
/// Regression test for #7077: Mixed-sort BV+Int trigger instantiation.
///
/// When a constructor like Cons takes a (_ BitVec 32) and Int, the trigger
/// pattern (Cons h t) must match the ground term (Cons #x0000002a tail).
/// Previously this returned Unknown/Sat instead of Unsat because E-matching
/// failed to instantiate the mixed-sort trigger.
#[test]
fn test_mixed_sort_bv_int_trigger_instantiation_unsat_7077() {
    let input = r#"
        (set-logic ALL)
        (declare-fun Cons ((_ BitVec 32) Int) Int)
        (declare-fun size (Int) Int)
        (assert
          (forall ((h (_ BitVec 32)) (t Int))
            (! (= (size (Cons h t)) (+ 1 (size t)))
               :pattern ((Cons h t)))))
        (declare-fun tail () Int)
        (assert (<= (size (Cons #x0000002a tail)) (size tail)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // E-matching should instantiate the quantifier with h=#x0000002a, t=tail.
    // This gives: size(Cons(#x2a, tail)) = 1 + size(tail).
    // Combined with: size(Cons(#x2a, tail)) <= size(tail).
    // Since 1 + size(tail) <= size(tail) is impossible: UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Mixed BV+Int trigger should fire on (Cons #x0000002a tail)"
    );
}
/// Regression test for #7077: All-Int analogue works correctly.
///
/// Same formula shape as the mixed-sort case but with all-Int constructor.
/// This serves as a baseline: if this passes but the BV version fails,
/// the issue is specifically in mixed-sort handling.
#[test]
fn test_all_int_trigger_instantiation_unsat_7077_baseline() {
    let input = r#"
        (set-logic ALL)
        (declare-fun Cons (Int Int) Int)
        (declare-fun size (Int) Int)
        (assert
          (forall ((h Int) (t Int))
            (! (= (size (Cons h t)) (+ 1 (size t)))
               :pattern ((Cons h t)))))
        (declare-fun tail () Int)
        (assert (<= (size (Cons 42 tail)) (size tail)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "All-Int trigger should fire on (Cons 42 tail)"
    );
}

/// Regression test for #8616: AUFLIA quantifier E-matching SAT model verification.
///
/// From verification-consumer's `quantifier_forall_trigger_instantiation` test.
/// At ay commit 8620923ed983, the EUF solver's BCP-mode fast path (deferred
/// rebuild) could skip `incremental_merge_bool_valued_atoms()` and
/// `sync_egraph_to_uf()`, causing the E-graph to miss congruence merges.
/// This made E-matching fail to find the ground term match for f(5),
/// producing a SAT result that violated the clause database.
///
/// The fix (commit 323a15427) reverted the BCP-mode fast path, ensuring
/// the full incremental rebuild always runs.
#[test]
fn test_auflia_quantifier_forall_trigger_8616() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)))))
        (assert (<= (f 5) 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // E-matching: f(5) matches pattern (f x) with x=5.
    // Instantiation: f(5) > 0. Combined with f(5) <= 0: UNSAT.
    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8616: AUFLIA forall with trigger must instantiate on f(5)"
    );
}

/// Regression test for #8616 variant: UFLIA (no arrays) quantifier E-matching.
///
/// Same formula as test_auflia_quantifier_forall_trigger_8616 but with UFLIA
/// logic to verify E-matching works on both AUFLIA and UFLIA paths.
#[test]
fn test_uflia_quantifier_forall_trigger_8616() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)))))
        (assert (<= (f 5) 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8616: UFLIA forall with trigger must instantiate on f(5)"
    );
}

/// Regression: a satisfiable polymorphic identity counterexample query must
/// answer `sat`, not degrade to Unknown, when the restored universal
/// Box/Unbox and identity axioms admit a certified total model.
///
/// History: the original restored-total-UF-completion shortcut carried this
/// class unsoundly (no ground-coverage premises — removed as the #8969
/// wrong-SAT fix, which re-pinned this test to fail-closed `unknown`; a
/// local shape-only left-inverse arm briefly restored `sat` and was itself
/// removed as a wrong-SAT — see
/// `test_left_inverse_ground_non_injectivity_must_not_be_sat_2774`). The
/// sound replacement is the left-inverse SAT certificate
/// (`mbqi_sat_validated_left_inverse_axioms`): it EXHIBITS a total model by
/// functionalized re-evaluation (Box := injective embedding, Unbox :=
/// table-inverse + fallback, identity := id) and re-verifies every original
/// assertion under it, so this `sat` is certified, not heuristic.
#[test]
fn test_deductive_checks_polymorphic_identity_wrong_value_is_sat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const y (_ BitVec 32))
        (declare-fun identity (Poly) Poly)
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (= y #x00000005))
        (assert (forall ((x Poly)) (! (= (identity x) x) :pattern ((identity x)))))
        (assert (not (= (Unbox_i32 (identity (Box_i32 y))) #x00000006)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#2774: wrong-value polymorphic identity query should produce a counterexample"
    );
}

/// Regression for the removed ae06cec3b5 left-inverse/identity certificate
/// arm (wrong-SAT): a ground fact forcing `Box` NON-INJECTIVITY contradicts
/// the axiom (`Unbox(Box a) = a`, `Unbox(Box b) = b`, `Box a = Box b` ⟹
/// `a = b` by congruence through `Unbox`, vs `distinct a b`) — the formula
/// is UNSAT, and the removed arm certified it `sat`: its "genuine ground Sat
/// over a decision-complete core" premise was unenforced (the ground layer
/// treats uninterpreted-sorted equalities between distinct UF applications
/// as free, missing the quantifier-derived congruence consequence). Any
/// answer but `sat` is sound here; `unsat` is the exact answer.
#[test]
fn test_left_inverse_ground_non_injectivity_must_not_be_sat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (distinct a b))
        (assert (= (Box_i32 a) (Box_i32 b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs.len(), 1, "Expected 1 output, got: {outputs:?}");
    assert_ne!(
        outputs[0], "sat",
        "#2774: ground non-injectivity is UNSAT by congruence — must never certify sat"
    );
}

/// The UF-completion SAT path must not hide an explicit violated ground
/// instance of the same universal Box/Unbox axiom.
#[test]
fn test_deductive_checks_polymorphic_box_unbox_ground_violation_is_unsat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (not (= (Unbox_i32 (Box_i32 #x00000000)) #x00000000)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#2774: explicit ground violation must remain UNSAT"
    );
}

/// deductive-checks `seq_from_fn` shape (#seq-from-fn bounded discharge): an array
/// pinned pointwise by a `bvult`-guarded forall with a LITERAL length, plus a
/// goal reading an OUT-OF-RANGE index. The guard exempts index 5, so the read
/// is unconstrained and the formula is satisfiable (z3: sat). The
/// literal-bounded BV forall is discharged by exact finite expansion, making
/// the problem quantifier-free.
#[test]
fn test_seq_from_fn_bounded_bv_guard_out_of_range_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000002) (= (select s i) ((_ extract 31 0) i)))
             :pattern ((select s i)))))
        (assert (=> (bvult #x0000000000000000 #x0000000000000002)
                    (= (select s #x0000000000000000) #x00000000)))
        (assert (=> (bvult #x0000000000000001 #x0000000000000002)
                    (= (select s #x0000000000000001) #x00000001)))
        (assert (= (select s #x0000000000000005) #x00000000))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "out-of-range read of a bounded from_fn array must be sat"
    );
}

/// Adversarial twin of the bounded discharge: a ground fact pinning an
/// IN-RANGE index inconsistently with the axiom must stay unsat — the
/// expansion is an exact equivalence, so the guarded instance
/// `(= (select s 1) #x00000001)` directly contradicts the pin.
#[test]
fn test_seq_from_fn_bounded_bv_guard_in_range_violation_is_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000002) (= (select s i) ((_ extract 31 0) i)))
             :pattern ((select s i)))))
        (assert (= (select s #x0000000000000001) #x000000ff))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "in-range violation of a bounded from_fn axiom must stay unsat"
    );
}

/// Adversarial probe for the #2774 left-inverse/identity certificate: a
/// covered ground violation of an identity axiom must stay unsat (the trigger
/// IS the identity application, so the violating application is instantiated
/// and refuted on the ground).
#[test]
fn test_identity_over_uninterpreted_sort_ground_violation_is_unsat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const p Poly)
        (declare-fun identity (Poly) Poly)
        (assert (forall ((x Poly)) (! (= (identity x) x) :pattern ((identity x)))))
        (assert (not (= (identity p) p)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#2774: covered identity violation must remain UNSAT"
    );
}

/// Adversarial probe for the #2774 certificate's COVERAGE premise: when the
/// axiom's trigger is a DIFFERENT symbol than its head, a ground application
/// of the head at an uncovered point is NOT forced to agree with the axiom,
/// so no sat certificate may fire (the exact #8969 hole shape). The formula
/// is genuinely UNSAT (`identity q != q` contradicts the forall), so any
/// answer but `sat` is sound; `sat` here would be a wrong-SAT.
#[test]
fn test_identity_trigger_disjoint_uncovered_head_is_never_sat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const p Poly)
        (declare-const q Poly)
        (declare-fun identity (Poly) Poly)
        (declare-fun probe (Poly) Bool)
        (assert (forall ((x Poly)) (! (= (identity x) x) :pattern ((probe x)))))
        (assert (probe p))
        (assert (not (= (identity q) q)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_ne!(
        outputs,
        vec!["sat"],
        "#2774/#8969: uncovered head application must not be certified sat"
    );
}

/// Adversarial probe: a left-inverse axiom whose codomain sort also carries
/// an UNRECOGNIZED quantifier (here a one-element cardinality bound on Poly)
/// must not be certified sat — the certificate's fresh-element universe
/// enlargement is only sound when EVERY quantifier in scope is a recognized
/// shape. The formula is genuinely UNSAT for BitVec 32 (|Poly| = 1 forces
/// Box 0 = Box 1, and the left inverse then forces 0 = 1).
#[test]
fn test_left_inverse_with_cardinality_bound_is_never_sat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const c Poly)
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (forall ((y Poly)) (= y c)))
        (assert (= (Unbox_i32 (Box_i32 #x00000000)) #x00000000))
        (assert (= (Unbox_i32 (Box_i32 #x00000001)) #x00000001))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_ne!(
        outputs,
        vec!["sat"],
        "#2774: cardinality-bounded codomain must not be certified sat"
    );
}

/// False-control for the left-inverse SAT certificate
/// (`mbqi_sat_validated_left_inverse_axioms`): a ground fact forcing `Box`
/// NON-INJECTIVITY contradicts the axiom (`Unbox(Box a) = a`,
/// `Unbox(Box b) = b`, `Box a = Box b` ⟹ `a = b` vs `distinct a b`) — the
/// certificate's injectivity check must decline and the query stay UNSAT.
///
/// GAP CLOSED (K2, #2774): this pin was red-by-ignore because the ground
/// refutation `Unbox(Box a) = Unbox(Box b)` (congruence from the two
/// e-matched instances + `Box a = Box b`) was never derived on the ALL/BV
/// route — the certificate correctly declined (verified by the sibling
/// `..._is_not_sat_...` control below), but the engine answered the sound
/// fail-closed `unknown` instead of the asserted exact `unsat`. Root cause
/// was in the eager QF_UFBV ground encoding, not the quantifier layer: a
/// BV-return UF application pair with uninterpreted-sort arguments
/// (`Unbox(Box a)` / `Unbox(Box b)`, args of sort `Poly`) was skipped by
/// BOTH congruence generators — `generate_euf_bv_axioms_debug` needs BV bits
/// on every differing argument, and `generate_non_bv_euf_congruence`'s
/// consumer gates need a ground `(= f(a) f(b))`/`distinct` atom or
/// Bool-return Tseitin vars. Fixed by section 1c of
/// `generate_non_bv_euf_congruence` (bit-level result congruence with
/// Tseitin-encoded argument equality), after which the instantiated ground
/// core is UNSAT by plain EUF congruence. z3-adjudicated unsat (#8969
/// discipline).
#[test]
fn false_control_left_inverse_ground_non_injectivity_unsat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (distinct a b))
        (assert (= (Box_i32 a) (Box_i32 b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#2774 left-inverse cert: ground non-injectivity must stay UNSAT"
    );
}

/// Runnable sibling of the ignored exact-`unsat` pin above: the
/// CERTIFICATE-SIDE guarantee for ground non-injectivity. The left-inverse
/// certificate's Box materialization is structurally injective, so
/// re-evaluating `(= (Box_i32 a) (Box_i32 b))` under distinct `a`,`b` yields
/// false and the certificate DECLINES — the engine must answer `unsat` or a
/// fail-closed `unknown`, NEVER `sat`. This stays enforced in CI while the
/// exact-refutation pin waits on the missing ground-congruence derivation.
#[test]
fn false_control_left_inverse_ground_non_injectivity_is_not_sat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (distinct a b))
        (assert (= (Box_i32 a) (Box_i32 b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs.len(), 1, "Expected 1 output, got: {outputs:?}");
    assert_ne!(
        outputs[0], "sat",
        "#2774 left-inverse cert: ground non-injectivity must never certify SAT (unsat or fail-closed unknown)"
    );
}

/// False-control for the left-inverse SAT certificate: a ground fact pinning
/// `Unbox` AGAINST the axiom on the `Box` image (`Unbox(Box c) = d`,
/// `distinct c d`) — the image-agreement check must decline and the e-matched
/// instance must refute.
#[test]
fn false_control_left_inverse_image_disagreement_unsat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const c (_ BitVec 32))
        (declare-const d (_ BitVec 32))
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (distinct c d))
        (assert (= (Unbox_i32 (Box_i32 c)) d))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#2774 left-inverse cert: Unbox image disagreement must stay UNSAT"
    );
}

/// False-control for the left-inverse SAT certificate's composition rule: a
/// domain-collapse forall (`forall u v:Poly. u = v`) alongside the axiom is
/// NOT a universe-independent shape, so the certificate must decline (the
/// enlargement argument would break it). Collapse + axiom + `distinct a b`
/// is genuinely UNSAT; SAT here would be a wrong verdict.
#[test]
fn false_control_left_inverse_domain_collapse_interaction_not_sat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-const a (_ BitVec 32))
        (declare-const b (_ BitVec 32))
        (declare-fun Box_i32 ((_ BitVec 32)) Poly)
        (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
        (assert (forall ((x (_ BitVec 32))) (! (= (Unbox_i32 (Box_i32 x)) x) :pattern ((Box_i32 x)))))
        (assert (forall ((u Poly) (v Poly)) (= u v)))
        (assert (distinct a b))
        (assert (or (= (Box_i32 a) (Box_i32 b)) (distinct (Box_i32 a) (Box_i32 b))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs.len(), 1, "Expected 1 output, got: {outputs:?}");
    assert_ne!(
        outputs[0], "sat",
        "#2774 left-inverse cert: domain-collapse interaction must not be SAT (unsat or fail-closed unknown)"
    );
}

/// False-control for the left-inverse SAT certificate's sort restriction: a
/// `Box` into an INTERPRETED sort (Bool) cannot be enlarged, and
/// `forall x:BV8. BoolUnbox(BoolBox x) = x` is a pigeonhole UNSAT (256 → 2).
/// The certificate must decline on the interpreted result sort; any SAT here
/// would be a wrong verdict.
///
/// HISTORY: this pin was red-by-ignore for a ground-layer WRONG-SAT (the
/// certificate correctly declined — `left_inverse_axiom_symbols` requires
/// `Sort::Uninterpreted` on the boxed term — but the eager-bitblast ground
/// solve dropped congruence over Bool-sorted UF argument positions and
/// certified `sat`). Closed by the #boolarg-congruence fix (see
/// `tests/group_bv/bool_arg_congruence_boolbox.rs`); the query now answers
/// exact `unsat`. The assertion stays `!= sat` because this test is the
/// soundness gate — a completeness regression to `unknown` is fail-closed
/// and belongs to the group_bv suite's exact-verdict pins, not here.
#[test]
fn false_control_left_inverse_interpreted_target_not_sat_2774() {
    let input = r#"
        (set-logic ALL)
        (declare-fun BoolBox ((_ BitVec 8)) Bool)
        (declare-fun BoolUnbox (Bool) (_ BitVec 8))
        (declare-const w (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (! (= (BoolUnbox (BoolBox x)) x) :pattern ((BoolBox x)))))
        (assert (= (BoolBox w) true))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs.len(), 1, "Expected 1 output, got: {outputs:?}");
    assert_ne!(
        outputs[0], "sat",
        "#2774 left-inverse cert: interpreted target sort must decline (pigeonhole UNSAT or fail-closed unknown)"
    );
}

/// verification-consumer's popcount logic helper is a universal constant-function definition:
/// `forall n. logic_count8__log(n) = c`, where `c` is built from free ITE
/// auxiliaries and does not depend on the bound `n`. MBQI should complete the
/// UF model for satisfiable consistency checks instead of returning Unknown.
#[test]
fn test_verification_consumer_constant_uf_definition_is_sat_8961() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun logic_count8__log (Int) Int)
        (declare-const bit0 Int)
        (declare-const bit1 Int)
        (assert (= bit0 0))
        (assert (= bit1 1))
        (assert (forall ((n Int))
            (! (= (+ bit0 bit1) (logic_count8__log n))
               :pattern ((logic_count8__log n)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#8961: constant UF definition should be model-completable"
    );
}

/// The constant-UF completion path must still reject an explicit ground
/// violation of the same universal definition.
#[test]
fn test_verification_consumer_constant_uf_definition_ground_violation_is_unsat_8961() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun logic_count8__log (Int) Int)
        (declare-const bit0 Int)
        (declare-const bit1 Int)
        (assert (= bit0 0))
        (assert (= bit1 1))
        (assert (forall ((n Int))
            (! (= (+ bit0 bit1) (logic_count8__log n))
               :pattern ((logic_count8__log n)))))
        (assert (not (= (+ bit0 bit1) (logic_count8__log 5))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#8961: explicit violation of constant UF definition must remain UNSAT"
    );
}

/// Regression test for the #qfax-quantified-bypass gate (Z3 #7544 parity).
///
/// Subset antisymmetry over characteristic `(Array Int Bool)` arrays:
///   (forall x. a[x] => b[x]) ∧ (forall x. b[x] => a[x]) ∧ (distinct a b)
/// is UNSAT (mutual subset implies extensional equality). Under
/// `(set-logic ALL)` the quantifier-stripped ground window auto-detects as
/// QfAuflia with constants-only integer content, and the isolated array-EUF
/// escalation (4a853221) used to intercept it: its stage-1 `Sat` left no EUF
/// model for `try_ematching_refinement_round`, so interleaved E-matching never
/// instantiated the foralls at the extensionality witness and the #8729 guard
/// degraded the provable UNSAT to `unknown`. The escalation is now gated on
/// `original_problem_had_quantifiers`, restoring the explicit-AUFLIA behavior.
#[test]
fn test_all_logic_quantified_bool_array_subset_antisymmetry_unsat_7544() {
    let input = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Bool))
        (declare-fun b () (Array Int Bool))
        (assert (forall ((x Int)) (=> (select a x) (select b x))))
        (assert (forall ((x Int)) (=> (select b x) (select a x))))
        (assert (distinct a b))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "Z3#7544: mutual-subset Bool arrays with distinct must be UNSAT under (set-logic ALL)"
    );
}
