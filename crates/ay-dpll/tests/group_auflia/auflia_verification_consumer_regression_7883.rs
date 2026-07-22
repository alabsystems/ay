// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for verification-consumer downstream regressions #7883-#7887.
//!
//! SAT-level behavioral changes (#7633: shrink_enabled=false, #7649:
//! has_been_incremental=true) altered the CDCL search trajectory, breaking
//! E-matching convergence on AUFLIA formulas that verification-consumer depends on.
//!
//! Fixes applied: vivification re-enabled for theory mode (#8836),
//! post-CEGQI E-matching pass added (#8837).
//!
//! These tests exercise realistic verification-consumer verification patterns that require:
//! - Multi-round E-matching with chaining (#7883)
//! - Wrapping/modular arithmetic with UF axioms (#7884)
//! - Loop invariant preservation with inductive steps (#7885)
//! - Recursive closure properties (#7886)
//! - Standard library specification patterns (#7887)

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn expect_unsat(input: &str, label: &str) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let last = outputs.last().expect("at least one output");
    assert_eq!(
        last.trim(),
        "unsat",
        "{label}: expected UNSAT, got {}",
        last.trim()
    );
}

fn expect_sat(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert_eq!(result, SolverOutcome::Sat, "{label}: expected SAT");
}

fn expect_unsat_or_unknown(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert!(
        matches!(result, SolverOutcome::Unsat | SolverOutcome::Unknown),
        "{label}: expected UNSAT or Unknown, got {result:?}",
    );
}

// ============================================================================
// #7883: Quantifier E-matching completeness
// ============================================================================

/// #7883 pattern: Multi-round E-matching chain with transitive axioms.
///
/// verification-consumer generates verification conditions where proving a property requires
/// instantiating multiple quantified axioms in sequence: axiom A produces a
/// ground term that triggers axiom B, which produces a term that triggers C.
/// This requires 3 E-matching rounds minimum.
///
/// P(a) is given. forall x. P(x) => P(f(x)). Goal: P(f(f(a))).
/// Round 1: instantiate x:=a, get P(f(a)).
/// Round 2: instantiate x:=f(a), get P(f(f(a))).
/// Contradiction with not(P(f(f(a)))).
#[test]
#[timeout(30_000)]
fn test_7883_ematching_two_step_chain() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort T 0)
        (declare-fun P (T) Bool)
        (declare-fun f (T) T)
        (declare-const a T)
        (assert (forall ((x T)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
        (assert (P a))
        (assert (not (P (f (f a)))))
        (check-sat)
        "#,
        "#7883: two-step E-matching chain",
    );
}

/// #7883 pattern: Three-step chain requires 4 E-matching rounds.
///
/// P(a) + forall x. P(x) => P(f(x)) + not(P(f(f(f(a))))).
/// Requires 3 instantiations chained across rounds.
#[test]
#[timeout(30_000)]
fn test_7883_ematching_three_step_chain() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort T 0)
        (declare-fun P (T) Bool)
        (declare-fun f (T) T)
        (declare-const a T)
        (assert (forall ((x T)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
        (assert (P a))
        (assert (not (P (f (f (f a))))))
        (check-sat)
        "#,
        "#7883: three-step E-matching chain",
    );
}

/// #7883 pattern: Cross-axiom chaining.
///
/// verification-consumer verification conditions often involve multiple axioms where
/// one axiom's conclusion triggers another. This tests that the solver
/// can chain across different quantified assertions.
///
/// Axiom 1: forall x. A(x) => B(f(x))
/// Axiom 2: forall y. B(y) => C(g(y))
/// Given: A(a). Goal: C(g(f(a))).
/// Round 1: A(a) triggers axiom 1 with x:=a, get B(f(a)).
/// Round 2: B(f(a)) triggers axiom 2 with y:=f(a), get C(g(f(a))).
#[test]
#[timeout(30_000)]
fn test_7883_cross_axiom_chaining() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort T 0)
        (declare-fun A (T) Bool)
        (declare-fun B (T) Bool)
        (declare-fun C (T) Bool)
        (declare-fun f (T) T)
        (declare-fun g (T) T)
        (declare-const a T)
        (assert (forall ((x T)) (! (=> (A x) (B (f x))) :pattern ((A x)))))
        (assert (forall ((y T)) (! (=> (B y) (C (g y))) :pattern ((B y)))))
        (assert (A a))
        (assert (not (C (g (f a)))))
        (check-sat)
        "#,
        "#7883: cross-axiom E-matching chain",
    );
}

/// #7883 pattern: Triggerless quantifier with enumerative instantiation.
///
/// verification-consumer emits triggerless quantifiers for extensional equality and
/// pointwise axioms. Without triggers, the solver must use enumerative
/// instantiation to find ground instances. Post-CEGQI E-matching (#7979)
/// ensures these get properly resolved.
#[test]
#[timeout(30_000)]
fn test_7883_triggerless_quantifier_enum() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (= a 5))
        (assert (forall ((x Int)) (= (f x) (+ x 1))))
        (assert (not (= (f a) 6)))
        (check-sat)
        "#,
        "#7883: triggerless quantifier enumerative instantiation",
    );
}

/// #7883 pattern: Multiple quantifiers sharing a function symbol.
///
/// verification-consumer's sequence axiom sets include multiple axioms mentioning the
/// same function (e.g., seq_len, seq_index). E-matching must process
/// all relevant axioms when a ground term appears.
#[test]
#[timeout(30_000)]
fn test_7883_shared_function_symbol_axioms() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun len ((Array Int Int)) Int)
        (declare-fun valid ((Array Int Int)) Bool)
        (declare-const arr (Array Int Int))
        ; Axiom 1: length is non-negative
        (assert (forall ((a (Array Int Int))) (! (>= (len a) 0) :pattern ((len a)))))
        ; Axiom 2: valid arrays have positive length
        (assert (forall ((a (Array Int Int))) (! (=> (valid a) (> (len a) 0)) :pattern ((valid a)))))
        (assert (valid arr))
        (assert (not (> (len arr) 0)))
        (check-sat)
        "#,
        "#7883: shared function symbol across axioms",
    );
}

// ============================================================================
// #7884: LIA+UF wrapping arithmetic
// ============================================================================

/// #7884 pattern: Wrapping addition axiom with concrete overflow.
///
/// verification-consumer models Rust's wrapping arithmetic via quantified UF axioms:
/// wrapping_add(a, b) = (a + b) mod 2^N. This must work for values that
/// actually overflow.
#[test]
#[timeout(30_000)]
fn test_7884_wrapping_add_overflow() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun wrapping_add (Int Int) Int)
        (assert (forall ((a Int) (b Int))
          (! (= (wrapping_add a b) (mod (+ a b) 256))
             :pattern ((wrapping_add a b)))))
        ; 250 + 10 = 260 mod 256 = 4
        (assert (not (= (wrapping_add 250 10) 4)))
        (check-sat)
        "#,
        "#7884: wrapping add with overflow",
    );
}

/// #7884 pattern: Wrapping subtraction via axiom.
///
/// wrapping_sub(a, b) = (a - b + 256) mod 256 for u8 semantics.
/// 3 - 5 + 256 = 254 mod 256 = 254.
#[test]
#[timeout(30_000)]
fn test_7884_wrapping_sub_underflow() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun wrapping_sub (Int Int) Int)
        (assert (forall ((a Int) (b Int))
          (! (= (wrapping_sub a b) (mod (+ (- a b) 256) 256))
             :pattern ((wrapping_sub a b)))))
        ; 3 - 5 wrapping = 254
        (assert (not (= (wrapping_sub 3 5) 254)))
        (check-sat)
        "#,
        "#7884: wrapping sub with underflow",
    );
}

/// #7884 pattern: Wrapping arithmetic with symbolic values and bounds check.
///
/// Given 0 <= x < 128 and 0 <= y < 128, wrapping_add(x, y) = x + y
/// (no overflow because x + y < 256).
#[test]
#[timeout(30_000)]
fn test_7884_wrapping_no_overflow_symbolic() {
    // This test uses expect_unsat_or_unknown because it involves quantified
    // mod/div constraints. The solver correctly instantiates the quantifier
    // via E-matching, but the resulting ground formula requires reasoning about
    // `mod(x+y, 256) = x+y` when `0 <= x+y < 256`. The LIA solver cannot
    // always prove this (mod reasoning incompleteness), so the model validation
    // catches the invalid model and degrades to Unknown rather than returning
    // a spurious SAT. This is the correct behavior — Unknown is sound. (#7979)
    expect_unsat_or_unknown(
        r#"
        (set-logic AUFLIA)
        (declare-fun wrapping_add (Int Int) Int)
        (assert (forall ((a Int) (b Int))
          (! (= (wrapping_add a b) (mod (+ a b) 256))
             :pattern ((wrapping_add a b)))))
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (< x 128))
        (assert (>= y 0))
        (assert (< y 128))
        ; x + y < 256, so wrapping_add(x,y) = x + y
        (assert (not (= (wrapping_add x y) (+ x y))))
        (check-sat)
        "#,
        "#7884: wrapping add no overflow with symbolic bounds (known LIA+mod gap)",
    );
}

/// #7884 pattern: Chained wrapping operations.
///
/// wrapping_add(wrapping_add(100, 100), 100) = (100+100+100) mod 256 = 44.
/// E-matching instantiates both wrapping_add applications in one round
/// (both are ground terms in the negated goal). The inner instantiation
/// produces wrapping_add(100,100) = mod(200, 256). The outer produces
/// wrapping_add(wrapping_add(100,100), 100) = mod(wrapping_add(100,100)+100, 256).
/// The LIA solver must chain these equalities to derive the final value.
///
/// Z3 returns UNSAT. AY currently returns unknown because the LIA solver
/// does not fully reduce mod(wrapping_add(100,100)+100, 256) after
/// substituting the inner equality. This is a known completeness gap
/// in the E-matching + LIA integration for nested UF applications.
#[test]
#[timeout(30_000)]
fn test_7884_chained_wrapping_ops() {
    expect_unsat_or_unknown(
        r#"
        (set-logic AUFLIA)
        (declare-fun wrapping_add (Int Int) Int)
        (assert (forall ((a Int) (b Int))
          (! (= (wrapping_add a b) (mod (+ a b) 256))
             :pattern ((wrapping_add a b)))))
        ; wrapping_add(wrapping_add(100, 100), 100) = 300 mod 256 = 44
        (assert (not (= (wrapping_add (wrapping_add 100 100) 100) 44)))
        (check-sat)
        "#,
        "#7884: chained wrapping operations (known gap: nested UF + mod)",
    );
}

// ============================================================================
// #7885: Loop verification completeness
// ============================================================================

/// #7885 pattern: Simple loop invariant preservation.
///
/// verification-consumer's loop verification: invariant holds at entry, preserved by
/// body, must hold at exit. This is the core inductive step.
///
/// inv(n) <=> n >= 0.
/// Pre: inv(x). Body: x' = x + 1. Goal: inv(x').
#[test]
#[timeout(30_000)]
fn test_7885_loop_invariant_simple_increment() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun inv (Int) Bool)
        (declare-const x_pre Int)
        (declare-const x_post Int)
        (assert (forall ((n Int)) (! (= (inv n) (>= n 0)) :pattern ((inv n)))))
        (assert (inv x_pre))
        (assert (= x_post (+ x_pre 1)))
        (assert (not (inv x_post)))
        (check-sat)
        "#,
        "#7885: loop invariant simple increment",
    );
}

/// #7885 pattern: Loop invariant with upper bound.
///
/// inv(n, limit) <=> (0 <= n <= limit).
/// Pre: inv(x, L). Body: x' = x + 1, assume x < L.
/// Goal: inv(x', L).
#[test]
#[timeout(30_000)]
fn test_7885_loop_invariant_bounded() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun inv (Int Int) Bool)
        (declare-const x_pre Int)
        (declare-const x_post Int)
        (declare-const limit Int)
        (assert (forall ((n Int) (l Int))
          (! (= (inv n l) (and (>= n 0) (<= n l)))
             :pattern ((inv n l)))))
        (assert (inv x_pre limit))
        (assert (< x_pre limit))
        (assert (= x_post (+ x_pre 1)))
        (assert (not (inv x_post limit)))
        (check-sat)
        "#,
        "#7885: loop invariant with upper bound",
    );
}

/// #7885 pattern: Loop invariant with array and index.
///
/// verification-consumer models array-processing loops. The invariant states that
/// all elements processed so far satisfy a property.
///
/// inv(arr, i) <=> forall j. 0 <= j < i => arr[j] >= 0
/// Pre: inv(arr, 0) (trivially true).
/// Body: assert arr[i] >= 0, set i' = i + 1.
/// Goal: inv(arr, i').
///
/// This is a complex pattern combining arrays, quantifiers, and arithmetic.
/// We simplify to avoid nested quantifier issues and test the core pattern.
#[test]
#[timeout(30_000)]
fn test_7885_loop_array_processing() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-const arr (Array Int Int))
        (declare-const i Int)
        (declare-fun processed (Int) Bool)
        ; processed(k) means we've verified arr[0..k) are non-negative
        (assert (forall ((k Int))
          (! (=> (and (processed k) (>= (select arr k) 0))
              (processed (+ k 1)))
             :pattern ((processed k)))))
        ; Base case: processed(0) is true
        (assert (processed 0))
        ; The element at index 0 is non-negative
        (assert (>= (select arr 0) 0))
        ; Goal: processed(1)
        (assert (not (processed 1)))
        (check-sat)
        "#,
        "#7885: loop array processing invariant",
    );
}

/// #7885 pattern: Loop with decreasing variant function.
///
/// verification-consumer proves loop termination via a decreasing variant.
/// variant(x) >= 0 and variant(x') < variant(x) for each iteration.
#[test]
#[timeout(30_000)]
fn test_7885_loop_variant_decreasing() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun variant (Int) Int)
        (declare-const x_pre Int)
        (declare-const x_post Int)
        (assert (forall ((n Int)) (! (= (variant n) n) :pattern ((variant n)))))
        (assert (> (variant x_pre) 0))
        (assert (= x_post (- x_pre 1)))
        (assert (not (< (variant x_post) (variant x_pre))))
        (check-sat)
        "#,
        "#7885: loop variant decreasing",
    );
}

// ============================================================================
// #7886: Closure verification
// ============================================================================

/// #7886 pattern: Simple function composition closure.
///
/// verification-consumer verifies closure properties: if f is monotone and f(a) > a,
/// then f(f(a)) > f(a) > a. This requires E-matching to chain the
/// monotonicity axiom.
#[test]
#[timeout(30_000)]
fn test_7886_closure_monotone_composition() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        ; f is strictly monotone
        (assert (forall ((x Int) (y Int))
          (! (=> (< x y) (< (f x) (f y)))
             :pattern ((f x) (f y)))))
        ; f(a) > a
        (assert (< a (f a)))
        ; Goal: f(f(a)) > f(a) (follows from monotonicity with x:=a, y:=f(a))
        (assert (not (< (f a) (f (f a)))))
        (check-sat)
        "#,
        "#7886: closure monotone composition",
    );
}

/// #7886 pattern: Closure over a predicate.
///
/// If P is closed under f (P(x) => P(f(x))), and P(a), then P(f(a)).
/// This is the fundamental pattern verification-consumer uses for closure verification.
#[test]
#[timeout(30_000)]
fn test_7886_closure_predicate_preservation() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun f (S) S)
        (declare-const a S)
        ; P closed under f
        (assert (forall ((x S)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
        ; P(a) holds
        (assert (P a))
        ; Goal: P(f(a))
        (assert (not (P (f a))))
        (check-sat)
        "#,
        "#7886: closure predicate preservation",
    );
}

/// #7886 pattern: Two-step closure with multiple predicates.
///
/// P closed under f, Q closed under g, P(x) => Q(x).
/// Given P(a), prove Q(g(f(a))).
/// Chain: P(a) => P(f(a)) => Q(f(a)) => Q(g(f(a))).
#[test]
#[timeout(30_000)]
fn test_7886_closure_two_predicates_chain() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun Q (S) Bool)
        (declare-fun f (S) S)
        (declare-fun g (S) S)
        (declare-const a S)
        ; P closed under f
        (assert (forall ((x S)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
        ; Q closed under g
        (assert (forall ((x S)) (! (=> (Q x) (Q (g x))) :pattern ((Q x)))))
        ; P implies Q
        (assert (forall ((x S)) (! (=> (P x) (Q x)) :pattern ((P x)))))
        (assert (P a))
        ; Goal: Q(g(f(a)))
        ; P(a) => P(f(a)) => Q(f(a)) => Q(g(f(a)))
        (assert (not (Q (g (f a)))))
        (check-sat)
        "#,
        "#7886: closure two-predicate chain",
    );
}

/// #7886 pattern: Closure with implication under guard.
///
/// verification-consumer often generates guarded closure axioms:
/// forall x. guard(x) => (P(x) => P(f(x))).
/// The guard must be satisfied for the closure to apply.
#[test]
#[timeout(30_000)]
fn test_7886_closure_guarded() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        ; Guarded closure: only applies when x >= 0
        (assert (forall ((x Int))
          (! (=> (and (>= x 0) (P x)) (P (f x)))
             :pattern ((P x)))))
        ; f preserves non-negativity
        (assert (forall ((x Int))
          (! (=> (>= x 0) (>= (f x) 0))
             :pattern ((f x)))))
        (assert (>= a 0))
        (assert (P a))
        ; Goal: P(f(a))
        (assert (not (P (f a))))
        (check-sat)
        "#,
        "#7886: guarded closure",
    );
}

// ============================================================================
// #7887: Std_specs verification failures
// ============================================================================

/// #7887 pattern: Option::unwrap specification.
///
/// verification-consumer models Rust's Option type with axioms:
/// is_some(some(v)) = true, unwrap(some(v)) = v.
/// Verification: if is_some(x), then some(unwrap(x)) = x.
#[test]
#[timeout(30_000)]
fn test_7887_option_unwrap_spec() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort Val 0)
        (declare-sort Opt 0)
        (declare-fun some (Val) Opt)
        (declare-fun unwrap (Opt) Val)
        (declare-fun is_some (Opt) Bool)
        (declare-const x Opt)
        ; some(v) is always Some
        (assert (forall ((v Val)) (! (= (is_some (some v)) true) :pattern ((some v)))))
        ; unwrap(some(v)) = v
        (assert (forall ((v Val)) (! (= (unwrap (some v)) v) :pattern ((some v)))))
        ; Roundtrip: is_some(x) => some(unwrap(x)) = x
        (assert (forall ((o Opt)) (! (=> (is_some o) (= (some (unwrap o)) o)) :pattern ((unwrap o)))))
        ; x is Some
        (assert (is_some x))
        ; Goal: unwrap(x) produces a valid value that round-trips
        (assert (not (= (some (unwrap x)) x)))
        (check-sat)
        "#,
        "#7887: Option::unwrap roundtrip spec",
    );
}

/// #7887 pattern: Vec bounds checking specification.
///
/// verification-consumer models Vec::get with axioms:
/// 0 <= i < len(v) => is_some(get(v, i))
/// is_some(get(v, i)) => unwrap(get(v, i)) = select(data(v), i)
#[test]
#[timeout(30_000)]
fn test_7887_vec_bounds_spec() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun vec_len ((Array Int Int)) Int)
        (declare-fun vec_get ((Array Int Int) Int) Int)
        (declare-fun in_bounds ((Array Int Int) Int) Bool)
        (declare-const v (Array Int Int))
        (declare-const idx Int)
        ; in_bounds checks
        (assert (forall ((a (Array Int Int)) (i Int))
          (! (= (in_bounds a i) (and (>= i 0) (< i (vec_len a))))
             :pattern ((in_bounds a i)))))
        ; vec_get returns the element when in bounds
        (assert (forall ((a (Array Int Int)) (i Int))
          (! (=> (in_bounds a i) (= (vec_get a i) (select a i)))
             :pattern ((vec_get a i)))))
        ; Setup: len >= 1 and idx = 0
        (assert (>= (vec_len v) 1))
        (assert (= idx 0))
        (assert (in_bounds v idx))
        ; Store 42 at index 0
        (assert (= (select v 0) 42))
        ; Goal: vec_get(v, 0) = 42
        (assert (not (= (vec_get v idx) 42)))
        (check-sat)
        "#,
        "#7887: Vec bounds checking spec",
    );
}

/// #7887 pattern: HashMap contains/get consistency.
///
/// verification-consumer axiomatizes map operations:
/// contains(insert(m, k, v), k) = true
/// get(insert(m, k, v), k) = v
#[test]
#[timeout(30_000)]
fn test_7887_hashmap_insert_get_spec() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort Map 0)
        (declare-fun map_insert (Map Int Int) Map)
        (declare-fun map_get (Map Int) Int)
        (declare-fun map_contains (Map Int) Bool)
        (declare-const m Map)
        (declare-const k Int)
        (declare-const v Int)
        ; insert then contains: always true for the inserted key
        (assert (forall ((mm Map) (kk Int) (vv Int))
          (! (= (map_contains (map_insert mm kk vv) kk) true)
             :pattern ((map_insert mm kk vv)))))
        ; insert then get: returns the inserted value
        (assert (forall ((mm Map) (kk Int) (vv Int))
          (! (= (map_get (map_insert mm kk vv) kk) vv)
             :pattern ((map_insert mm kk vv)))))
        ; Insert k->42, then get k
        (assert (= v 42))
        (assert (not (= (map_get (map_insert m k v) k) 42)))
        (check-sat)
        "#,
        "#7887: HashMap insert/get spec",
    );
}

/// #7887 pattern: Result::map specification.
///
/// map(ok(v), f) = ok(f(v))
/// map(err(e), f) = err(e)
#[test]
#[timeout(30_000)]
fn test_7887_result_map_spec() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-sort Res 0)
        (declare-fun ok (Int) Res)
        (declare-fun err (Int) Res)
        (declare-fun is_ok (Res) Bool)
        (declare-fun result_map (Res) Res)
        (declare-fun transform (Int) Int)
        ; ok is_ok
        (assert (forall ((v Int)) (! (= (is_ok (ok v)) true) :pattern ((ok v)))))
        ; err is not ok
        (assert (forall ((e Int)) (! (= (is_ok (err e)) false) :pattern ((err e)))))
        ; map on ok applies transform
        (assert (forall ((v Int))
          (! (= (result_map (ok v)) (ok (transform v)))
             :pattern ((result_map (ok v))))))
        ; transform(5) = 10
        (assert (= (transform 5) 10))
        ; Goal: result_map(ok(5)) = ok(10)
        (assert (not (= (result_map (ok 5)) (ok 10))))
        (check-sat)
        "#,
        "#7887: Result::map spec",
    );
}

// ============================================================================
// Combined patterns: realistic verification-consumer VCs
// ============================================================================

/// Combined pattern: Array initialization loop with wrapping index.
///
/// Models a loop that initializes an array with wrapping arithmetic index:
/// for i in 0..n: arr[wrapping_add(base, i)] = default_val
/// After the loop, arr[wrapping_add(base, 0)] should equal default_val.
#[test]
#[timeout(30_000)]
fn test_combined_array_init_wrapping() {
    expect_unsat(
        r#"
        (set-logic AUFLIA)
        (declare-fun wrapping_add (Int Int) Int)
        (declare-const arr (Array Int Int))
        (declare-const arr2 (Array Int Int))
        (declare-const base Int)
        (declare-const default_val Int)
        ; wrapping_add axiom
        (assert (forall ((a Int) (b Int))
          (! (= (wrapping_add a b) (mod (+ a b) 256))
             :pattern ((wrapping_add a b)))))
        ; arr2 is arr with arr2[wrapping_add(base, 0)] = default_val
        (assert (= arr2 (store arr (wrapping_add base 0) default_val)))
        ; Goal: select(arr2, wrapping_add(base, 0)) = default_val
        (assert (not (= (select arr2 (wrapping_add base 0)) default_val)))
        (check-sat)
        "#,
        "combined: array init with wrapping index",
    );
}

/// Combined pattern: verification-consumer push/pop refutation with quantified axioms.
///
/// Models verification-consumer's primary verification pattern: assert background axioms,
/// push, assert VC negation, check-sat (expect UNSAT for valid VCs).
#[test]
#[timeout(30_000)]
fn test_combined_push_pop_refutation() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun Q (S) Bool)
        (declare-fun f (S) S)
        (declare-const a S)
        ; Background axioms
        (assert (forall ((x S)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
        (assert (forall ((x S)) (! (=> (P x) (Q x)) :pattern ((P x)))))
        ; VC: P(a) => Q(f(a))
        (push 1)
        (assert (P a))
        (assert (not (Q (f a))))
        (check-sat)
        (pop 1)
    "#;
    let commands = parse(smt).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let check_result = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .expect("should have a check-sat result");
    assert_eq!(
        check_result.trim(),
        "unsat",
        "combined: push/pop refutation should be UNSAT"
    );
}

/// Soundness check: make sure SAT formulas are not falsely reported as UNSAT.
///
/// This is the complement of the UNSAT tests above. If the fixes over-eagerly
/// strengthen E-matching, they could produce false UNSAT results. We verify
/// that genuinely satisfiable formulas do not return UNSAT.
///
/// Note: The solver may return `unknown` for AUFLIA formulas with quantifiers
/// because E-matching is inherently incomplete. This is sound. The key
/// invariant is that `unsat` is never returned for satisfiable formulas.
#[test]
#[timeout(30_000)]
fn test_soundness_sat_with_quantifiers() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun P (S) Bool)
        (declare-fun f (S) S)
        (declare-const a S)
        ; P closed under f
        (assert (forall ((x S)) (! (=> (P x) (P (f x))) :pattern ((P x)))))
        ; P(a) holds
        (assert (P a))
        ; This is satisfiable: P(a) and P(f(a)) are both true
        (check-sat)
    "#;
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert!(
        matches!(result, SolverOutcome::Sat | SolverOutcome::Unknown),
        "soundness: SAT formula with quantifiers must not return UNSAT, got {result:?}",
    );
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "soundness: SAT formula must never return UNSAT"
    );
}

/// Soundness check: wrapping arithmetic SAT case.
///
/// wrapping_add(200, 100) is 44 (300 mod 256), not 300.
/// Asserting it equals 44 is consistent with the wrapping_add axiom.
///
/// Note: With quantifiers containing `mod`, the solver may return Unknown
/// because model validation cannot verify universally quantified assertions.
/// The key invariant is that UNSAT is never returned for satisfiable formulas.
/// Both SAT and Unknown are acceptable here. (#7979)
#[test]
#[timeout(30_000)]
fn test_soundness_wrapping_sat() {
    let result = run_executor_smt_with_timeout(
        r#"
        (set-logic AUFLIA)
        (declare-fun wrapping_add (Int Int) Int)
        (assert (forall ((a Int) (b Int))
          (! (= (wrapping_add a b) (mod (+ a b) 256))
             :pattern ((wrapping_add a b)))))
        ; This is satisfiable
        (assert (= (wrapping_add 200 100) 44))
        (check-sat)
        "#,
        30,
    )
    .expect("execution should succeed");
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "soundness: SAT formula must never return UNSAT"
    );
}

// ============================================================================
// #7884: Bool-sorted UF with carry chain integer arithmetic (QF_UFLIA)
// ============================================================================
//
// The verification-consumer regression involved QF_UFLIA formulas where a Bool-sorted UF
// application (e.g., nonzero_inv(wrapping_add_u8(a,b))) has a definitional
// equality connecting it to an arithmetic predicate. The carry chain encoding
// (a + b = 256*k + result, k in {0,1}) introduces a variable `k` that the
// LRA solver may assign a fractional value (1/256). When the N-O combiner
// returns NeedModelEquality for interface terms and those equalities are
// already encoded ("stale"), the split loop treated them as Sat, skipping
// the integrality check for `k`.
//
// Fix: check_inner() now checks integer variable integrality before
// forwarding NeedModelEquality/NeedModelEqualities from LRA.

/// #7884 regression: Bool-sorted UF with carry chain and three nonzero_inv axioms.
///
/// This is the exact pattern that triggered the model validation failure:
/// nonzero_inv(wrapping_add_u8(a,b)) combined with the carry chain encoding
/// for wrapping u8 addition.
#[test]
#[timeout(30_000)]
fn test_7884_bool_uf_carry_chain_nonzero() {
    expect_unsat(
        r#"
        (set-logic QF_UFLIA)
        (declare-fun nonzero_inv (Int) Bool)
        (declare-fun wrapping_add_u8 (Int Int) Int)

        (declare-const a Int)
        (declare-const b Int)
        (declare-const result Int)
        (declare-const k Int)

        ; u8 bounds
        (assert (>= a 0))
        (assert (<= a 255))
        (assert (= b 0))
        (assert (>= result 0))
        (assert (<= result 255))
        (assert (>= k 0))
        (assert (<= k 1))

        ; Wrapping add carry chain: a + b = 256*k + result
        (assert (= (+ a b) (+ (* 256 k) result)))

        ; UF link
        (assert (= (wrapping_add_u8 a b) result))

        ; nonzero_inv axioms for each relevant value
        (assert (= (nonzero_inv a) (not (= a 0))))
        (assert (= (nonzero_inv result) (not (= result 0))))
        ; Key: invariant for the UF application
        (assert (= (nonzero_inv (wrapping_add_u8 a b)) (not (= (wrapping_add_u8 a b) 0))))

        ; Precondition: a is nonzero
        (assert (nonzero_inv a))

        ; Negated postcondition: wrapping_add_u8(a, 0) is zero
        (assert (not (nonzero_inv (wrapping_add_u8 a b))))

        (check-sat)
        "#,
        "#7884: Bool UF carry chain with three nonzero_inv axioms",
    );
}

/// #7884 variant: simpler version without the third nonzero_inv axiom.
/// This was working before the fix but validates the carry chain itself.
#[test]
#[timeout(30_000)]
fn test_7884_carry_chain_simple() {
    expect_unsat(
        r#"
        (set-logic QF_UFLIA)
        (declare-fun nonzero_inv (Int) Bool)
        (declare-fun wrapping_add_u8 (Int Int) Int)

        (declare-const a Int)
        (declare-const b Int)
        (declare-const result Int)
        (declare-const k Int)

        (assert (>= a 0))
        (assert (<= a 255))
        (assert (= b 0))
        (assert (>= result 0))
        (assert (<= result 255))
        (assert (>= k 0))
        (assert (<= k 1))

        (assert (= (+ a b) (+ (* 256 k) result)))
        (assert (= (wrapping_add_u8 a b) result))

        (assert (= (nonzero_inv a) (not (= a 0))))
        (assert (= (nonzero_inv result) (not (= result 0))))

        (assert (nonzero_inv a))
        (assert (not (nonzero_inv result)))

        (check-sat)
        "#,
        "#7884: carry chain simple variant without UF nonzero_inv",
    );
}

/// #7884 soundness check: SAT variant where a=0 is allowed.
#[test]
#[timeout(30_000)]
fn test_7884_carry_chain_sat_variant() {
    expect_sat(
        r#"
        (set-logic QF_UFLIA)
        (declare-fun nonzero_inv (Int) Bool)
        (declare-fun wrapping_add_u8 (Int Int) Int)

        (declare-const a Int)
        (declare-const b Int)
        (declare-const result Int)
        (declare-const k Int)

        (assert (>= a 0))
        (assert (<= a 255))
        (assert (>= b 0))
        (assert (<= b 255))
        (assert (>= result 0))
        (assert (<= result 255))
        (assert (>= k 0))
        (assert (<= k 1))

        (assert (= (+ a b) (+ (* 256 k) result)))
        (assert (= (wrapping_add_u8 a b) result))

        (assert (= (nonzero_inv a) (not (= a 0))))

        ; a could be 0, result could be 0
        (assert (= result 0))

        (check-sat)
        "#,
        "#7884 soundness: SAT variant where a=0 is permitted",
    );
}

/// #7884 variant: Two carry chains with shared variable.
///
/// Tests the fix handles multiple fractional carry variables correctly.
#[test]
#[timeout(30_000)]
fn test_7884_double_carry_chain() {
    expect_unsat(
        r#"
        (set-logic QF_UFLIA)
        (declare-fun nonzero_inv (Int) Bool)
        (declare-fun wrapping_add_u8 (Int Int) Int)

        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const r1 Int)
        (declare-const r2 Int)
        (declare-const k1 Int)
        (declare-const k2 Int)

        ; u8 bounds
        (assert (>= a 0)) (assert (<= a 255))
        (assert (= b 0))
        (assert (= c 0))
        (assert (>= r1 0)) (assert (<= r1 255))
        (assert (>= r2 0)) (assert (<= r2 255))
        (assert (>= k1 0)) (assert (<= k1 1))
        (assert (>= k2 0)) (assert (<= k2 1))

        ; Carry chain 1: a + b = 256*k1 + r1
        (assert (= (+ a b) (+ (* 256 k1) r1)))
        ; Carry chain 2: a + c = 256*k2 + r2
        (assert (= (+ a c) (+ (* 256 k2) r2)))

        (assert (= (nonzero_inv a) (not (= a 0))))
        (assert (= (nonzero_inv r1) (not (= r1 0))))

        ; Precondition: a nonzero
        (assert (nonzero_inv a))
        ; Negated postcondition: r1 = 0
        (assert (not (nonzero_inv r1)))

        (check-sat)
        "#,
        "#7884: double carry chain with two fractional k variables",
    );
}
