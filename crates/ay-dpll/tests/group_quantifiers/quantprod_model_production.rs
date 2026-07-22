// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! #quantprod model-production battery: the measured z3-decides / AY-unknown
//! quantifier families now DECIDE, and their wrong-fact twins refute.
//!
//! Five fixes, one per family, each pinned here with its true-fact probe AND
//! its flipped-fact twin (a fix that only flips the headline probe while the
//! negation stays wrong is a wrong verdict — handoff §2.2):
//!
//! * **A (LIA guarded forall, linear bound on a constant):** the deep-QE
//!   prepass used to Cooper-eliminate the forall into constant-divisor `mod`
//!   atoms the ground LIA lane cannot decide, pre-empting the exact bounded
//!   finite-domain expansion. `deep_qe` now skips assertions the expansion
//!   provably grounds (`bounded_expansion_grounds_all_quantifiers`).
//! * **F (UFLIA 2-var monotonicity + endpoint pins):** per-var literal bound
//!   extraction could not see bounds holding only transitively through
//!   binder-binder guards (`0<=x ∧ x<y ∧ y<=N`). The guarded-box analysis
//!   (`analyze_bounded_int_box_forall`) closes the chains and expands the
//!   FULL or-body over the entailed box — an exact equivalence.
//! * **G (LRA `∀x∃y` on [0,1]):** the QE engine decided the shape but its
//!   DNF/elimination abort constants were too small; raised under the
//!   existing wall-clock interrupt poll.
//! * **g2 (const-array equality under forall):** `select` over a literal
//!   const-array (direct or pinned by a retained ground equality) folds to
//!   the element inside quantified assertions, making the forall vacuous.
//! * **g3 (definitional forall over a declared UF):** adopted as a macro at
//!   the frontend (z3's macro-finder equivalent) with the definitional
//!   `(define-fun …)` model entry.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

fn expect(smt: &str, expected: SolverOutcome, label: &str) {
    let result = run_executor_smt_with_timeout(smt, 60).expect("execution should succeed");
    assert_eq!(result, expected, "{label}: got {result:?}");
}

// ---------------------------------------------------------------- family A

/// A11: `a <= -5x+4` on `x ∈ [0,100]` pins `a <= -496`; `a >= -497` is SAT.
/// Cooper's adoption used to leave this at `unknown (unsupported arithmetic)`.
#[test]
fn quantprod_a_guarded_forall_linear_bound_sat() {
    expect(
        r#"(set-logic LIA)
(declare-const a Int)
(assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 100)) (<= a (+ (* -5 x) 4)))))
(assert (>= a -497))
(check-sat)"#,
        SolverOutcome::Sat,
        "A guarded-forall true-fact",
    );
}

/// Twin: tightening the free bound past the true minimum (-496) must refute.
#[test]
fn quantprod_a_guarded_forall_linear_bound_twin_unsat() {
    expect(
        r#"(set-logic LIA)
(declare-const a Int)
(assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 100)) (<= a (+ (* -5 x) 4)))))
(assert (>= a -495))
(check-sat)"#,
        SolverOutcome::Unsat,
        "A guarded-forall wrong-fact twin",
    );
}

// ---------------------------------------------------------------- family F

/// F00: non-strict monotonicity with equal endpoint pins is SAT (constant f).
#[test]
fn quantprod_f_monotone_equal_pins_sat() {
    expect(
        r#"(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y) (<= y 5)) (<= (f x) (f y)))))
(assert (= (f 0) -2))
(assert (= (f 5) -2))
(check-sat)"#,
        SolverOutcome::Sat,
        "F non-strict equal pins",
    );
}

/// F01: STRICT monotonicity forces `f(5) >= f(0)+5 = 3`, but the pin says 2.
/// The tainted-instantiation path used to discard this genuine refutation.
#[test]
fn quantprod_f_strict_gap_too_small_unsat() {
    expect(
        r#"(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y) (<= y 5)) (< (f x) (f y)))))
(assert (= (f 0) -2))
(assert (= (f 5) 2))
(check-sat)"#,
        SolverOutcome::Unsat,
        "F strict insufficient gap",
    );
}

/// F01 flipped: gap 5 exactly fits a strict chain — SAT.
#[test]
fn quantprod_f_strict_gap_exact_sat() {
    expect(
        r#"(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y) (<= y 5)) (< (f x) (f y)))))
(assert (= (f 0) -2))
(assert (= (f 5) 3))
(check-sat)"#,
        SolverOutcome::Sat,
        "F strict exact gap twin",
    );
}

/// F05: N=60 — the 60x60 entailed box needs the extended
/// `MAX_GUARDED_INT_BOX_COMBOS` budget; uniform-in-N is the point.
#[test]
fn quantprod_f_monotone_large_n_sat() {
    expect(
        r#"(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y) (<= y 60)) (<= (f x) (f y)))))
(assert (= (f 0) -2))
(assert (= (f 60) -2))
(check-sat)"#,
        SolverOutcome::Sat,
        "F large-N equal pins",
    );
}

/// F05 twin: a descending endpoint under non-strict monotonicity refutes.
#[test]
fn quantprod_f_monotone_large_n_twin_unsat() {
    expect(
        r#"(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y) (<= y 60)) (<= (f x) (f y)))))
(assert (= (f 0) -2))
(assert (= (f 60) -3))
(check-sat)"#,
        SolverOutcome::Unsat,
        "F large-N wrong-fact twin",
    );
}

// ---------------------------------------------------------------- family G

/// G04: `∀x∈[0,1] ∃y∈[0,1]. x<=y<=x+1/2` — witnessed by `y=x`; the QE
/// prepass used to abort on its DNF-distribution caps.
#[test]
fn quantprod_g_forall_exists_box_sat() {
    expect(
        r#"(set-logic LRA)
(assert (forall ((x Real)) (=> (and (<= 0.0 x) (<= x 1.0))
  (exists ((y Real)) (and (<= 0.0 y) (<= y 1.0) (and (<= x y) (<= y (+ x (/ 1 2)))))))))
(check-sat)"#,
        SolverOutcome::Sat,
        "G forall-exists box",
    );
}

/// Twin: demanding a STRICTLY larger witness fails at the right endpoint
/// (`x=1` needs `y>1` inside `[0,1]`).
#[test]
fn quantprod_g_forall_exists_box_twin_unsat() {
    expect(
        r#"(set-logic LRA)
(assert (forall ((x Real)) (=> (and (<= 0.0 x) (<= x 1.0))
  (exists ((y Real)) (and (<= 0.0 y) (<= y 1.0) (and (< x y) (<= y (+ x (/ 1 2)))))))))
(check-sat)"#,
        SolverOutcome::Unsat,
        "G forall-exists strict twin",
    );
}

// ---------------------------------------------------------------- family g2

/// Const-array equality + pointwise forall: the select fold makes the
/// quantifier vacuous instead of tripping the MBQI-unsafe array fail-close.
#[test]
fn quantprod_g2_const_array_pointwise_forall_sat() {
    expect(
        r#"(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(assert (= a ((as const (Array Int Int)) 0)))
(assert (forall ((x Int)) (= (select a x) 0)))
(check-sat)"#,
        SolverOutcome::Sat,
        "g2 const-array pointwise forall",
    );
}

/// Twin: a conflicting concrete read refutes through the retained pin.
#[test]
fn quantprod_g2_const_array_conflicting_read_unsat() {
    expect(
        r#"(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(assert (= a ((as const (Array Int Int)) 0)))
(assert (forall ((x Int)) (= (select a x) 0)))
(assert (= (select a 5) 1))
(check-sat)"#,
        SolverOutcome::Unsat,
        "g2 conflicting read twin",
    );
}

// ---------------------------------------------------------------- family g3

/// Definitional forall over a declared UF adopts as a macro: the UFNIA
/// square definition + a consistent pin decides SAT.
#[test]
fn quantprod_g3_definitional_forall_sat() {
    expect(
        r#"(set-logic UFNIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f x) (* x x))))
(assert (= (f 4) 16))
(check-sat)"#,
        SolverOutcome::Sat,
        "g3 definitional forall",
    );
}

/// Twin: a pin contradicting the definition is a ground contradiction after
/// expansion (`16 = 17`).
#[test]
fn quantprod_g3_definitional_forall_twin_unsat() {
    expect(
        r#"(set-logic UFNIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f x) (* x x))))
(assert (= (f 4) 17))
(check-sat)"#,
        SolverOutcome::Unsat,
        "g3 definitional wrong-pin twin",
    );
}

/// The g3 model must carry the DEFINITIONAL interpretation (z3 parity): a
/// finite table cannot satisfy `forall x. f(x) = x*x`, so `(get-model)` has
/// to emit the adopted `define-fun` body.
#[test]
fn quantprod_g3_model_emits_definitional_interp() {
    use ay_dpll::Executor;
    use ay_frontend::parse;
    let smt = r#"(set-logic UFNIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f x) (* x x))))
(assert (= (f 4) 16))
(check-sat)
(get-model)"#;
    let commands = parse(smt).expect("parse");
    let mut executor = Executor::new();
    let outputs = executor.execute_all(&commands).expect("execute");
    let sat_line = outputs
        .iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
        .expect("verdict line");
    assert_eq!(sat_line.trim(), "sat", "g3 must decide sat");
    let model = outputs
        .iter()
        .find(|l| l.contains("(model"))
        .expect("model output");
    assert!(
        model.contains("define-fun f") && model.contains("(* x_0 x_0)"),
        "g3 model must define f by its definitional body, got: {model}"
    );
}

/// Adoption must FAIL CLOSED when the symbol was already used by an earlier
/// assertion: the pre-macro occurrence would otherwise constrain a
/// disconnected `f` (wrong-SAT source). `f(5) = 24` conflicts with the
/// definition, so the sound answers are `unsat` (if the engine refutes) or
/// `unknown` — never `sat`.
#[test]
fn quantprod_g3_pre_use_blocks_adoption_no_wrong_sat() {
    let smt = r#"(set-logic UFNIA)
(declare-fun f (Int) Int)
(assert (= (f 5) 24))
(assert (forall ((x Int)) (= (f x) (* x x))))
(check-sat)"#;
    let result = run_executor_smt_with_timeout(smt, 60).expect("execution should succeed");
    assert_ne!(
        result,
        SolverOutcome::Sat,
        "pre-adoption use of f must not produce a wrong SAT"
    );
}
