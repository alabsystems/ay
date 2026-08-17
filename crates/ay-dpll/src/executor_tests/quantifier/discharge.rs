// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rank-9 quantifier discharge for verification-consumer (2026-07-08 wishlist plan).
//!
//! verification-consumer sends raw EXISTENTIAL preconditions and quantified Mapping/FMap
//! style axioms (pointwise UF definitions, often guarded). These tests pin the
//! three rank-9 steps:
//!
//! 1. Witness-directed instantiation for (negated) existentials over a
//!    provably-complete bounded Int range (extended finite-domain expansion,
//!    `skolemize/finite_domain.rs`).
//! 2. The CEGQI div/mod CE-var bail lifted for NONZERO CONSTANT divisors
//!    (`quantifier_loop/cegqi_refinement.rs`).
//! 3. The generalized pointwise-materializable UF-definition SAT certificate:
//!    guarded definitions, the linear-Int fragment, distinct-head discipline
//!    (`executor/mbqi.rs`, `quantifier_loop/mod.rs`, `result_mapping.rs`).
//!
//! Soundness rules pinned throughout: Sat only with a verified model
//! extension, Unsat only from a complete finite range or a real instantiation
//! contradiction; Unknown is always acceptable — so the negative tests assert
//! `never sat` / `never unsat` rather than a forced decision.

use super::*;

// ---------------------------------------------------------------------------
// (a) Satisfiable existential-precondition shapes.
// ---------------------------------------------------------------------------

/// The literal verification-consumer existential-precondition shape with a free Bool UF:
/// `exists x in [0,10]. P(x)` is satisfiable (choose P(0) := true). Decided
/// by bounded finite-domain expansion; must never be unsat.
#[test]
fn test_exists_bounded_bool_uf_precondition_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (exists ((x Int)) (and (<= 0 x) (<= x 10) (P x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "satisfiable existential refuted");
    assert_eq!(outputs, vec!["sat"]);
}

/// Decided-sat with PURE ARITHMETIC where the witness is verifiable:
/// x := 697 satisfies the skolemized body, and the model is validated.
#[test]
fn test_exists_bounded_pure_arith_witness_sat() {
    let input = r#"
        (set-logic LIA)
        (assert (exists ((x Int)) (and (<= 0 x) (<= x 1000) (= (+ x 3) 700))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

/// Rank-9 step 1: mid-band range (256 < 501 <= 512) plus a pointwise Bool-UF
/// definition pinning the witness inside the range. Previously
/// `Unknown(QuantifierUnhandled)` (the range exceeded the 256 finite-domain
/// budget and MBQI cannot evaluate `P` at fresh points); the extended
/// expansion + definitional instances decide it: x := 300 is a VERIFIED
/// witness (the ground model satisfies every expanded disjunct instance).
#[test]
fn test_exists_midrange_bool_uf_with_definition_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((v Int)) (= (P v) (= v 300))))
        (assert (exists ((x Int)) (and (<= 0 x) (<= x 500) (P x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    let reason = exec.unknown_reason();
    assert_ne!(outputs, vec!["unsat"], "satisfiable existential refuted");
    assert_eq!(outputs, vec!["sat"], "reason={reason:?}");
}

/// Rank-9 step 3: WIDE range (past any expansion budget) plus a pointwise
/// definition — the Skolemized ground core is Sat (sk := 700) and the
/// generalized model-backed UF-definition certificate (linear-Int fragment)
/// extends the model over the definition. Previously Unknown.
#[test]
fn test_exists_wide_bool_uf_with_definition_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((v Int)) (= (P v) (= v 700))))
        (assert (exists ((x Int)) (and (<= 0 x) (<= x 1000000) (P x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "satisfiable existential refuted");
    // #quantified-model-gate: satisfiable, but the emitted `P` table
    // collapses to a constant body that falsifies `∀v. P(v) ⇔ v=700`; the
    // gate fail-closes to `unknown` rather than print a falsifying witness.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat (with a valid model) or fail-closed unknown, got {outputs:?}"
    );
}

// ---------------------------------------------------------------------------
// (b) FALSE variants: provably-empty / witness-free finite ranges.
// ---------------------------------------------------------------------------

/// Provably-EMPTY finite range: `[5,3]` has no elements, so the existential
/// is false regardless of `P`. Both the empty-range equivalence fold and the
/// Skolemized ground core decide unsat; it must never be sat.
#[test]
fn test_exists_empty_range_bool_uf_unsat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (exists ((x Int)) (and (<= 5 x) (<= x 3) (P x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["sat"], "empty-range existential accepted");
    assert_eq!(outputs, vec!["unsat"]);
}

/// Mid-band range whose definition places the only P-point OUTSIDE the
/// range: exhausting the provably-complete finite range without a witness is
/// a sound refutation of the existential.
#[test]
fn test_exists_midrange_bool_uf_no_witness_unsat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((v Int)) (= (P v) (= v 1000))))
        (assert (exists ((x Int)) (and (<= 0 x) (<= x 500) (P x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["sat"], "witness-free existential accepted");
    assert_eq!(outputs, vec!["unsat"]);
}

/// Wide-range FALSE variant: the definitional instance at the Skolem constant
/// (`P(sk) = (sk = 2000000)`) contradicts the range bound, a real
/// instantiation contradiction.
#[test]
fn test_exists_wide_bool_uf_no_witness_unsat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((v Int)) (= (P v) (= v 2000000))))
        (assert (exists ((x Int)) (and (<= 0 x) (<= x 1000000) (P x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["sat"], "witness-free existential accepted");
    assert_eq!(outputs, vec!["unsat"]);
}

/// NEGATED existential over a mid-band range with a forced witness inside:
/// `P(200)` witnesses the existential, so its negation refutes. This is the
/// NNF'd triggerless-forall shape from the plan's root cause.
#[test]
fn test_neg_exists_midrange_witness_inside_unsat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (P 200))
        (assert (not (exists ((x Int)) (and (<= 0 x) (<= x 300) (P x)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "witnessed negated existential accepted"
    );
    assert_eq!(outputs, vec!["unsat"]);
}

/// NEGATED existential, witness OUTSIDE the range: satisfiable (P can be
/// false on all of [0,300]); the complete expansion certifies the model.
#[test]
fn test_neg_exists_midrange_witness_outside_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (P 400))
        (assert (not (exists ((x Int)) (and (<= 0 x) (<= x 300) (P x)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "satisfiable negated existential refuted"
    );
    assert_eq!(outputs, vec!["sat"]);
}

/// Wide negated existential with a definitional witness inside the range:
/// decided unsat via enumerative/definitional instantiation at the visible
/// constant (700) — a real instantiation contradiction, no enumeration of the
/// full range required (regression guard; already decided before rank-9).
#[test]
fn test_neg_exists_wide_definitional_witness_unsat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((v Int)) (= (P v) (= v 700))))
        (assert (not (exists ((x Int)) (and (<= 0 x) (<= x 1000000) (P x)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "witnessed negated existential accepted"
    );
    assert_eq!(outputs, vec!["unsat"]);
}

// ---------------------------------------------------------------------------
// (c) Generalized pointwise-UF-definition certificate.
// ---------------------------------------------------------------------------

/// GUARDED definition `forall v. (0 <= v <= 1000000) => f(v) = v + 1` with a
/// satisfiable ground core (`f(a) = 5`, `a` in `[0,10]` forces `a = 4`). The
/// generalized certificate accepts the guarded shape over the linear-Int
/// fragment; previously Unknown(QuantifierCegqiIncomplete).
#[test]
fn test_guarded_uf_definition_certificate_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun a () Int)
        (assert (forall ((v Int)) (=> (and (<= 0 v) (<= v 1000000)) (= (f v) (+ v 1)))))
        (assert (<= 0 a))
        (assert (<= a 10))
        (assert (= (f a) 5))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "satisfiable guarded definition refuted"
    );
    // #quantified-model-gate: the formula is satisfiable, but the emitted
    // finite-table model (constant `else`) FALSIFIES the million-point
    // guarded definition, so the quantified model gate fail-closes the
    // unmaterialized certificate to `unknown`. `sat` is acceptable ONLY once
    // the completion is materialized into a valid printable model.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat (with a valid model) or fail-closed unknown, got {outputs:?}"
    );
}

/// Control for the guarded certificate: the same definition with a ground
/// value OFF the definition line inside the guard is a genuine contradiction.
#[test]
fn test_guarded_uf_definition_violated_unsat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun a () Int)
        (assert (forall ((v Int)) (=> (and (<= 0 v) (<= v 1000000)) (= (f v) (+ v 1)))))
        (assert (<= 0 a))
        (assert (<= a 10))
        (assert (= (f a) 500))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

/// UNGUARDED Int definition (`forall v. f(v) = v + 1`, ground `f(a) = 5`):
/// the linear-Int fragment extension alone decides this (the definition is a
/// CEGQI candidate whose CE lemma drives the first solve UNSAT; the
/// certificate now decides the ground-only Sat). Previously Unknown.
#[test]
fn test_unguarded_int_uf_definition_certificate_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun a () Int)
        (assert (forall ((v Int)) (= (f v) (+ v 1))))
        (assert (= (f a) 5))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "satisfiable definition refuted");
    // #quantified-model-gate: satisfiable, but a finite-table model with a
    // constant `else` cannot satisfy `∀v. f(v)=v+1`; the gate fail-closes the
    // unmaterialized certificate to `unknown` rather than print a falsifying
    // witness.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat (with a valid model) or fail-closed unknown, got {outputs:?}"
    );
}

/// NON-definition lookalike the certificate must NOT accept: the "guard"
/// applies an uninterpreted predicate `R` to the binder (not interpreted-pure),
/// so `forall v. R(v) \/ f(v) = 0` is a coupled CONSTRAINT, not a pointwise
/// definition. Jointly with `R = (= w 9)` and `f == 1` the problem is UNSAT
/// at any v outside {9} — but the clash lives at NON-ground points, so a
/// wrongly-accepted certificate would mint sat from the (satisfiable-at-
/// ground-points) core. Must never answer sat.
#[test]
fn test_impure_guard_lookalike_never_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun R (Int) Bool)
        (assert (forall ((v Int)) (or (R v) (= (f v) 0))))
        (assert (forall ((w Int)) (= (R w) (= w 9))))
        (assert (forall ((u Int)) (= (f u) 1)))
        (assert (= (f 9) 1))
        (assert (R 9))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "impure-guard lookalike certified as a definition (wrong SAT)"
    );
}

/// Two GUARDED definitions of the SAME symbol with overlapping guards clash
/// at v = 0 (`f(0) = 1` and `f(0) = 2`) — a point no ground application
/// covers, so the per-symbol materialization argument fails and the
/// distinct-head discipline must reject the certificate. Truly UNSAT; must
/// never answer sat.
#[test]
fn test_same_symbol_guarded_definitions_never_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((v Int)) (or (not (<= 0 v)) (= (f v) 1))))
        (assert (forall ((v Int)) (or (not (<= v 0)) (= (f v) 2))))
        (assert (= (f 5) 1))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "same-symbol guarded definitions certified jointly (wrong SAT)"
    );
}

/// A recursive lookalike (`f` reappears on the value side) is a fixpoint
/// constraint, not a pointwise assignment; with `f(3) = 7` and
/// `forall v. (0 <= v) => f(v) = f(v+1) + 1` ... kept simple: the recursive
/// shape must not be certified sat when it genuinely contradicts. Here
/// `forall v. f(v) = f(v) + 1` is UNSAT outright.
#[test]
fn test_recursive_definition_lookalike_never_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((v Int)) (= (f v) (+ (f v) 1))))
        (assert (= (f 0) 0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "recursive fixpoint certified (wrong SAT)"
    );
}

// ---------------------------------------------------------------------------
// (d) Constant-divisor CEGQI (step 2).
// ---------------------------------------------------------------------------

mod division;
