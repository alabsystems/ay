// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Capability regression: AY must DERIVE `unsat` on a quantified UFBV `fixpoint`
//! check whose universal is genuinely violated (#quantified-premise-forced).
//!
//! Minimized from the SV-COMP `wintersteiger fmsd13 fixpoint` benchmarks (20
//! UFBV + 1 UFNIRA of which AY once answered a wrong `sat` — see the sibling
//! `ufbv_deferred_selfcheck_failclosed` soundness test). The body is
//! `∀xs. (premise(xs) ⟹ conclusion(xs, UF))`: the `premise` is an SSA equality
//! chain that PINS the binders (a0=1, a1=2, a2=3), and the `conclusion` defines
//! uninterpreted functions pointwise (fa0/fa1/fa2 = the same computation) and
//! then asserts a FIXPOINT disjunction `(or (= a2 (fa0 …)) (= a2 (fa1 …)))`.
//! At the pinned point a2=3 equals neither fa0=1 nor fa1=2, so the universal is
//! false ⇒ UNSAT (z3 and cvc5 agree).
//!
//! Root cause of the former wrong `sat`: the UF-completion SAT certificate
//! (`quantifiers_supported_by_uf_completion`) materialized the pointwise UF
//! definitions and granted `sat`; its MBQI validator
//! (`disambiguate_cegqi_valid_via_mbqi`) only instantiated single-`Int`-binder
//! foralls over a value window, so it silently skipped this multi-`BitVec`-binder
//! shape and never found the refuting instance. Fixed by
//! `premise_forced_binder_refutation`: use the recovered premise only to obtain
//! concrete BitVector model values, substitute those exact literals into the
//! whole universal body, and independently refute that standalone ground
//! instance. The premise is never added to the proof problem. Default mode must
//! now DECIDE `unsat`; `--self-check` may stay `unknown` until the proof lane
//! certifies the reduction.

/// The fully-collapsing fixpoint check MUST be decided `unsat` in default mode.
#[test]
fn ufbv_fixpoint_premise_forced_is_unsat() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa1 a2 a1 a0)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "quantified UFBV fixpoint check is UNSAT (z3, cvc5 agree; the universal \
         is violated at the premise-pinned point a2=3 ≠ fa0=1, fa1=2) — AY must \
         derive it via premise-forced refutation, not answer a wrong `sat`; \
         got {results:?}"
    );
}

/// SOUNDNESS guard: the SAME shape made GENUINELY SAT (the fixpoint disjunction
/// now includes the reached value, `(= a2 (fa2 …))` with a2=fa2=3) must NEVER be
/// refuted — the premise-forced refutation must not manufacture a wrong `unsat`.
#[test]
fn ufbv_fixpoint_satisfiable_variant_is_never_unsat() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa2 a2 a1 a0)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "this fixpoint check IS satisfiable (a2=3 = fa2=3 witnesses the \
         disjunction) — the premise-forced refutation must never manufacture a \
         wrong `unsat`; got {results:?}"
    );
}

/// SOUNDNESS guard: an uninterpreted function whose user-visible name merely
/// starts with `bv` is not a BitVector theory operator.  The ground assertions
/// make `bvshadow` constantly zero over the complete one-bit domain, so the
/// universal's premise is always false and the formula is satisfiable.
///
/// A premise-refutation classifier that trusts the `bv*` spelling instead of
/// declaration identity can incorrectly treat `(bvshadow x)` as interpreted,
/// assert the otherwise-vacuous premise at a fresh constant, and manufacture
/// `unsat`.
#[test]
fn user_declared_bv_prefix_in_premise_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun bvshadow ((_ BitVec 1)) (_ BitVec 1))
        (assert (= (bvshadow #b0) #b0))
        (assert (= (bvshadow #b1) #b0))
        (assert (forall ((x (_ BitVec 1)))
          (=> (= (bvshadow x) #b1) false)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "the exhaustive ground table makes the universal vacuously true; a \
         user-declared `bvshadow` must not be classified as an interpreted BV \
         operator by spelling alone; got {results:?}"
    );
}

/// Stronger declaration-identity adversary: the body also carries a genuine UF
/// conclusion, ensuring the UF-completion validation path examines the
/// universal.  `bvtrap` is false at every value of the complete one-bit domain,
/// so this formula is satisfiable.
#[test]
fn user_declared_bv_prefix_with_uf_conclusion_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun bvtrap ((_ BitVec 1)) Bool)
        (declare-fun p ((_ BitVec 1)) Bool)
        (assert (not (bvtrap #b0)))
        (assert (not (bvtrap #b1)))
        (assert (forall ((x (_ BitVec 1)))
          (=> (bvtrap x) (p x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "`bvtrap` is a user UF that is false on the complete one-bit domain, \
         making the universal vacuously true; got {results:?}"
    );
}

/// SOUNDNESS guard: integer division by zero has a fixed-but-arbitrary value in
/// each SMT model.  The ground assertion chooses `(div 0 0) != 0`, making the
/// universal premise false at its only pinned point and the whole formula SAT.
/// An isolated premise solve may choose the different legal value zero, but
/// that model cannot be mixed with the ground model to manufacture UNSAT.
#[test]
fn underspecified_division_in_premise_is_never_refuted() {
    let smt = r#"
        (set-logic UFNIA)
        (declare-fun p (Int) Bool)
        (assert (distinct (div 0 0) 0))
        (assert (forall ((x Int))
          (=> (and (= x 0) (= (div x 0) 0)) (p x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "div-by-zero is underspecified and the asserted interpretation makes \
         the universal vacuous; got {results:?}"
    );
}

/// SOUNDNESS guard: isolated premise satisfiability over an uninterpreted sort
/// may choose a larger carrier than the original model.  Here a singleton
/// carrier satisfies both universals because every `distinct x y` premise is
/// false.  A premise probe must not borrow a two-element carrier and combine it
/// with the singleton-only outer problem.
#[test]
fn model_varying_binder_carrier_is_never_refuted() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-fun p (U U) Bool)
        (assert (forall ((z U)) (= z a)))
        (assert (forall ((x U) (y U))
          (=> (distinct x y) (and (p x y) (not (p x y))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "a singleton U is a model, so an isolated premise probe must not assume \
         a larger uninterpreted carrier; got {results:?}"
    );
}

/// SOUNDNESS guard: a universal below a disjunction is not entailed by the
/// problem.  Choosing `g = true` satisfies the assertion regardless of the
/// deliberately contradictory universal branch.
#[test]
fn nonconjunctive_forall_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-const g Bool)
        (declare-fun p ((_ BitVec 1)) Bool)
        (assert (or g
          (forall ((x (_ BitVec 1)))
            (=> (= x x) (and (p x) (not (p x)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "g=true satisfies the disjunction; a nested forall is not a top-level \
         consequence and its instance cannot justify UNSAT; got {results:?}"
    );
}

/// Exercise the De Morgan candidate-extraction arm explicitly. `bvtrap` is a
/// user UF, not an interpreted BV operator, and is false over the complete
/// one-bit domain. The disjunction is therefore true for every binder value.
#[test]
fn de_morgan_user_bv_prefix_candidate_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun bvtrap ((_ BitVec 1)) Bool)
        (declare-fun p ((_ BitVec 1)) Bool)
        (assert (not (bvtrap #b0)))
        (assert (not (bvtrap #b1)))
        (assert (forall ((x (_ BitVec 1)))
          (or (not (bvtrap x)) (p x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "the De Morgan partition is candidate synthesis only; a user `bv*` UF \
         cannot justify UNSAT; got {results:?}"
    );
}

/// The disposable premise probes must not register their fresh constants in
/// the user executor. Repeated SAT checks exercise the same capability twice;
/// neither visible model may contain the private qpf prefix.
#[test]
fn repeated_sat_checks_do_not_leak_qpf_symbols() {
    let smt = r#"
        (set-logic UFBV)
        (set-option :produce-models true)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa2 a2 a1 a0)))))))
        (check-sat)
        (get-model)
        (check-sat)
        (get-model)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results.iter().filter(|r| r.as_str() == "sat").count(),
        2,
        "the satisfiable variant must remain stable across repeated checks; got {results:?}"
    );
    assert!(
        results.iter().all(|r| !r.contains("__ay_qpf")),
        "disposable premise symbols must never escape into a visible model; got {results:?}"
    );
}

/// Proof/self-check mode must never emit a satisfiable answer for the false
/// fixpoint universal. It may remain `unknown` until this reduction has an
/// authored `forall_inst` proof, or emit `unsat` only through the strict
/// self-certification funnel.
#[test]
fn fixpoint_selfcheck_never_emits_sat() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa1 a2 a1 a0)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_selfcheck_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "self-check may certify UNSAT or fail closed to unknown, never claim SAT \
         for the false universal; got {results:?}"
    );
}
