// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cardinal soundness spec: the syntactic UF-completion classifier must never
//! act as a SAT certificate (#ufbv-strict-uf-completion-no-coverage).
//!
//! At 0.5.0+build.6243 this regression was red: the strict leg proposed `sat`
//! without a coverage premise. The mandatory independent-model boundary now
//! withholds any such unconfirmed proposal in every mode, so this is a green
//! publication-soundness guard. The strict leg still needs real coverage to
//! recover a definitive answer instead of sound `unknown`.
//!
//! Ground truth needs no oracle. Instantiate the single universal at
//! `x = #x00000001`: the conjuncts demand `f(1) = 0` and `1 = f(1)`, hence
//! `1 = 0`. The universal is false, so the assertion set is UNSATISFIABLE. z3
//! 4.15.4 agrees. `sat` is therefore a wrong answer; `unsat` is ideal and
//! `unknown` is an acceptable sound incompleteness.
//!
//! WHY THIS IS SEPARATE from `ufbv_deferred_default_mode_wrong_sat.rs`: that file
//! guards corpus instances of the `(=> premise conclusion)` shape, which the
//! multi-point `premise_forced_binder_refutation` probe can refute by sampling
//! premise models. This body is a BARE CONJUNCTION with no premise, so that probe
//! declines by construction and cannot ever fix this case. The two files pin the
//! two search shapes; this one pins the bare-conjunction publication boundary.
//!
//! The defect, traced with `--debug-cert`: the result mapper treated
//! `quantifiers_supported_by_uf_completion` as a certificate even though it is
//! only a local shape classifier. Compounding it,
//! `term_supported_by_uf_completion`'s `and` arm (`mbqi.rs:1339`) accepts each
//! conjunct independently and nothing requires a defined head to be defined once,
//! so the contradictory pair `(= (f x) 0)` / `(= x (f x))` is certified as freely
//! completable.
//!
//! A coverage flag is not a repair. E-matching clears `has_uninstantiated` after
//! one accepted match, not after covering the binder domain. The partial-match
//! regression below pins that distinction. SAT recovery therefore needs an
//! independently constructed/rechecked total model or a narrow semantic
//! certificate; the broad classifier is only a refinement hint.

const STRICT_LEG_WRONG_SAT: &str =
    include_str!("../fixtures/ufbv_uf_completion_strict_leg_wrong_sat.smt2");

/// Regression for the formerly open wrong-`sat` publication obligation.
#[test]
fn strict_uf_completion_never_grants_sat_without_coverage() {
    let results = crate::common::solve_vec(STRICT_LEG_WRONG_SAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "WRONG SAT regression: this problem is UNSATISFIABLE — instantiating at \
         x = #x00000001 demands f(1) = 0 and 1 = f(1), hence 1 = 0 (z3 4.15.4 \
         agrees `unsat`). The broad UF-completion classifier must never grant \
         `sat`; `unknown` is the sound answer and `unsat` is ideal. Got {results:?}"
    );
}

fn assert_default_and_selfcheck_never_sat(smt: &str, description: &str) {
    let default = crate::common::solve_vec(smt);
    assert!(
        !default.iter().any(|r| r == "sat"),
        "{description}: default mode must not emit sat; got {default:?}"
    );
    let selfcheck = crate::common::solve_selfcheck_vec(smt);
    assert!(
        !selfcheck.iter().any(|r| r == "sat"),
        "{description}: self-check mode must not emit sat; got {selfcheck:?}"
    );
}

/// One trigger match is not coverage. The explicit trigger has a ground match
/// only at zero, while the universal is false at one.
#[test]
fn one_ematch_does_not_turn_the_shape_classifier_into_a_certificate() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 16)) (_ BitVec 16))
        (declare-fun trigger ((_ BitVec 16)) (_ BitVec 16))
        (assert (= (trigger #x0000) #x0000))
        (assert (forall ((x (_ BitVec 16)))
          (! (and (= (f x) #x0000) (= x (f x)))
             :pattern ((trigger x)))))
        (check-sat)
        "#,
        "one E-match at x=0 leaves the refuting x=1 point uncovered",
    );
}

/// Having no ground occurrence of an explicit trigger head means only that
/// E-matching cannot fire. It does not make the quantified body satisfiable.
#[test]
fn dead_trigger_is_not_a_semantic_sat_certificate() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (assert
          (forall ((x (_ BitVec 1)))
            (! (and (= (f x) #b0) (= (f x) #b1))
               :pattern ((f x)))))
        (check-sat)
        "#,
        "a dead trigger cannot satisfy an impossible universal body",
    );
}

/// The narrower model-backed classifier has the same obligation: matching a
/// definition at `x = 0` says nothing about the already-ground application at
/// `x = 1`. Materializing `f(x) = 0` would falsify the ground assertion.
#[test]
fn one_ematch_does_not_establish_given_sat_ground_application_coverage() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 16)) (_ BitVec 16))
        (declare-fun trigger ((_ BitVec 16)) (_ BitVec 16))
        (assert (= (f #x0001) #x0001))
        (assert (= (trigger #x0000) #x0000))
        (assert (forall ((x (_ BitVec 16)))
          (! (= (f x) #x0000)
             :pattern ((trigger x)))))
        (check-sat)
        "#,
        "one unrelated trigger match does not cover the ground f(1) application",
    );
}

/// With the exact definition head as the trigger, every indexed `f` use is
/// instantiated. The conflicting ground point must therefore be refuted.
#[test]
fn exact_definition_head_trigger_covers_the_ground_application() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 16)) (_ BitVec 16))
        (assert (= (f #x0001) #x0001))
        (assert (forall ((x (_ BitVec 16)))
          (! (= (f x) #x0000)
             :pattern ((f x)))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve_vec(smt), ["unsat"]);
    let selfcheck = crate::common::solve_selfcheck_vec(smt);
    assert!(
        !selfcheck.iter().any(|result| result == "sat"),
        "self-check may withhold an uncertified refutation but must never emit sat; \
         got {selfcheck:?}"
    );
}

/// Two pointwise definitions of the same head can match at different points
/// while remaining jointly inconsistent everywhere. "Each matched once" is
/// still not a materialized joint model.
#[test]
fn separately_matched_same_head_definitions_are_not_a_joint_model_certificate() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 16)) (_ BitVec 16))
        (declare-fun trigger_zero ((_ BitVec 16)) (_ BitVec 16))
        (declare-fun trigger_one ((_ BitVec 16)) (_ BitVec 16))
        (assert (= (trigger_zero #x0000) #x0000))
        (assert (= (trigger_one #x0001) #x0001))
        (assert (forall ((x (_ BitVec 16)))
          (! (= (f x) #x0000)
             :pattern ((trigger_zero x)))))
        (assert (forall ((x (_ BitVec 16)))
          (! (= (f x) #x0001)
             :pattern ((trigger_one x)))))
        (check-sat)
        "#,
        "separate matches cannot reconcile conflicting total definitions of f",
    );
}

/// Checking heads independently is insufficient: these two distinct-head
/// equations jointly require a bit-vector value equal to its complement.
#[test]
fn distinct_head_cycle_is_not_a_completion_certificate() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 16)) (_ BitVec 16))
        (declare-fun g ((_ BitVec 16)) (_ BitVec 16))
        (assert (forall ((x (_ BitVec 16))) (= (f x) (g x))))
        (assert (forall ((x (_ BitVec 16))) (= (g x) (bvnot (f x)))))
        (check-sat)
        "#,
        "distinct syntactic heads can still form an inconsistent cycle",
    );
}

/// A single syntactic equation can impose an impossible cardinality
/// constraint. `f(g(x)) = x` would inject 2^16 values through Bool.
#[test]
fn finite_domain_pigeonhole_is_not_a_completion_certificate() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic UFBV)
        (declare-fun g ((_ BitVec 16)) Bool)
        (declare-fun f (Bool) (_ BitVec 16))
        (assert (forall ((x (_ BitVec 16))) (= (f (g x)) x)))
        (check-sat)
        "#,
        "a Bool-mediated left inverse cannot cover the BV16 domain",
    );
}

/// Extracting and materializing a nested forall does not establish the truth
/// of its enclosing Boolean assertion. Here `p(true)` and `p(false)` force
/// `p(q)` for every Boolean `q`, so the final negated application is false
/// regardless of the quantified definition's truth value.
#[test]
fn nested_forall_is_not_a_top_level_definition_certificate() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic UFBV)
        (declare-fun p (Bool) Bool)
        (declare-fun f ((_ BitVec 16)) (_ BitVec 16))
        (assert (p true))
        (assert (p false))
        (assert (= (f #x0000) #x0000))
        (assert
          (not
            (p
              (forall ((x (_ BitVec 16)))
                (! (= (f x) #x0000)
                   :pattern ((f x)))))))
        (check-sat)
        "#,
        "materializing a nested forall cannot discharge its enclosing assertion",
    );
}

/// A Seq binder is outside MBQI's synthesizable sorts. Shape recognition and
/// one E-match cannot prove this impossible left inverse: it would inject the
/// infinite `(Seq Int)` domain through Bool.
#[test]
fn unsafe_binder_completion_shape_does_not_bypass_fail_closed_gate() {
    assert_default_and_selfcheck_never_sat(
        r#"
        (set-logic ALL)
        (declare-fun g ((Seq Int)) Bool)
        (declare-fun f (Bool) (Seq Int))
        (declare-const s (Seq Int))
        (assert (= (g s) false))
        (assert
          (forall ((x (Seq Int)))
            (! (= (f (g x)) x)
               :pattern ((g x)))))
        (check-sat)
        "#,
        "a shape-only completion hint cannot discharge an unsafe Seq binder",
    );
}

/// `--self-check` reaches the same mandatory publication boundary. Pin it so
/// later certificate work cannot regress the stricter workflow.
#[test]
fn strict_uf_completion_selfcheck_failclosed() {
    let results = crate::common::solve_selfcheck_vec(STRICT_LEG_WRONG_SAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "`--self-check` must stay fail-closed here (measured `unknown` with \
         `:reason-unknown incomplete`); got {results:?}"
    );
}

/// Sanity: the fixture is the input this spec claims, so it cannot pass vacuously.
#[test]
fn fixture_is_the_minimal_unsat_strict_leg_witness() {
    assert!(
        STRICT_LEG_WRONG_SAT.contains("(set-info :status unsat)"),
        "fixture must declare its UNSAT ground truth"
    );
    assert!(
        STRICT_LEG_WRONG_SAT.contains("forall"),
        "fixture must be quantified"
    );
    // Both conjuncts are load-bearing: the constant-valued definition of `f` AND
    // the equation against the BARE bound variable. Lose either and the shape no
    // longer exercises the strict leg's missing distinct-head discipline.
    assert!(
        STRICT_LEG_WRONG_SAT.contains("(= (f x) (_ bv0 32))")
            && STRICT_LEG_WRONG_SAT.contains("(= x (f x))"),
        "fixture must retain BOTH contradictory definitions of `f` — the \
         constant-valued one and the bare-bound-variable one"
    );
    assert!(
        ay_frontend::parse(STRICT_LEG_WRONG_SAT).is_ok(),
        "fixture must parse — else the verdict assertion is vacuous"
    );
}
