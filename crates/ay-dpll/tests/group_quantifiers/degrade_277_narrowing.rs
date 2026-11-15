// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for the `degrade@277` narrowing (#degrade277-narrow).
//!
//! # What the gate was, and what it is now
//!
//! `classify_quantifier_result` discards a ground UNSAT whenever the
//! pre-instantiation snapshot holds a `forall` outside top-level conjunctive
//! position and the quantifier-free core is not independently UNSAT, because
//! the refutation *may* have been manufactured by conjoining an instance of a
//! universal the problem does not assert unconditionally.
//!
//! Syntactic position is not what licenses a conjoin. Every lane that appends a
//! ground instance to `ctx.assertions` as a top-level fact is gated on
//! `ematching::entailed_forall_set` — the polarity- and unit-aware predicate
//! for "the PROBLEM entails this universal". A universal the problem entails
//! may be instantiated wherever it sits. So the gate's premise is false exactly
//! when NO non-conjunctive `forall` of the snapshot was treated as entailed,
//! and that is now the extra condition.
//!
//! The four legs of the predicate itself (unset authority, an unlicensed MBQI
//! conjoin, an entailed non-conjunctive `forall`, and the narrow case) are unit
//! tested next to the gate in
//! `crates/ay-dpll/src/executor/quantifier_loop/result_mapping.rs`. This module
//! pins the two things a unit test cannot: that the narrowing buys a real,
//! externally checkable verdict, and that it moves no soundness floor.
//!
//! # Ground truth for every fixture here is stated in its doc comment and was
//! confirmed against z3 5.1.0.

/// The capability differential, and the mutation differential for this change.
///
/// `∀x. p(x)` is a top-level conjunct: entailed, so E-matching instantiates it
/// at `c` and the instance clashes with `¬p(c)`. The third assertion adds a
/// `forall` under a positive `or` whose sibling `g` is unconstrained — outside
/// conjunctive position and NOT entailed, so no lane ever instantiates it, and
/// `purify_quantifier_atoms` replaces it with a Boolean proxy.
///
/// The old gate saw "a non-conjunctive forall exists" and threw the refutation
/// away. Nothing about that `forall` touched the derivation.
///
/// **GROUND TRUTH: UNSAT** — `∀x.p(x)` alone refutes `¬p(c)` no matter how the
/// third assertion is satisfied. z3 5.1.0 agrees. Measured at
/// `0.25.0+build.9545.7229fb4b29`: `unknown` before the narrowing, `unsat`
/// after, in the default, `--strict-proofs` and `--self-check` postures alike,
/// with a five-step hole-free Alethe certificate the pinned Carcara 1.1.0 calls
/// `valid` (`unproved_steps=0 trust_free=yes`).
const NONENTAILED_BYSTANDER_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun c () Int)
(declare-fun g () Bool)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (not (p c)))
(assert (or g (forall ((y Int)) (q y))))
(check-sat)
"#;

/// The satisfiable sibling: the same shape with the refuting ground fact
/// flipped, plus a constraint that forces the disjunct-position `forall` to be
/// discharged by its Boolean sibling rather than by the universal.
///
/// **GROUND TRUTH: SAT** (`p ≡ true`, `q ≡ false`, `g ≡ true`), confirmed by
/// z3 5.1.0. A refutation here would mean the narrowing let through an UNSAT
/// built on the non-entailed universal — the exact failure the gate exists to
/// prevent.
const NONENTAILED_BYSTANDER_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun c () Int)
(declare-fun g () Bool)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (p c))
(assert (or g (forall ((y Int)) (q y))))
(assert (not (q c)))
(check-sat)
"#;

/// A genuinely UNSAT problem whose ABSTRACTED skeleton is satisfiable, with an
/// entailed conjunctive universal added so the full E-matching + classification
/// pipeline runs and the narrowing predicate is actually consulted.
///
/// `n <= 4` refutes `n > 5`, so the clause forces `∀x. p(x)`, which forces
/// `p(c)` and contradicts `¬p(c)`. **GROUND TRUTH: UNSAT**, and z3 5.1.0 agrees.
/// The skeleton `(or (> n 5) qproxy) ∧ n ≤ 4 ∧ ¬p(c) ∧ rproxy` is satisfiable
/// with `qproxy := true`, so `sat` here is a WRONG ANSWER handed back from a
/// model of an over-approximation.
const PROXIED_SKELETON_SAT_BUT_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun n () Int)
(declare-fun c () Int)
(declare-fun p (Int) Bool)
(declare-fun r (Int) Bool)
(assert (forall ((z Int)) (r z)))
(assert (<= n 4))
(assert (or (> n 5) (forall ((x Int)) (p x))))
(assert (not (p c)))
(check-sat)
"#;

fn verdicts(smt: &str) -> Vec<String> {
    crate::common::solve_vec(smt)
}

/// CAPABILITY. Remove the `nonconjunctive_forall_may_have_been_conjoined`
/// conjunct from the gate and this test fails: the refutation is discarded and
/// the answer is `unknown`. That is the mutation differential — the narrowing
/// is load-bearing for this verdict, not decoration on one that already held.
#[test]
fn a_bystander_nonentailed_forall_no_longer_eats_the_refutation() {
    let results = verdicts(NONENTAILED_BYSTANDER_UNSAT);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "`forall x. p(x)` is a top-level conjunct and `not (p c)` contradicts \
         its instance at c. The only other universal is neither entailed nor \
         instantiated by any lane, so it cannot have contributed to the \
         derivation and must not veto it; got {results:?}"
    );
}

/// The same verdict must survive the fail-closed self-check posture: the
/// narrowing lets an ordinary E-matching refutation through, so AY's own
/// checker has a real proof to confirm.
#[test]
fn the_recovered_refutation_survives_self_check() {
    let results = crate::common::solve_selfcheck_vec(NONENTAILED_BYSTANDER_UNSAT);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the recovered refutation is an ordinary `forall_inst` + resolution \
         derivation, so it must survive the posture that publishes only what \
         AY can check; got {results:?}"
    );
}

/// SOUNDNESS FLOOR. The narrowing may never manufacture a refutation.
#[test]
fn the_narrowing_never_manufactures_a_refutation() {
    for (name, smt) in [
        ("bystander sibling", NONENTAILED_BYSTANDER_SAT),
        (
            "rodin shape",
            r#"
            (set-logic AUFLIA)
            (declare-sort D 0)
            (declare-fun dap (D D) Bool)
            (declare-fun mAckn (D) Bool)
            (declare-fun a () D)
            (assert (forall ((x D))
              (not (and (mAckn x) (exists ((x0 D)) (dap x0 x))))))
            (assert (not (mAckn a)))
            (assert (dap a a))
            (check-sat)
            "#,
        ),
    ] {
        let results = verdicts(smt);
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER ({name}): this problem is SATISFIABLE. A refutation \
             would mean an instance of a universal the problem does not entail \
             was conjoined and the narrowed gate let it through; got {results:?}"
        );
    }
}

/// SOUNDNESS FLOOR, the acceptance obligation: a `sat` may never be published
/// through a proxied quantifier, with the narrowing live.
///
/// The proxy abstraction is an OVER-APPROXIMATION — `σ(A)` UNSAT implies `A`
/// UNSAT, but a model of `σ(A)` assigns the fresh proxies freely and says
/// nothing about `A`. The narrowing is read at exactly one site, inside an arm
/// already conditioned on `Ok(SolveResult::Unsat(_))`, so it cannot widen a SAT
/// path; these fixtures are the live-fire check on that claim.
#[test]
fn no_sat_is_published_through_a_proxied_quantifier() {
    let results = verdicts(PROXIED_SKELETON_SAT_BUT_UNSAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "WRONG ANSWER: this problem is UNSATISFIABLE and only its abstracted \
         skeleton is satisfiable. Publishing `sat` hands back a model of the \
         over-approximation as a model of the query. `unsat` and `unknown` are \
         both acceptable; got {results:?}"
    );
}

/// The same floor under `--self-check`, where nothing may be published that
/// AY's own checker cannot confirm.
#[test]
fn no_sat_is_published_through_a_proxied_quantifier_under_self_check() {
    let results = crate::common::solve_selfcheck_vec(PROXIED_SKELETON_SAT_BUT_UNSAT);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "`--self-check` must not certify a model of the abstraction; got \
         {results:?}"
    );
}

/// A proxy is preprocessing scaffolding, not a symbol of the query. It must
/// never reach a published model — which, while the fail-closed arm holds, is
/// automatic because an abstracted solve publishes no model at all.
#[test]
fn proxies_stay_out_of_published_output() {
    let with_model = format!(
        "{}\n(get-model)\n",
        PROXIED_SKELETON_SAT_BUT_UNSAT.trim_end()
    );
    let results = verdicts(&with_model);
    for line in &results {
        assert!(
            !line.contains("qproxy"),
            "an abstraction proxy escaped into published output: {line:?} \
             (full output {results:?})"
        );
    }
}

/// (#degrade277-unit-harvest) Verus's fuel-guarded definition, reduced from
/// `broadcast_forall::test2` (the Verus fix queue's `D1-guarded-forall.smt2`).
///
/// Verus states every fuel-controlled definition and broadcast lemma as
/// `(=> (fuel_bool f) (forall ...))` and asserts the guard inside its negated
/// goal. `mk_implies`/`mk_not` store that goal as `(and (fuel_bool p) … (not
/// tmp%1))`, so the guard is a conjunct of an asserted `and`. The instantiation
/// licence (`entailed_forall_set`) reads units through that conjunction and
/// instantiates the definition; the `degrade@277` narrowing used to read only
/// literally top-level atoms, judged the same universal non-conjunctive, and
/// discarded the refutation (`unknown (incomplete quantifier-unhandled)`).
///
/// **GROUND TRUTH: UNSAT** — `(fuel_bool p)` is asserted, so the definition
/// holds, its instance at `(I 10)` gives `f(I 10)` because `(I 10)` has type
/// INT, and the goal denies it. z3 4.12.5 answers `unsat`.
const VERUS_FUEL_GUARDED_DEFINITION_UNSAT: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-sort Type 0)
(declare-const INT Type)
(declare-fun has_type (Poly Type) Bool)
(assert (forall ((x Int)) (! (has_type (I x) INT) :pattern ((has_type (I x) INT)))))
(declare-const fuel%f FuelId)
(declare-const fuel%p FuelId)
(assert (distinct fuel%f fuel%p))
(declare-fun f (Poly) Bool)
(assert (=> (fuel_bool fuel%p)
  (forall ((i Poly)) (! (=> (has_type i INT) (f i)) :pattern ((f i))))))
(declare-const tmp%1 Bool)
(declare-const label Bool)
(assert (not (=> (fuel_bool fuel%p) (=> (= tmp%1 (f (I 10))) (=> label tmp%1)))))
(check-sat)
"#;

/// CAPABILITY for #degrade277-unit-harvest: the refutation of a fuel-guarded
/// definition whose guard is a conjunct of the negated goal is published.
#[test]
fn a_guard_asserted_inside_a_conjunction_no_longer_loses_the_refutation() {
    let results = verdicts(VERUS_FUEL_GUARDED_DEFINITION_UNSAT);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the goal asserts `(fuel_bool p)` as a conjunct, so the guarded \
         definition is entailed and its instance at `(I 10)` refutes the goal; \
         got {results:?}"
    );
}

/// SOUNDNESS FLOOR for #degrade277-unit-harvest: the stronger unit oracle may
/// only recognise guards the problem entails.
///
/// * `conjunct guard, satisfiable`: the guard IS entailed, but nothing
///   contradicts the definition — a refutation would be manufactured.
/// * `disjunct guard`: the guard sits under an `or` inside the asserted
///   conjunction, so it is not a unit, and the problem is satisfiable with
///   `h` true and `g` false. Instantiating the guarded universal as a fact
///   would refute it.
///
/// **GROUND TRUTH: SAT** for both; z3 4.12.5 answers `sat`.
#[test]
fn the_unit_harvest_never_manufactures_a_refutation() {
    for (name, smt) in [
        (
            "conjunct guard, satisfiable",
            r#"
            (declare-fun g () Bool)
            (declare-fun c () Int)
            (declare-fun f (Int) Bool)
            (assert (=> g (forall ((x Int)) (! (f x) :pattern ((f x))))))
            (assert (and g (f c)))
            (check-sat)
            "#,
        ),
        (
            "disjunct guard",
            r#"
            (declare-fun g () Bool)
            (declare-fun h () Bool)
            (declare-fun c () Int)
            (declare-fun f (Int) Bool)
            (assert (=> g (forall ((x Int)) (! (not (f x)) :pattern ((f x))))))
            (assert (and (or g h) (f c)))
            (check-sat)
            "#,
        ),
    ] {
        let results = verdicts(smt);
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER ({name}): this problem is SATISFIABLE; got {results:?}"
        );
    }
}
