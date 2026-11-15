// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for Boolean arguments of uninterpreted functions inside
//! quantifier instances (Verus fix queue, row D).
//!
//! Verus boxes a Boolean into its `Poly` sort with `(B b)`, so a trait
//! method's definition reads `(= (apple ... self b) (B (> (%I b) 10)))`.
//! check-sat replaces a compound Boolean argument such as `(> (%I b) 10)` by a
//! fresh proxy before quantifier preprocessing, but the instances that
//! preprocessing then adds still carried the compound argument. EUF cannot
//! congruence-close over `(B <compound>)`, so the goal's `(B proxy)` and the
//! instance's `(B (< 10 (%I t)))` stayed apart, the ground solve found a model
//! the model gate rightly rejected, and the query ended `unknown`
//! (`traits::test_generic_1*` in the Verus suite). In a solve that publishes
//! without a proof (`--z3-mode`, the Verus route) the instances are now
//! purified the same way. A proof-carrying solve keeps them unpurified: a
//! refutation through an instance's proxy rests on an EUF lemma its strict
//! proof checker rejects, and it answered `unknown` on queries it refutes
//! without the proxies.
//!
//! Ground truth for every fixture is in its doc comment; the unsat ones were
//! checked with z3 4.12.5 (the solver Verus ships), with and without MBQI.

/// Reduced from Verus `traits::test_generic_1_ok`. **GROUND TRUTH: UNSAT.**
/// The goal denies the definition's instance at the ground tuple. The unused
/// Real function routes the query through the datatype + AUFLIRA lane.
const TRAIT_METHOD_DEFINITION: &str = r#"
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun R (Real) Poly)
(declare-fun %I (Poly) Int)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-fun UINT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun DST (Dcr) Dcr)
(declare-datatypes ((S. 0) (tuple%2. 0))
  (((S./S (S./S/?0 Poly) (S./S/?1 Poly)))
   ((tuple%2./tuple%2 (tuple%2./tuple%2/?0 Poly) (tuple%2./tuple%2/?1 Poly)))))
(declare-fun TYPE%S. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%tuple%2. (Dcr Type Dcr Type) Type)
(declare-fun Poly%S. (S.) Poly)
(declare-fun Poly%tuple%2. (tuple%2.) Poly)
(declare-fun apple (Dcr Type Dcr Type Poly Poly) Poly)
(assert (forall ((C&. Dcr) (C& Type) (self! Poly) (b! Poly)) (!
  (= (apple $ (TYPE%S. $ BOOL C&. C&) (DST $) (TYPE%tuple%2. C&. C& $ (UINT 16)) self! b!)
     (B (> (%I b!) 10)))
  :pattern ((apple $ (TYPE%S. $ BOOL C&. C&) (DST $) (TYPE%tuple%2. C&. C& $ (UINT 16)) self! b!)))))
(assert (not (= (apple $ (TYPE%S. $ BOOL $ (UINT 8)) (DST $) (TYPE%tuple%2. $ (UINT 8) $ (UINT 16))
    (Poly%S. (S./S (B true) (I 10))) (Poly%tuple%2. (tuple%2./tuple%2 (I 10) (I 20))))
  (B (> (%I (Poly%tuple%2. (tuple%2./tuple%2 (I 10) (I 20)))) 10)))))
(check-sat)
"#;

/// `TRAIT_METHOD_DEFINITION` with the goal's threshold moved to 11.
/// **GROUND TRUTH: SAT** (z3: sat): `%I` of the tuple is free, so it can be 11.
const TRAIT_METHOD_DEFINITION_SAT: &str = r#"
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun R (Real) Poly)
(declare-fun %I (Poly) Int)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-fun UINT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun DST (Dcr) Dcr)
(declare-datatypes ((S. 0) (tuple%2. 0))
  (((S./S (S./S/?0 Poly) (S./S/?1 Poly)))
   ((tuple%2./tuple%2 (tuple%2./tuple%2/?0 Poly) (tuple%2./tuple%2/?1 Poly)))))
(declare-fun TYPE%S. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%tuple%2. (Dcr Type Dcr Type) Type)
(declare-fun Poly%S. (S.) Poly)
(declare-fun Poly%tuple%2. (tuple%2.) Poly)
(declare-fun apple (Dcr Type Dcr Type Poly Poly) Poly)
(assert (forall ((C&. Dcr) (C& Type) (self! Poly) (b! Poly)) (!
  (= (apple $ (TYPE%S. $ BOOL C&. C&) (DST $) (TYPE%tuple%2. C&. C& $ (UINT 16)) self! b!)
     (B (> (%I b!) 10)))
  :pattern ((apple $ (TYPE%S. $ BOOL C&. C&) (DST $) (TYPE%tuple%2. C&. C& $ (UINT 16)) self! b!)))))
(assert (not (= (apple $ (TYPE%S. $ BOOL $ (UINT 8)) (DST $) (TYPE%tuple%2. $ (UINT 8) $ (UINT 16))
    (Poly%S. (S./S (B true) (I 10))) (Poly%tuple%2. (tuple%2./tuple%2 (I 10) (I 20))))
  (B (> (%I (Poly%tuple%2. (tuple%2./tuple%2 (I 10) (I 20)))) 11)))))
(check-sat)
"#;

/// Found by differential fuzzing. **GROUND TRUTH: UNSAT.** The instance at
/// `(I 5)` gives `(g (I 5)) = (B (> 5 0))`, and `(>= 5 1)` has the same value.
const RESPELLED_ATOM: &str = r#"
(declare-sort P 0)
(declare-fun B (Bool) P)
(declare-fun I (Int) P)
(declare-fun i (P) Int)
(declare-fun g (P) P)
(assert (forall ((n Int)) (! (= (i (I n)) n) :pattern ((I n)))))
(assert (forall ((x P)) (! (= (g x) (B (> (i x) 0))) :pattern ((g x)))))
(assert (not (= (g (I 5)) (B (>= (i (I 5)) 1)))))
(check-sat)
"#;

/// `RESPELLED_ATOM` with `(>= 5 6)`, which is false. **GROUND TRUTH: SAT**
/// (z3 times out): P = Int, I and i the identity, (B true) = 1,
/// (B false) = 0, (g x) = (B (> x 0)).
const RESPELLED_ATOM_SAT: &str = r#"
(declare-sort P 0)
(declare-fun B (Bool) P)
(declare-fun I (Int) P)
(declare-fun i (P) Int)
(declare-fun g (P) P)
(assert (forall ((n Int)) (! (= (i (I n)) n) :pattern ((I n)))))
(assert (forall ((x P)) (! (= (g x) (B (> (i x) 0))) :pattern ((g x)))))
(assert (not (= (g (I 5)) (B (>= (i (I 5)) 6)))))
(check-sat)
"#;

/// Found by differential fuzzing. **GROUND TRUTH: UNSAT.** The goal denies the
/// instance at `(I 11)` itself; the last assertion adds a Boolean argument
/// the top-level pass purifies.
const SAME_ATOM_WITH_A_PURIFIED_SIBLING: &str = r#"
(declare-sort P 0)
(declare-fun B (Bool) P)
(declare-fun I (Int) P)
(declare-fun i (P) Int)
(declare-fun g (P) P)
(declare-fun q (P) Bool)
(assert (forall ((n Int)) (! (= (i (I n)) n) :pattern ((I n)))))
(assert (forall ((x P)) (! (= (g x) (B (= (i x) 10))) :pattern ((g x)))))
(assert (not (= (g (I 11)) (B (= (i (I 11)) 10)))))
(assert (= (B (q (I 11))) (B true)))
(check-sat)
"#;

/// Reduced from a Verus `has_type` / `B` / `%B` boxing shape. **GROUND TRUTH:
/// UNSAT** (z3: unsat): `(B p)` is `(B true)`, so `p` is `(%B (B true))`,
/// which is true. Refuted in both postures; with the instances purified, the
/// proof-carrying solve answered `unknown` (its refutation rested on an
/// `EufCongruentPred` lemma over a proxy predicate, which the strict checker
/// rejects).
const BOXED_BOOLEAN_CONSTANT: &str = r#"
(declare-sort Poly 0)
(declare-fun B (Bool) Poly)
(declare-fun %B (Poly) Bool)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(declare-fun has_type (Poly Int) Bool)
(assert (forall ((b Bool)) (! (= (%B (B b)) b) :pattern ((B b)))))
(assert (forall ((x Poly)) (! (=> (has_type x 1) (= x (B (%B x)))) :pattern ((has_type x 1)))))
(declare-const p Bool)
(assert (= (B p) (B true)))
(assert (not p))
(check-sat)
"#;

/// `BOXED_BOOLEAN_CONSTANT` with `p` asserted. **GROUND TRUTH: SAT** (z3: sat).
const BOXED_BOOLEAN_CONSTANT_SAT: &str = r#"
(declare-sort Poly 0)
(declare-fun B (Bool) Poly)
(declare-fun %B (Poly) Bool)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(declare-fun has_type (Poly Int) Bool)
(assert (forall ((b Bool)) (! (= (%B (B b)) b) :pattern ((B b)))))
(assert (forall ((x Poly)) (! (=> (has_type x 1) (= x (B (%B x)))) :pattern ((has_type x 1)))))
(declare-const p Bool)
(assert (= (B p) (B true)))
(assert p)
(check-sat)
"#;

/// The default posture (proof-carrying).
fn verdicts(smt: &str) -> Vec<String> {
    crate::common::solve_vec(smt)
}

/// The CLI's `--z3-mode` posture, which publishes without a proof.
fn verdicts_proof_shed(smt: &str) -> Vec<String> {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_competition_mode(true);
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"))
}

#[test]
fn a_boolean_argument_of_an_instance_is_congruence_closed() {
    for (name, smt) in [
        ("trait method definition", TRAIT_METHOD_DEFINITION),
        ("respelled atom", RESPELLED_ATOM),
        (
            "same atom, purified sibling",
            SAME_ATOM_WITH_A_PURIFIED_SIBLING,
        ),
    ] {
        let results = verdicts_proof_shed(smt);
        assert!(
            results.iter().any(|r| r == "unsat"),
            "{name}: the definition's instance refutes the goal; got {results:?}"
        );
    }
}

#[test]
fn a_proof_carrying_solve_refutes_a_boxed_boolean_constant() {
    for results in [
        verdicts(BOXED_BOOLEAN_CONSTANT),
        verdicts_proof_shed(BOXED_BOOLEAN_CONSTANT),
    ] {
        assert!(
            results.iter().any(|r| r == "unsat"),
            "the boxed constant is refuted in both postures; got {results:?}"
        );
    }
    for results in [
        verdicts(BOXED_BOOLEAN_CONSTANT_SAT),
        verdicts_proof_shed(BOXED_BOOLEAN_CONSTANT_SAT),
    ] {
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER: this query is SATISFIABLE; got {results:?}"
        );
    }
}

#[test]
fn instance_boolean_arguments_never_refute_a_satisfiable_query() {
    for (name, smt) in [
        ("trait method definition", TRAIT_METHOD_DEFINITION_SAT),
        ("respelled atom", RESPELLED_ATOM_SAT),
    ] {
        for results in [
            verdicts(smt),
            verdicts_proof_shed(smt),
            crate::common::solve_selfcheck_vec(smt),
        ] {
            assert!(
                !results.iter().any(|r| r == "unsat"),
                "WRONG ANSWER ({name}): this query is SATISFIABLE; got {results:?}"
            );
        }
    }
}

#[test]
fn instance_boolean_arguments_are_never_sat_when_refutable() {
    for (name, smt) in [
        ("trait method definition", TRAIT_METHOD_DEFINITION),
        ("respelled atom", RESPELLED_ATOM),
        (
            "same atom, purified sibling",
            SAME_ATOM_WITH_A_PURIFIED_SIBLING,
        ),
    ] {
        for results in [
            verdicts(smt),
            verdicts_proof_shed(smt),
            crate::common::solve_selfcheck_vec(smt),
        ] {
            assert!(
                !results.iter().any(|r| r == "sat"),
                "WRONG ANSWER ({name}): this query is UNSATISFIABLE; got {results:?}"
            );
        }
    }
}
