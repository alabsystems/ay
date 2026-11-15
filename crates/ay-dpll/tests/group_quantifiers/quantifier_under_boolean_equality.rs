// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for quantifiers nested in Boolean structure (Verus fix
//! queue, row D).
//!
//! Verus asserts every quantified claim as `(= tmp%k (exists ...))` or
//! `(= tmp%k (forall ...))`, and states each extensional-equality axiom as
//! `(= (ext_eq s t) (and (= (len s) (len t)) (forall i. ...)))`. The NNF
//! Skolemizer had no arm for a Boolean `=`, so the quantifier kept no
//! polarity: an existential was never Skolemized or instantiated, and a
//! universal was only a proxy the ground solver guessed. In z3's unsat cores of
//! the suite's "unknown where z3 proves unsat" queries, not one with this shape
//! was refuted. The `=` is now split into its two implications (#iff-split),
//! except where it is the whole body of a universal defining a predicate, as
//! in the extensional-equality axiom (#iff-split-definition): split, that
//! definition's witness is a Skolem function of the binders, and the native
//! posture declined every refutation resting on it. A solve that publishes
//! without a proof (`--z3-mode`) splits the definition too.
//!
//! An assertion whose quantifiers are all entailed, but which carries ground
//! content around them, used to be deleted whole by the quantifier strip. Row
//! D1's unit propagation makes such universals entailed far more often, and so
//! does the split, e.g. `(or (and (= (len s) (len t)) Q) (not e))` once `e` is
//! a fact; deleting the assertion loses `(= (len s) (len t))`. It is now kept
//! with each entailed universal replaced by `true` (#entailed-to-true).
//!
//! Ground truth for every fixture is in its doc comment and was checked with
//! z3 4.12.5 (the solver Verus ships), with and without MBQI.

/// **GROUND TRUTH: UNSAT.** `e` is a fact, so the disjunction forces
/// `(= (len 0) (len 1))`, which the last assertion denies. The universal is
/// entailed through the same clause, and the strip deleted the clause with it.
const ENTAILED_NESTED: &str = r#"
(set-logic ALL)
(declare-fun len (Int) Int)
(declare-fun el (Int Int) Int)
(declare-const e Bool)
(assert (or (and (= (len 0) (len 1))
  (forall ((i Int)) (! (= (el 0 i) (el 1 i)) :pattern ((el 0 i))))) (not e)))
(assert e)
(assert (not (= (len 0) (len 1))))
(check-sat)
"#;

/// `ENTAILED_NESTED` with a different length denied. **GROUND TRUTH: SAT.**
const ENTAILED_NESTED_SAT: &str = r#"
(set-logic ALL)
(declare-fun len (Int) Int)
(declare-fun el (Int Int) Int)
(declare-const e Bool)
(assert (or (and (= (len 0) (len 1))
  (forall ((i Int)) (! (= (el 0 i) (el 1 i)) :pattern ((el 0 i))))) (not e)))
(assert e)
(assert (not (= (len 0) (len 2))))
(check-sat)
"#;

/// Reduced from Verus `quantifiers::test1`: the goal's `exists` sits under
/// `(= tmp ...)`. **GROUND TRUTH: UNSAT.** With `tmp` false the existential is
/// false, so its negation `forall i. not (nat i /\ i >= 0 /\ tr i)` holds and
/// its instance at 300 contradicts `tr 300`.
const GOAL_EXISTS: &str = r#"
(set-logic ALL)
(declare-fun tr (Int) Bool)
(declare-fun nat (Int) Bool)
(declare-const tmp Bool)
(declare-const label Bool)
(assert (forall ((i Int)) (! (tr i) :pattern ((tr i)))))
(assert (forall ((x Int)) (! (=> (<= 0 x) (nat x)) :pattern ((nat x)))))
(assert (tr 300))
(assert (not (=> (= tmp (exists ((i Int)) (! (and (nat i) (>= i 0) (tr i))
  :pattern ((tr i))))) (=> label tmp))))
(check-sat)
"#;

/// `GOAL_EXISTS` without the definition of `tr` and with `(tr 300)` false.
/// **GROUND TRUTH: SAT.**
const GOAL_EXISTS_SAT: &str = r#"
(set-logic ALL)
(declare-fun tr (Int) Bool)
(declare-fun nat (Int) Bool)
(declare-const tmp Bool)
(declare-const label Bool)
(assert (forall ((x Int)) (! (=> (<= 0 x) (nat x)) :pattern ((nat x)))))
(assert (not (tr 300)))
(assert (not (=> (= tmp (exists ((i Int)) (! (and (nat i) (>= i 0) (tr i))
  :pattern ((tr i))))) (=> label tmp))))
(check-sat)
"#;

/// The extensional-equality shape, read backwards: both sequences have
/// length 0, so the inner universal holds vacuously and `(e 0 1)` is true.
/// **GROUND TRUTH: UNSAT.** The definition is not split
/// (#iff-split-definition), so this is refuted as it was before #iff-split.
const EXT_EQ_BACKWARD: &str = r#"
(set-logic ALL)
(declare-fun len (Int) Int)
(declare-fun el (Int Int) Int)
(declare-fun e (Int Int) Bool)
(declare-const tmp Bool)
(assert (forall ((s Int) (t Int)) (! (= (e s t) (and (= (len s) (len t))
  (forall ((i Int)) (! (=> (and (<= 0 i) (< i (len s))) (= (el s i) (el t i)))
    :pattern ((el s i)))))) :pattern ((e s t)))))
(assert (= (len 0) 0))
(assert (= (len 1) 0))
(assert (not (=> (= tmp (e 0 1)) tmp)))
(check-sat)
"#;

/// `EXT_EQ_BACKWARD` with both lengths 1, so the elements decide.
/// **GROUND TRUTH: SAT.**
const EXT_EQ_BACKWARD_SAT: &str = r#"
(set-logic ALL)
(declare-fun len (Int) Int)
(declare-fun el (Int Int) Int)
(declare-fun e (Int Int) Bool)
(declare-const tmp Bool)
(assert (forall ((s Int) (t Int)) (! (= (e s t) (and (= (len s) (len t))
  (forall ((i Int)) (! (=> (and (<= 0 i) (< i (len s))) (= (el s i) (el t i)))
    :pattern ((el s i)))))) :pattern ((e s t)))))
(assert (= (len 0) 1))
(assert (= (len 1) 1))
(assert (not (=> (= tmp (e 0 1)) tmp)))
(check-sat)
"#;

/// The extensional-equality shape, read forwards: `(e 0 1)` forces equal
/// lengths. **GROUND TRUTH: UNSAT.** Split, the instance at (0, 1) is
/// `(or (and (= (len 0) (len 1)) Q) (not (e 0 1)))` with `Q` entailed;
/// deleting it whole, as the quantifier strip did, loses the length equality
/// (#entailed-to-true).
const EXT_EQ_FORWARD: &str = r#"
(set-logic ALL)
(declare-fun len (Int) Int)
(declare-fun el (Int Int) Int)
(declare-fun e (Int Int) Bool)
(assert (forall ((s Int) (t Int)) (! (= (e s t) (and (= (len s) (len t))
  (forall ((i Int)) (! (=> (and (<= 0 i) (< i (len s))) (= (el s i) (el t i)))
    :pattern ((el s i)))))) :pattern ((e s t)))))
(assert (e 0 1))
(assert (not (= (len 0) (len 1))))
(check-sat)
"#;

/// `EXT_EQ_FORWARD` with equal lengths and one differing element inside
/// them. **GROUND TRUTH: UNSAT** as well, through the inner universal's
/// instance at 0; its twin below drops the element fact.
const EXT_EQ_FORWARD_ELEMENT: &str = r#"
(set-logic ALL)
(declare-fun len (Int) Int)
(declare-fun el (Int Int) Int)
(declare-fun e (Int Int) Bool)
(assert (forall ((s Int) (t Int)) (! (= (e s t) (and (= (len s) (len t))
  (forall ((i Int)) (! (=> (and (<= 0 i) (< i (len s))) (= (el s i) (el t i)))
    :pattern ((el s i)))))) :pattern ((e s t)))))
(assert (e 0 1))
(assert (= (len 0) 2))
(assert (not (= (el 0 0) (el 1 0))))
(check-sat)
"#;

/// `EXT_EQ_FORWARD_ELEMENT` with the differing element outside the length.
/// **GROUND TRUTH: SAT.**
const EXT_EQ_FORWARD_SAT: &str = r#"
(set-logic ALL)
(declare-fun len (Int) Int)
(declare-fun el (Int Int) Int)
(declare-fun e (Int Int) Bool)
(assert (forall ((s Int) (t Int)) (! (= (e s t) (and (= (len s) (len t))
  (forall ((i Int)) (! (=> (and (<= 0 i) (< i (len s))) (= (el s i) (el t i)))
    :pattern ((el s i)))))) :pattern ((e s t)))))
(assert (e 0 1))
(assert (= (len 0) 2))
(assert (not (= (el 0 5) (el 1 5))))
(check-sat)
"#;

/// A forall-exists claim under a Boolean equality, asserted false.
/// **GROUND TRUTH: UNSAT** (z3 4.12.5): `∀y. ∃x. x > y` is valid.
const ALTERNATION_FALSE: &str = r#"
(set-logic ALL)
(declare-const b Bool)
(assert (= b (forall ((y Int)) (exists ((x Int)) (> x y)))))
(assert (not b))
(check-sat)
"#;

/// `ALTERNATION_FALSE` with `b` asserted true. **GROUND TRUTH: SAT.**
const ALTERNATION_TRUE: &str = r#"
(set-logic ALL)
(declare-const b Bool)
(assert (= b (forall ((y Int)) (exists ((x Int)) (> x y)))))
(assert b)
(check-sat)
"#;

fn verdicts(smt: &str) -> Vec<String> {
    crate::common::solve_vec(smt)
}

/// CAPABILITY: before #entailed-to-true this answered `unknown`.
#[test]
fn ground_content_around_an_entailed_universal_is_kept() {
    let results = verdicts(ENTAILED_NESTED);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the clause forces (= (len 0) (len 1)); got {results:?}"
    );
}

/// CAPABILITY: before #iff-split this answered `unknown`.
#[test]
fn an_existential_under_a_boolean_equality_is_refuted() {
    let results = verdicts(GOAL_EXISTS);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "with tmp false the existential's negation is instantiated at 300; got {results:?}"
    );
}

/// REGRESSION GUARD: all three were refuted before #iff-split, through the
/// proxy lane. Splitting the definition under its universal lost all three in
/// this posture (Skolem-function witness, no proof record);
/// #iff-split-definition keeps the definition whole.
#[test]
fn extensional_equality_is_refuted_both_ways() {
    for (name, smt) in [
        ("backward", EXT_EQ_BACKWARD),
        ("forward, lengths", EXT_EQ_FORWARD),
        ("forward, element", EXT_EQ_FORWARD_ELEMENT),
    ] {
        let results = verdicts(smt);
        assert!(
            results.iter().any(|r| r == "unsat"),
            "{name}: the extensional-equality definition refutes the goal; got {results:?}"
        );
    }
}

/// The CLI's `--z3-mode` posture, the one Verus runs ay in.
pub(super) fn z3_mode_verdicts(smt: &str) -> Vec<String> {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_competition_mode(true);
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"))
}

/// REGRESSION GUARD for #iff-split-alternation: answered `unsat` in the
/// `--z3-mode` posture before the split, and `unknown` while it split this
/// equality, whose positive copy needs a Skolem function of `y`. The default
/// posture answers `unknown` either way.
#[test]
fn a_quantifier_alternation_under_a_boolean_equality_is_refuted() {
    let results = z3_mode_verdicts(ALTERNATION_FALSE);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "every y has a larger x, so b cannot be false; got {results:?}"
    );
}

/// SOUNDNESS FLOOR: each satisfiable twin differs from a refuted fixture in
/// one fact, and must never be refuted.
#[test]
fn quantifiers_in_boolean_structure_never_refute_a_satisfiable_query() {
    for (name, smt) in [
        ("entailed nested", ENTAILED_NESTED_SAT),
        ("goal exists", GOAL_EXISTS_SAT),
        ("ext_eq backward", EXT_EQ_BACKWARD_SAT),
        ("ext_eq forward", EXT_EQ_FORWARD_SAT),
        ("alternation true", ALTERNATION_TRUE),
    ] {
        for results in [
            verdicts(smt),
            crate::common::solve_selfcheck_vec(smt),
            z3_mode_verdicts(smt),
        ] {
            assert!(
                !results.iter().any(|r| r == "unsat"),
                "WRONG ANSWER ({name}): this query is SATISFIABLE; got {results:?}"
            );
        }
    }
}

/// The recovered refutations never become `sat` in any posture.
#[test]
fn quantifiers_in_boolean_structure_are_never_sat_when_refutable() {
    for smt in [
        ENTAILED_NESTED,
        GOAL_EXISTS,
        EXT_EQ_BACKWARD,
        EXT_EQ_FORWARD,
        EXT_EQ_FORWARD_ELEMENT,
        ALTERNATION_FALSE,
    ] {
        for results in [
            verdicts(smt),
            crate::common::solve_selfcheck_vec(smt),
            z3_mode_verdicts(smt),
        ] {
            assert!(
                !results.iter().any(|r| r == "sat"),
                "WRONG ANSWER: the query is UNSATISFIABLE; got {results:?}"
            );
        }
    }
}

/// Generated w1_51 file 49 (`gen_w1.py OUTDIR 400 51`). **GROUND TRUTH:
/// UNSAT** (z3 4.16.0): with `q` a fact the universal holds, and `v := -2`
/// falsifies its body for either value of `p`. Every `Int` term of the problem
/// sits under the binder.
pub(super) const W1_ITE_COEFFICIENT: &str = r#"
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= q (forall ((v Int)) (> (+ (* v (ite p 0 2)) v) (- 2)))))
(assert q)
(check-sat)
"#;

/// Generated w1_51 file 92. **GROUND TRUTH: UNSAT** (z3 4.16.0): with
/// `w = 1` the coefficient `(mod w 3) - 1` is 0, so the body is `v >= 0`.
pub(super) const W1_MOD_COEFFICIENT: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun q () Bool)
(assert (= q (forall ((v Int)) (>= (+ (* v (- (mod w 3) 1)) v) 0))))
(assert q)
(assert (= w 1))
(check-sat)
"#;

/// Generated w1_51 file 13. **GROUND TRUTH: UNSAT** (z3 4.16.0): `v := 0`
/// falsifies `(> (+ (* (mod w 3) v) v 0) 0)`.
pub(super) const W1_WITH_SECOND_UNIVERSAL: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun a () Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun A () (Array Int Int))
(assert (= q (forall ((v Int)) (> (+ (* (mod w 3) v) v 0) 0))))
(assert (forall ((v Int)) (or (= (+ (* v (select A a)) (* 2 v)) 0) (> a 3))))
(assert q)
(assert p)
(check-sat)
"#;

/// `W1_ITE_COEFFICIENT` with the equality weakened to the implication it
/// contains. **GROUND TRUTH: UNSAT** (z3 4.16.0). `unknown` in the default
/// posture before #iff-split-implied-authority, with or without the split,
/// and again since the lane's presentation gate: the restoration pass gives
/// no spelling to a root whose authored head (`=>`) differs from its
/// canonical one (`or`), so the certificate would assume
/// `(or (forall ((v_2 Int)) ..) (not q))`, no assertion of the input.
pub(super) const W1_IMPLIED: &str = r#"
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (=> q (forall ((v Int)) (> (+ (* v (ite p 0 2)) v) (- 2)))))
(assert q)
(check-sat)
"#;

/// `W1_ITE_COEFFICIENT` with `q` denied. **GROUND TRUTH: SAT.**
const W1_DENIED_SAT: &str = r#"
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= q (forall ((v Int)) (> (+ (* v (ite p 0 2)) v) (- 2)))))
(assert (not q))
(check-sat)
"#;

/// The universal holds once `p` is a fact. **GROUND TRUTH: SAT.**
const W1_ITE_HOLDS_SAT: &str = r#"
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= q (forall ((v Int)) (> (* v (ite p 0 2)) (- 2)))))
(assert q)
(assert p)
(check-sat)
"#;

/// `W1_MOD_COEFFICIENT` without `w = 1`: `w = 0` makes the body `0 >= 0`.
/// **GROUND TRUTH: SAT.**
const W1_MOD_FREE_SAT: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun q () Bool)
(assert (= q (forall ((v Int)) (>= (+ (* v (- (mod w 3) 1)) v) 0))))
(assert q)
(check-sat)
"#;

/// REGRESSION GUARD for #iff-split-implied-authority, in the CLI's default
/// posture (the authored boundary). All three w1_51 files answered `unsat`
/// before #iff-split (admitted as `discharged-trust`), and `unknown
/// (quantifier-unhandled)` after it: the split makes the universal entailed,
/// its enumerated instance at a ground value (`-2`, `0`, `-1`) refutes the
/// query, and the artifact firewall then demands an authored-scope
/// certificate that no lane could build — none read a universal under an
/// authored `=`, and none was told the refuting value. They now publish as
/// `strict-proof`.
#[test]
fn an_equated_universal_refuted_by_an_instance_is_published_in_the_default_posture() {
    for (name, smt) in [
        ("ite coefficient", W1_ITE_COEFFICIENT),
        ("mod coefficient", W1_MOD_COEFFICIENT),
        ("second universal", W1_WITH_SECOND_UNIVERSAL),
    ] {
        let results = crate::common::solve_authored_vec(smt);
        assert!(
            results.iter().any(|r| r == "unsat"),
            "{name}: the universal's CEGQI instance refutes the query; got {results:?}"
        );
    }
}

/// SOUNDNESS FLOOR for the fixtures above, in every posture.
#[test]
fn equated_universal_twins_are_never_refuted() {
    for (name, smt) in [
        ("denied", W1_DENIED_SAT),
        ("holds", W1_ITE_HOLDS_SAT),
        ("mod free", W1_MOD_FREE_SAT),
    ] {
        for results in [
            crate::common::solve_authored_vec(smt),
            crate::common::solve_authored_selfcheck_vec(smt),
            verdicts(smt),
            z3_mode_verdicts(smt),
        ] {
            assert!(
                !results.iter().any(|r| r == "unsat"),
                "WRONG ANSWER ({name}): this query is SATISFIABLE; got {results:?}"
            );
        }
    }
}
