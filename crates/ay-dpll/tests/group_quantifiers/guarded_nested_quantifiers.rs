// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for quantifiers nested in guarded instances
//! (#guarded-nested-quantifiers), for the duals of proxied existentials
//! (#guarded-existential-duals) and for the guarded clauses of interleaved
//! E-matching rounds (#guarded-interleaved-instances).
//!
//! A universal the problem does not entail gets a Boolean proxy `q`, and its
//! instances become clauses `(or (not q) body[t̄])`. When `body[t̄]` itself
//! holds a quantifier, that quantifier gets a proxy of its own, and the
//! E-matching rounds instantiate it in turn. Verus writes such a universal for
//! `let b = forall|x| P(x) ==> forall|z| R(x, z)`, as `(= b (forall ...))`
//! (`triggers::test_lets_and_nested_quantifiers_issue1347`).
//!
//! Ground truth for every fixture was checked with z3 4.12.5 with MBQI off,
//! as Verus runs it. Each refutable fixture has a satisfiable twin one line
//! apart, which must never be refuted in either posture.

/// The universal sits in a disjunct the problem forces through a chain the
/// unit refinement does not see, so it is not entailed and is a proxy target;
/// its instance at `x := 7` holds the inner universal.
/// **GROUND TRUTH: UNSAT** (`(R 7 20)` follows from the inner universal).
const NESTED_UNDER_DISJUNCT: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun R (Int Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (! (=> (P x) (forall ((z Int)) (! (R x z) :pattern ((R x z))))) :pattern ((P x))))))
(assert (or (not c) d))
(assert (not d))
(assert (P 7))
(assert (not (R 7 20)))
(check-sat)
"#;

/// `NESTED_UNDER_DISJUNCT` with the denied atom at `x := 8`, which no
/// instance reaches. **GROUND TRUTH: SAT.**
const NESTED_UNDER_DISJUNCT_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun R (Int Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (! (=> (P x) (forall ((z Int)) (! (R x z) :pattern ((R x z))))) :pattern ((P x))))))
(assert (or (not c) d))
(assert (not d))
(assert (P 7))
(assert (not (R 8 20)))
(check-sat)
"#;

/// The Verus shape: the universal under a Boolean `=`, the inner one under a
/// `let` that names a term of the outer binder. **GROUND TRUTH: UNSAT.**
const NESTED_UNDER_EQUALITY: &str = r#"
(set-logic UFLIA)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun bar (Poly) Bool)
(declare-fun llama (Poly) Int)
(declare-fun foo (Poly Poly) Bool)
(declare-const b Bool)
(assert (not (=> (= b (forall ((x Poly)) (! (=> (bar x) (let ((y (llama x))) (forall ((z Poly)) (! (foo (I y) z) :pattern ((foo (I y) z)))))) :pattern ((bar x)))))
  (=> b (=> (bar (I 7)) (foo (I (llama (I 7))) (I 20)))))))
(check-sat)
"#;

/// `NESTED_UNDER_EQUALITY` with the goal at a term no instance reaches.
/// **GROUND TRUTH: SAT.**
const NESTED_UNDER_EQUALITY_SAT: &str = r#"
(set-logic UFLIA)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun bar (Poly) Bool)
(declare-fun llama (Poly) Int)
(declare-fun foo (Poly Poly) Bool)
(declare-const b Bool)
(assert (not (=> (= b (forall ((x Poly)) (! (=> (bar x) (let ((y (llama x))) (forall ((z Poly)) (! (foo (I y) z) :pattern ((foo (I y) z)))))) :pattern ((bar x)))))
  (=> b (=> (bar (I 7)) (foo (I (llama (I 8))) (I 20)))))))
(check-sat)
"#;

/// Two levels of nesting under the Boolean `=`. **GROUND TRUTH: UNSAT.**
const NESTED_TWICE: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int Int Int) Bool)
(declare-const b Bool)
(assert (= b (forall ((x Int)) (! (=> (P x) (forall ((y Int)) (! (=> (Q x y) (forall ((z Int)) (! (R x y z) :pattern ((R x y z))))) :pattern ((Q x y))))) :pattern ((P x))))))
(assert b)
(assert (P 1))
(assert (Q 1 2))
(assert (not (R 1 2 3)))
(check-sat)
"#;

/// `NESTED_TWICE` with the denied atom off the instantiated path.
/// **GROUND TRUTH: SAT.**
const NESTED_TWICE_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int Int Int) Bool)
(declare-const b Bool)
(assert (= b (forall ((x Int)) (! (=> (P x) (forall ((y Int)) (! (=> (Q x y) (forall ((z Int)) (! (R x y z) :pattern ((R x y z))))) :pattern ((Q x y))))) :pattern ((P x))))))
(assert b)
(assert (P 1))
(assert (Q 1 2))
(assert (not (R 1 3 3)))
(check-sat)
"#;

/// The inner universal in a NEGATIVE position of the instance: its proxy
/// must stay free, since nothing makes it true. The outer universal holds
/// with every `S` true and `T 1` false only if the inner one is false, which
/// a model can arrange. **GROUND TRUTH: SAT.**
const NESTED_NEGATIVE_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun S (Int Int) Bool)
(declare-fun T (Int) Bool)
(declare-fun U (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (! (=> (U x) (=> (forall ((y Int)) (! (S x y) :pattern ((S x y)))) (T x))) :pattern ((U x))))))
(assert (or (not c) d))
(assert (not d))
(assert (U 1))
(assert (S 1 5))
(assert (not (T 1)))
(check-sat)
"#;

/// `NESTED_NEGATIVE_SAT` with the inner universal's body made a tautology,
/// so it is true and forces `T 1`. **GROUND TRUTH: UNSAT.** It is not
/// required to be refuted (nothing ties a free proxy to its universal's truth
/// when the universal is valid); it pins that the twin's verdict differs for
/// the right reason.
const NESTED_NEGATIVE: &str = r#"
(set-logic UFLIA)
(declare-fun S (Int Int) Bool)
(declare-fun T (Int) Bool)
(declare-fun U (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (! (=> (U x) (=> (forall ((y Int)) (! (or (S x y) (not (S x y))) :pattern ((S x y)))) (T x))) :pattern ((U x))))))
(assert (or (not c) d))
(assert (not d))
(assert (U 1))
(assert (S 1 5))
(assert (not (T 1)))
(check-sat)
"#;

/// A guarded universal whose trigger meets a ground term only through an
/// equality an entailed instance supplies, `(K 0) = (G 5)`.
/// **GROUND TRUTH: UNSAT.**
const GUARDED_AFTER_INSTANCE_EQUALITY: &str = r#"
(set-logic UFLIA)
(declare-fun G (Int) Int)
(declare-fun F (Int) Bool)
(declare-fun H (Int) Bool)
(declare-fun K (Int) Int)
(declare-fun A (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (forall ((u Int)) (! (=> (A u) (= (K u) (G 5))) :pattern ((A u)))))
(assert (or c (forall ((y Int)) (! (=> (F (G y)) (H y)) :pattern ((F (G y)))))))
(assert (or (not c) d))
(assert (not d))
(assert (A 0))
(assert (F (K 0)))
(assert (not (H 5)))
(check-sat)
"#;

/// `GUARDED_AFTER_INSTANCE_EQUALITY` with `H` denied where no instance
/// reaches. **GROUND TRUTH: SAT.**
const GUARDED_AFTER_INSTANCE_EQUALITY_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun G (Int) Int)
(declare-fun F (Int) Bool)
(declare-fun H (Int) Bool)
(declare-fun K (Int) Int)
(declare-fun A (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (forall ((u Int)) (! (=> (A u) (= (K u) (G 5))) :pattern ((A u)))))
(assert (or c (forall ((y Int)) (! (=> (F (G y)) (H y)) :pattern ((F (G y)))))))
(assert (or (not c) d))
(assert (not d))
(assert (A 0))
(assert (F (K 0)))
(assert (not (H 6)))
(check-sat)
"#;

/// A negated existential in a disjunct the problem forces: its dual universal
/// `∀x.¬(P x)` is guarded by the existential's proxy
/// (#guarded-existential-duals). **GROUND TRUTH: UNSAT.**
const EXISTENTIAL_IN_DISJUNCT: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (not (exists ((x Int)) (! (P x) :pattern ((P x)))))))
(assert (or (not c) d))
(assert (not d))
(assert (P 3))
(check-sat)
"#;

/// `EXISTENTIAL_IN_DISJUNCT` with the witness denied. **GROUND TRUTH: SAT.**
const EXISTENTIAL_IN_DISJUNCT_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (not (exists ((x Int)) (! (P x) :pattern ((P x)))))))
(assert (or (not c) d))
(assert (not d))
(assert (not (P 3)))
(check-sat)
"#;

/// An existential in the antecedent of a guarded instance: its witness
/// `(S 1 5)` makes it true through its dual's guarded clause, which forces
/// `(T 1)`. **GROUND TRUTH: UNSAT.**
const NESTED_EXISTENTIAL_ANTECEDENT: &str = r#"
(set-logic UFLIA)
(declare-fun S (Int Int) Bool)
(declare-fun T (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (! (=> (exists ((y Int)) (! (S x y) :pattern ((S x y)))) (T x)) :pattern ((T x))))))
(assert (or (not c) d))
(assert (not d))
(assert (S 1 5))
(assert (not (T 1)))
(check-sat)
"#;

/// `NESTED_EXISTENTIAL_ANTECEDENT` with `T` denied where no witness exists.
/// **GROUND TRUTH: SAT.**
const NESTED_EXISTENTIAL_ANTECEDENT_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun S (Int Int) Bool)
(declare-fun T (Int) Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (! (=> (exists ((y Int)) (! (S x y) :pattern ((S x y)))) (T x)) :pattern ((T x))))))
(assert (or (not c) d))
(assert (not d))
(assert (S 1 5))
(assert (not (T 2)))
(check-sat)
"#;

/// Verdicts with the proof cycle shed, the CLI's `--z3-mode` posture.
fn proof_shed_verdicts(smt: &str) -> Vec<String> {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_competition_mode(true);
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"))
        .iter()
        .map(|line| line.trim().to_string())
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

fn assert_never_unsat(name: &str, smt: &str) {
    for results in [
        proof_shed_verdicts(smt),
        crate::common::solve_vec(smt),
        crate::common::solve_selfcheck_vec(smt),
    ] {
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER ({name}): this problem is SATISFIABLE. A nested \
             quantifier's proxy is a free Boolean outside the clauses that \
             guard its own instances, so no refutation may rest on it being \
             true. Got {results:?}"
        );
    }
}

/// The refutable fixtures are refuted in the `--z3-mode` posture.
#[test]
fn quantifiers_nested_in_guarded_instances_are_instantiated() {
    for (name, smt) in [
        ("nested under a disjunct", NESTED_UNDER_DISJUNCT),
        ("nested under a Boolean =", NESTED_UNDER_EQUALITY),
        ("nested twice", NESTED_TWICE),
        ("negated existential in a disjunct", EXISTENTIAL_IN_DISJUNCT),
        (
            "nested existential antecedent",
            NESTED_EXISTENTIAL_ANTECEDENT,
        ),
    ] {
        let got = proof_shed_verdicts(smt);
        assert_eq!(
            got,
            ["unsat"],
            "{name}: the nested universal refutes the goal"
        );
    }
}

/// A guarded universal is instantiated at a binding only an instance's
/// equality supplies.
#[test]
fn a_guarded_universal_is_instantiated_after_an_instance_equality() {
    let got = proof_shed_verdicts(GUARDED_AFTER_INSTANCE_EQUALITY);
    assert_eq!(got, ["unsat"]);
}

/// Every satisfiable twin stays unrefuted in every posture.
#[test]
fn nested_and_interleaved_guarded_instances_never_refute_a_satisfiable_query() {
    for (name, smt) in [
        ("nested under a disjunct", NESTED_UNDER_DISJUNCT_SAT),
        ("nested under a Boolean =", NESTED_UNDER_EQUALITY_SAT),
        ("nested twice", NESTED_TWICE_SAT),
        ("nested in a negative position", NESTED_NEGATIVE_SAT),
        (
            "guarded after an instance equality",
            GUARDED_AFTER_INSTANCE_EQUALITY_SAT,
        ),
        (
            "negated existential in a disjunct",
            EXISTENTIAL_IN_DISJUNCT_SAT,
        ),
        (
            "nested existential antecedent",
            NESTED_EXISTENTIAL_ANTECEDENT_SAT,
        ),
    ] {
        assert_never_unsat(name, smt);
    }
}

/// The negative-position twin is never answered `sat`: the proxy
/// abstraction forbids it, whatever the guarded clauses say.
#[test]
fn a_negative_nested_universal_is_never_answered_sat() {
    for results in [
        proof_shed_verdicts(NESTED_NEGATIVE),
        crate::common::solve_vec(NESTED_NEGATIVE),
    ] {
        assert!(
            !results.iter().any(|r| r == "sat"),
            "WRONG ANSWER: NESTED_NEGATIVE is UNSATISFIABLE; got {results:?}"
        );
    }
}
