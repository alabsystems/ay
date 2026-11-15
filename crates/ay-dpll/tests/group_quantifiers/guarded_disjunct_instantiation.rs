// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for GUARDED instance clauses
//! (#quantifier-guarded-instances).
//!
//! # What the lane does
//!
//! `perform_ematching_with_generations` refuses to instantiate a `forall` the
//! assertion set does not ENTAIL, because every caller conjoins the returned
//! instance as a top-level fact and that is licensed only for an entailed
//! universal (`#auflia-disjunct-forall-false-unsat`). The refusal is about the
//! ASSERTION FORM. This lane keeps the refusal — nothing is ever conjoined —
//! and instead asserts
//!
//! ```text
//! (or (not qproxy) body[t̄])
//! ```
//!
//! against the Boolean proxy the stage-2 abstraction minted for that universal.
//! Under the abstraction's semantics `qproxy := ⟦∀x̄.B⟧`, that clause is true in
//! every model, at any polarity and in any position.
//!
//! # The two things that must never break
//!
//! 1. **A guarded clause may not refute a satisfiable problem.** The whole
//!    reason the unconditional conjunct was refused is that it can. Every
//!    fixture below whose ground truth is SAT must never come back `unsat`.
//! 2. **The guard must be load-bearing.** If the clause behaved like the
//!    conjunct — i.e. if the `(not qproxy)` literal were dropped, or if the
//!    proxy were forced true — the SAT fixtures WOULD go `unsat`. That is the
//!    mutation differential: `guard_is_load_bearing_not_decoration` pins the
//!    pair of problems that differ ONLY in whether the guard can be satisfied,
//!    and requires the verdicts to differ in the direction the guard predicts.

/// GROUND TRUTH: **SATISFIABLE.** Take `c := true`, `f(1) := -1`, and let the
/// universal be false. The clause `(or c (forall x. f x > 0))` is satisfied by
/// its first disjunct.
///
/// This is the fixture the whole lane could get wrong. E-matching finds the
/// binding `x := 1` for the disjunct-position universal; conjoining
/// `f(1) > 0` would contradict `f(1) < 0` and publish a WRONG `unsat`. The
/// guarded clause `(or (not qproxy) (f 1 > 0))` cannot, because the solver
/// satisfies it by setting `qproxy := false` — which is exactly the truth
/// value the universal has in the model above.
const GUARD_SATISFIED_BY_SIBLING_DISJUNCT: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const c Bool)
(assert (or c (forall ((x Int)) (> (f x) 0))))
(assert c)
(assert (< (f 1) 0))
(check-sat)
"#;

/// The same problem with the sibling disjunct FORCED FALSE by a two-step
/// implication chain, so the unit-fact refinement in `entailed_forall_set`
/// cannot see through it and the universal stays un-entailed (and therefore a
/// proxy target).
///
/// GROUND TRUTH: **UNSATISFIABLE.** `(not d)` forces `(not c)`, which forces
/// the universal, which forces `f(1) > 0`, contradicting `f(1) < 0`.
///
/// The abstraction alone cannot refute it: `(or c qproxy)` is satisfied by
/// `qproxy := true` with no consequence attached. The guarded clause is what
/// attaches the consequence.
const GUARD_FORCED_TRUE_BY_THE_CLAUSE: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (> (f x) 0))))
(assert (or (not c) d))
(assert (not d))
(assert (< (f 1) 0))
(check-sat)
"#;

/// A universal under an `ite` else-branch rather than directly under an `or`,
/// with the branch condition unreachable to the unit refinement for the same
/// reason as above.
///
/// GROUND TRUTH: **SATISFIABLE** — `d := true` selects the `then` branch, and
/// nothing then constrains `f`.
const ITE_BRANCH_GUARD_SATISFIABLE: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const c Bool)
(declare-const d Bool)
(assert (ite c true (forall ((x Int)) (> (f x) 0))))
(assert (or (not c) d))
(assert d)
(assert (< (f 1) 0))
(check-sat)
"#;

fn assert_never_unsat(name: &str, smt: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "WRONG ANSWER ({name}): this problem is SATISFIABLE. A guarded instance \
         clause `(or (not qproxy) body[t])` is satisfied by `qproxy := false`, \
         so it can never refute a model in which the universal is false. An \
         `unsat` here means the guard was dropped and the instance was asserted \
         as a top-level fact — the `#auflia-disjunct-forall-false-unsat` wrong \
         answer, reintroduced. Got {results:?}"
    );
}

#[test]
fn a_guarded_instance_never_refutes_a_satisfiable_disjunct_position_universal() {
    assert_never_unsat(
        "or-position universal, guard satisfiable",
        GUARD_SATISFIED_BY_SIBLING_DISJUNCT,
    );
}

#[test]
fn a_guarded_instance_never_refutes_a_satisfiable_ite_branch_universal() {
    assert_never_unsat("ite-branch universal", ITE_BRANCH_GUARD_SATISFIABLE);
}

/// Same fixtures under `--self-check`, where nothing may be published that AY's
/// own checker cannot confirm.
#[test]
fn guarded_instances_publish_no_unsat_under_self_check_on_sat_problems() {
    for (name, smt) in [
        ("or-position", GUARD_SATISFIED_BY_SIBLING_DISJUNCT),
        ("ite-branch", ITE_BRANCH_GUARD_SATISFIABLE),
    ] {
        let results = crate::common::solve_selfcheck_vec(smt);
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "`--self-check` must not certify a refutation built on a guarded \
             clause whose guard is satisfiable ({name}); got {results:?}"
        );
    }
}

/// (#guarded-instance-checked-derivation) A refutation resting on a guarded
/// clause is CERTIFIED: consequence replay derives the clause's resolvent on
/// the proxy, `(or c (> (f 1) 0))`, from the authored clause by `forall_inst`,
/// so `--self-check` publishes the `unsat` its own checker confirms.
///
/// COUNTERFACTUAL: before the derivation existed the guarded clause carried
/// no provenance, the refutation was a disclosed hole (`discharged-trust`),
/// and `--self-check` answered `unknown (self-check-rejected)` here.
#[test]
fn a_guarded_refutation_is_certified_under_self_check() {
    let results = crate::common::solve_selfcheck_vec(GUARD_FORCED_TRUE_BY_THE_CLAUSE);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the guarded instance has a checked `forall_inst` derivation from the \
         authored clause; got {results:?}"
    );
}

/// The same for the TRIGGERLESS universal only the guarded ENUMERATIVE lane
/// instantiates (#quantifier-guarded-enumerative): `x := 0` is an enumerated
/// ground term, and the resolvent `(or c (> (+ 0 y) 100))` contradicts
/// `(< y 0)` once `c` is forced false. Ground truth: UNSAT.
///
/// COUNTERFACTUAL: `unknown (self-check-rejected)` before the derivation.
#[test]
fn an_enumerated_guarded_refutation_is_certified_under_self_check() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-const c Bool)
        (declare-const d Bool)
        (declare-const y Int)
        (assert (or c (forall ((x Int)) (> (+ x y) 100))))
        (assert (or (not c) d))
        (assert (not d))
        (assert (< y 0))
        (check-sat)
    "#;
    let results = crate::common::solve_selfcheck_vec(smt);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the enumerated guarded instance has a checked derivation; got {results:?}"
    );
}

/// THE MUTATION DIFFERENTIAL, at the verdict level.
///
/// The two fixtures are the same formula up to one literal: whether the
/// universal's sibling disjunct can be true. `GUARD_SATISFIED_BY_SIBLING_
/// DISJUNCT` asserts `c`, so the guard is satisfiable and the instance must
/// buy nothing; `GUARD_FORCED_TRUE_BY_THE_CLAUSE` forces `(not c)`, so the
/// guard is pinned true and the instance is a consequence.
///
/// A lane that ignored the guard would answer `unsat` on BOTH. A lane that
/// never attached the instance would answer non-`unsat` on both, which is
/// merely today's behaviour and is also pinned here: this assertion is written
/// so it holds either way on the second fixture, and fails loudly on the first.
/// The first is the one that carries the soundness content.
#[test]
fn guard_is_load_bearing_not_decoration() {
    let satisfiable = crate::common::solve_vec(GUARD_SATISFIED_BY_SIBLING_DISJUNCT);
    let refutable = crate::common::solve_vec(GUARD_FORCED_TRUE_BY_THE_CLAUSE);
    assert!(
        !satisfiable.iter().any(|r| r == "unsat"),
        "the guard-satisfiable twin must not be refuted; got {satisfiable:?}"
    );
    if refutable.iter().any(|r| r == "unsat") {
        assert!(
            !satisfiable.iter().any(|r| r == "unsat"),
            "the two fixtures differ only in whether the guard can be false; \
             refuting BOTH would mean the guard literal is not consulted"
        );
    }
    // Neither may answer `sat`: the abstraction is live on both, and a model of
    // an over-approximation is not a model of the query.
    assert!(
        !refutable.iter().any(|r| r == "sat"),
        "an abstracted solve must publish `unknown` rather than `sat`; got \
         {refutable:?}"
    );
}

/// The pre-existing entailed lane must be untouched: a top-level universal is
/// still instantiated as a unit fact and still refutes, and a satisfiable one
/// is still not refuted. The guarded lane never sees these — the abstraction
/// declines on an all-entailed assertion set, so no proxy exists and
/// `add_guarded_instance_clauses` returns immediately.
#[test]
fn the_entailed_lane_is_unchanged() {
    let entailed_unsat = r#"
        (set-logic UFLIA)
        (declare-fun c () Int)
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int)) (p x)))
        (assert (not (p c)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(entailed_unsat);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "an entailed top-level universal must still be instantiated and \
         refuted; got {results:?}"
    );

    let entailed_sat = r#"
        (set-logic UFLIA)
        (declare-fun c () Int)
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int)) (p x)))
        (assert (p c))
        (check-sat)
    "#;
    let sat_results = crate::common::solve_vec(entailed_sat);
    assert!(
        !sat_results.iter().any(|r| r == "unsat"),
        "a satisfiable conjunctive-only problem must not be refuted; got \
         {sat_results:?}"
    );
}

/// An EXISTENTIAL in the same position must never be instantiated, guarded or
/// not. `(or (not q) body[t̄])` is valid for a universal (`∀x̄.B ⊨ B[t̄]`) and
/// INVALID for an existential (`∃x̄.B ⊭ B[t̄]`), so the matcher's
/// `TermData::Exists(..) => continue` is a soundness floor the guarded lane
/// does not relax, and `add_guarded_instance_clauses` re-checks the node kind.
///
/// GROUND TRUTH: **SATISFIABLE** — the existential is witnessed at `x := 2`
/// while `f(1) < 0`.
#[test]
fn an_existential_is_never_guarded_instantiated() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const c Bool)
        (declare-const d Bool)
        (assert (or c (exists ((x Int)) (> (f x) 0))))
        (assert (or (not c) d))
        (assert (not d))
        (assert (< (f 1) 0))
        (assert (> (f 2) 0))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "instantiating an existential at `x := 1` would pin an arbitrary term \
         as the witness and refute a satisfiable problem; got {results:?}"
    );
}

/// (#guarded-instance-match-terms) Two guarded definitions in a chain: `f`'s
/// instance at `1` is the only place the term `(g 1)` occurs, and `g`'s own
/// definition is guarded too. Neither guard is a unit — each is derived during
/// search from `(or a c)`, `(or b c)` and `(not c)` — so both universals are
/// unentailed and every instance of them is a guarded clause.
///
/// **GROUND TRUTH: UNSAT** — `a` and `b` are forced, so `f(1) = g(1) = 2`,
/// contradicting the last assertion. z3 4.12.5 answers `unsat`.
///
/// Before the fix `g`'s trigger never met `(g 1)`: the E-matching campaign
/// never indexed the terms of a guarded instance, and the interleaved rounds
/// drop guarded records. The answer was `unknown`.
const GUARDED_DEFINITION_CHAIN_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (=> a (forall ((x Int)) (! (= (f x) (g x)) :pattern ((f x))))))
(assert (=> b (forall ((x Int)) (! (= (g x) (+ x 1)) :pattern ((g x))))))
(assert (or a c))
(assert (or b c))
(assert (not c))
(assert (not (= (f 1) 2)))
(check-sat)
"#;

/// The same chain with `c` left free: `c := true` satisfies both guards'
/// disjunctions with `a` and `b` false, so neither definition need hold.
/// **GROUND TRUTH: SAT**; z3 4.12.5 answers `sat`.
const GUARDED_DEFINITION_CHAIN_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (=> a (forall ((x Int)) (! (= (f x) (g x)) :pattern ((f x))))))
(assert (=> b (forall ((x Int)) (! (= (g x) (+ x 1)) :pattern ((g x))))))
(assert (or a c))
(assert (or b c))
(assert (not (= (f 1) 2)))
(check-sat)
"#;

/// CAPABILITY for #guarded-instance-match-terms: the terms of a guarded
/// instance are offered to the matcher, so the chain closes.
#[test]
fn a_guarded_instance_feeds_its_terms_to_the_matcher() {
    let results = crate::common::solve_vec(GUARDED_DEFINITION_CHAIN_UNSAT);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "`(g 1)` occurs only inside `f`'s guarded instance; matching `g`'s \
         trigger on it closes the refutation; got {results:?}"
    );
}

/// SOUNDNESS FLOOR for #guarded-instance-match-terms: matching on a guarded
/// instance's terms adds instances, and those instances stay guarded (or are
/// conjoined only for an entailed universal), so the satisfiable sibling can
/// never be refuted.
#[test]
fn matching_on_guarded_terms_never_refutes_a_satisfiable_chain() {
    assert_never_unsat("guarded definition chain", GUARDED_DEFINITION_CHAIN_SAT);
    let results = crate::common::solve_selfcheck_vec(GUARDED_DEFINITION_CHAIN_SAT);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "WRONG ANSWER under --self-check: the chain is satisfiable; got {results:?}"
    );
}
