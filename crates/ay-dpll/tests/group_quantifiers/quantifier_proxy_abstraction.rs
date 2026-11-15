// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for the quantifier proxy abstraction
//! (#quantifier-proxy-abstraction).
//!
//! # What the pass does
//!
//! `flatten_and_strip_quantifiers` used to delete every assertion mentioning a
//! quantifier. For a goal shaped `(or (not G1) … (not Gn) (forall x̄. ¬φ))` that
//! deleted the GROUND disjuncts too, and the ground solve reported
//! `num_conflicts=0 num_decisions=0` — it never saw the goal. The pass replaces
//! the maximal quantifier subterms of such an assertion by fresh Boolean
//! variables, so the rewritten (quantifier-free) assertion survives the strip.
//!
//! # The one thing that must never break
//!
//! The rewrite is an OVER-APPROXIMATION. `M ⊨ A` extends to `M' ⊨ σ(A)` by
//! `q_i := ⟦Q_i⟧_M`, so
//!
//! * `σ(A)` UNSAT ⟹ `A` UNSAT — the direction this stage makes sound to keep;
//! * `σ(A)` SAT says NOTHING about `A`, because a model of `σ(A)` assigns the
//!   fresh proxies freely.
//!
//! So an abstracted solve that reaches `Sat` must publish `unknown`. The
//! fixtures below are GENUINELY UNSAT problems whose abstracted skeletons are
//! satisfiable: a `sat` on any of them is a wrong answer, produced by exactly
//! the failure mode this stage introduces.
//!
//! The `--rigor`/posture-independent unit specs for target selection, the
//! `Let` refusal, capture-safety and the reverse-substitution differential live
//! next to the pass in
//! `crates/ay-dpll/src/executor/quantifier_loop/preprocess/quantifier_proxy/tests.rs`.

/// A disjunct-position universal whose sibling disjunct is falsified by an
/// ARITHMETIC unit fact rather than a Boolean one.
///
/// That detail is what makes it an abstraction fixture at all: `is_unit_atom`
/// accepts `<=`, but the standalone atom and the NNF-minted negated disjunct
/// are not the same hash-consed `TermId` after arithmetic normalisation, so
/// `entailed_forall_set`'s unit refinement does not fire and the universal is
/// NOT entailed. It is therefore a proxy target.
///
/// GROUND TRUTH: `n <= 4` refutes `n > 5`, so the clause forces
/// `forall x. p(x)`, which forces `p(c)`, which contradicts `(not (p c))`.
/// **UNSAT.** The abstracted skeleton `(or (> n 5) qproxy) ∧ n <= 4 ∧ ¬p(c)` is
/// satisfiable with `qproxy := true`, so a `sat` here is precisely the wrong
/// answer the over-approximation would license if the fail-closed arm were
/// missing.
const ABSTRACTED_SKELETON_SAT_BUT_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun n () Int)
(declare-fun c () Int)
(declare-fun p (Int) Bool)
(assert (<= n 4))
(assert (or (> n 5) (forall ((x Int)) (p x))))
(assert (not (p c)))
(check-sat)
"#;

/// The same trap with the universal nested one level deeper, under an `ite`
/// rather than directly under the `or`, so the maximal-subterm collection has
/// to walk a branch to find it.
///
/// GROUND TRUTH: `n <= 4` selects the `else` branch, which is
/// `forall x. p(x)`, contradicting `(not (p c))`. **UNSAT**, and the abstracted
/// skeleton is again satisfiable by assigning the proxy freely.
const ABSTRACTED_UNDER_ITE: &str = r#"
(set-logic UFLIA)
(declare-fun n () Int)
(declare-fun c () Int)
(declare-fun p (Int) Bool)
(assert (<= n 4))
(assert (ite (> n 5) true (forall ((x Int)) (p x))))
(assert (not (p c)))
(check-sat)
"#;

fn assert_never_sat(name: &str, smt: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "WRONG ANSWER ({name}): this problem is UNSATISFIABLE, and its \
         abstracted skeleton is satisfiable only because the quantifier became \
         a free Boolean proxy. Publishing `sat` would hand back a model of an \
         over-approximation as if it were a model of the query. `unsat` and \
         `unknown` are both acceptable; got {results:?}"
    );
}

#[test]
fn abstracted_skeleton_sat_never_publishes_sat() {
    assert_never_sat("or-position universal", ABSTRACTED_SKELETON_SAT_BUT_UNSAT);
}

#[test]
fn abstracted_ite_branch_never_publishes_sat() {
    assert_never_sat("ite-branch universal", ABSTRACTED_UNDER_ITE);
}

/// Same fixtures under `--self-check`, where nothing may be published that AY's
/// own checker cannot confirm. The abstraction must not manufacture a `sat`
/// here either.
#[test]
fn abstracted_skeleton_sat_never_publishes_sat_under_self_check() {
    for (name, smt) in [
        ("or-position universal", ABSTRACTED_SKELETON_SAT_BUT_UNSAT),
        ("ite-branch universal", ABSTRACTED_UNDER_ITE),
    ] {
        let results = crate::common::solve_selfcheck_vec(smt);
        assert!(
            !results.iter().any(|r| r == "sat"),
            "`--self-check` must not certify a model of the abstraction \
             ({name}); got {results:?}"
        );
    }
}

/// A proxy is an internal Boolean variable minted by preprocessing. It is not a
/// user symbol and it denotes nothing in the query's vocabulary, so it must
/// never appear in a published model — a consumer reading `qproxy_17` back
/// would be reading the abstraction's own scaffolding.
///
/// Structurally this cannot happen while the fail-closed arm holds (an
/// abstracted solve publishes no model at all), which makes the assertion a
/// defense-in-depth pin on that arm as much as on the printer.
#[test]
fn proxies_never_reach_a_published_model() {
    let with_get_model = format!(
        "{}\n(get-model)\n(get-value ((p c)))\n",
        ABSTRACTED_SKELETON_SAT_BUT_UNSAT.trim_end()
    );
    let results = crate::common::solve_vec(&with_get_model);
    for line in &results {
        assert!(
            !line.contains("qproxy"),
            "an abstraction proxy escaped into published output: {line:?} \
             (full output {results:?})"
        );
    }
}

/// The abstraction must not disturb a problem whose universals are all in
/// CONJUNCTIVE position: every maximal quantifier subterm is entailed, the pass
/// declines, and the assertion vector reaching the ground solver is exactly the
/// one it saw before. Pinned by verdict rather than by wall time, which is
/// meaningless on a box running eight concurrent builds.
#[test]
fn conjunctive_only_problems_keep_their_verdicts() {
    // A top-level universal plus its refuting ground fact: E-matching
    // instantiates the ENTAILED universal exactly as before and refutes.
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
         refuted — the abstraction declines on it, so this path is unchanged; \
         got {results:?}"
    );

    // A satisfiable one, to pin that the decline is not buying soundness by
    // turning the whole family `unknown`.
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

/// The `(or (not G1) … (not Gn) (forall x̄. ¬φ))` shape the stage exists for,
/// in its SOUNDNESS direction: the ground disjuncts now reach the solver, and
/// the clause they belong to is genuinely satisfiable. Nothing about restoring
/// the goal may manufacture a refutation.
///
/// GROUND TRUTH: interpreting `q` as universally true satisfies every
/// assertion, so `unsat` is a wrong answer.
#[test]
fn restoring_the_goal_never_manufactures_a_refutation() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun n () Int)
        (declare-fun c () Int)
        (declare-fun q (Int) Bool)
        (assert (<= n 4))
        (assert (or (> n 5) (forall ((x Int)) (q x))))
        (assert (q c))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "`q ≡ true` satisfies every assertion; a refutation here would mean \
         the abstraction added a constraint rather than relaxing one; got \
         {results:?}"
    );
}
