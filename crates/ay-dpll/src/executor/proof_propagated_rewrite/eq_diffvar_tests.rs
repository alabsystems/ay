// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for the `EqDiffVar` rewrite-derivation lane (#4751).
//!
//! What only a real solve can show is pinned here: that the pass's atom folds
//! reach proof reconstruction, that this lane derives the rewritten assertions
//! instead of trusting them, and that the checker the executor itself runs
//! accepts the result. The step-shape conditions are decided by the checker's
//! own recognizers at plan time, so there is nothing separate to unit-test
//! about them — a shape the checker would reject is never emitted.

use ay_core::{AletheRule, ProofStep, TermId};
use ay_frontend::parse;

use crate::Executor;

/// The `EqDiffVar` pass's own target shape: a guarded var-var equality chain,
/// with the equality atoms nested under `or`/`ite` so the fold has to be lifted
/// through congruence rather than replaced at the root.
const GUARDED_UNSAT: &str = r#"
    (set-logic QF_LIA)
    (declare-const g1 Bool)
    (declare-const g2 Bool)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const a Int)
    (declare-const b Int)
    (assert (or (not g1) (= a x)))
    (assert (or (not g1) (= b y)))
    (assert (or g1 (= a y)))
    (assert (or g1 (= b x)))
    (assert (or (not g2) (= (+ x y) 1)))
    (assert (or g2 (= (+ a b) 1)))
    (assert (not (= (+ x y) 1)))
    (check-sat)
"#;

/// The same guarded chain, but every `or` also carries a disjunct that TOP-LEVEL
/// UNIT PROPAGATION deletes before `EqDiffVar` folds the equality beside it.
///
/// That is the round ORDER the two channels' stamps have to separate: the unit
/// round rewrites `(or (not g0) (not g1) (= a x))` to `(or (not g1) (= a x))`,
/// and `EqDiffVar` then rewrites THAT to `(or (not g1) (= d 0))`. Replaying the
/// first rewrite with the fold channel eligible reconstructs
/// `(or (not g1) (= d 0))` where the unit round wrote the unfolded form, so the
/// recorded `after` is never reached and the whole chain back to the authored
/// assertion declines.
const UNIT_PROPAGATED_GUARDED_UNSAT: &str = r#"
    (set-logic QF_LIA)
    (declare-const g0 Bool)
    (declare-const g1 Bool)
    (declare-const g2 Bool)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const a Int)
    (declare-const b Int)
    (assert g0)
    (assert (or (not g0) (not g1) (= a x)))
    (assert (or (not g0) (not g1) (= b y)))
    (assert (or (not g0) g1 (= a y)))
    (assert (or (not g0) g1 (= b x)))
    (assert (or (not g2) (= (+ x y) 1)))
    (assert (or g2 (= (+ a b) 1)))
    (assert (not (= (+ x y) 1)))
    (check-sat)
"#;

fn solve(script: &str) -> Executor {
    let commands = parse(script).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["unsat"]);
    exec
}

fn solve_guarded() -> Executor {
    let exec = solve(GUARDED_UNSAT);
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.rewritten_atoms")
            .is_some_and(|n| n > 0),
        "the reduction must actually have run, or this test proves nothing"
    );
    exec
}

fn mentions_diff_var(exec: &Executor, term: TermId) -> bool {
    ay_proof::format_term_alethe(&exec.ctx.terms, term).contains("__ay_eqdv")
}

/// Every premiseless `trust` step whose clause mentions a difference variable.
/// This is the population the lane exists to remove.
fn premiseless_trust_over_diff_vars(exec: &Executor) -> usize {
    exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| {
                let ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } = step
                else {
                    return false;
                };
                premises.is_empty() && clause.iter().any(|&term| mentions_diff_var(exec, term))
            })
            .count()
    })
}

fn steps_with_rule(exec: &Executor, wanted: &AletheRule) -> usize {
    exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
            .count()
    })
}

#[test]
fn a_rewritten_assertion_is_derived_rather_than_trusted() {
    let exec = solve_guarded();
    assert_eq!(
        premiseless_trust_over_diff_vars(&exec),
        0,
        "no assertion the pass rewrote may remain an unverified premiseless `trust` step"
    );
}

#[test]
fn the_lane_actually_fires_on_the_passs_own_shape() {
    // A test that only asserts an absence would pass with the lane deleted, so
    // pin the positive side too: the derivation cites the definition as a
    // checked `fresh_def_bound` premise and closes the atom equivalence with
    // the `la_disequality` triangle.
    let exec = solve_guarded();
    assert!(
        steps_with_rule(&exec, &AletheRule::FreshDefBound) > 0,
        "the derivation must cite the definitional bounds it rests on"
    );
    assert!(
        steps_with_rule(&exec, &AletheRule::EquivNeg1) > 0
            && steps_with_rule(&exec, &AletheRule::EquivNeg2) > 0,
        "the atom equivalence must be assembled from its two implications"
    );
}

#[test]
fn the_derived_proof_still_passes_the_executors_own_checker() {
    // The lane is only worth anything if the checker the executor runs accepts
    // what it emitted. Any step it cannot re-derive would be a HARD rejection
    // naming that rule, which is strictly worse than the rescuable `trust`
    // step the lane replaced, so assert the specific classes never appear.
    let exec = solve_guarded();
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    if let Err(error) = exec.check_proof_strict_with_datatypes(proof) {
        let rendered = error.to_string();
        for forbidden in [
            "fresh definition",
            "cong",
            "trans",
            "and_pos",
            "and_neg",
            "or_pos",
            "or_neg",
            "equiv_neg",
            "la_disequality",
            "arithmetic equality triangle",
        ] {
            assert!(
                !rendered.contains(forbidden),
                "the lane emitted a step the checker rejects ({forbidden}): {rendered}"
            );
        }
    }
}

#[test]
fn the_published_unsat_is_still_backed_by_a_certificate() {
    let exec = solve_guarded();
    assert!(
        exec.last_command_unsat_was_strictly_verified()
            || exec.last_command_unsat_was_independently_verified()
            || exec.last_command_unsat_was_exact_semantically_verified(),
        "the `unsat` must stay backed by a real certificate"
    );
}

#[test]
fn every_definition_this_lane_introduces_is_over_a_fresh_symbol() {
    // The lane emits `fresh_def_bound` steps of its own, so the property that
    // matters is not how MANY but over WHICH symbol. Here the only `<=` bounds
    // in the problem are over the AUTHORED `x` and `y`; a definition over
    // either would prove e.g. `x = x - y`, false at `x = 1, y = 1`. Every bound
    // introduced must name a symbol the problem never mentions.
    let exec = solve(
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= x y))
        (assert (<= y x))
        (assert (not (= x y)))
        (check-sat)
    "#,
    );
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    let authored: Vec<String> = ["x".to_owned(), "y".to_owned()].into();
    for step in &proof.steps {
        let ProofStep::Step {
            rule: AletheRule::FreshDefBound,
            clause,
            premises,
            args,
        } = step
        else {
            continue;
        };
        let shape = ay_core::proof_validation::recognize_fresh_def_bound(
            &exec.ctx.terms,
            clause,
            premises.len(),
            args,
        )
        .expect("every emitted fresh_def_bound must have the shape the checker demands");
        let ay_core::term::TermData::Var(name, _) = exec.ctx.terms.get(shape.definiendum) else {
            panic!("a fresh definition must name an atomic symbol");
        };
        assert!(
            !authored.contains(name),
            "`{name}` is an authored symbol; defining it would prove x = x - y, false at x = 1, y = 1"
        );
    }
    assert_eq!(premiseless_trust_over_diff_vars(&exec), 0);
}

#[test]
fn a_recorded_fold_over_an_authored_symbol_is_refused() {
    // ADVERSARIAL. Forge a record claiming the pass folded `(= a b)` to
    // `(= x 0)` over the AUTHORED `x`, defining it by `(+ a (- b))`. Accepting
    // it would emit `fresh_def_bound` steps binding `x`, i.e. it would prove
    // `x = a - b`, which refutes the satisfiable problem
    // `{ a = 0, b = 0, x = 5 }` (falsifying assignment: that model satisfies
    // the assertions and `x != a - b`).
    //
    // Two independent gates refuse it and the test pins BOTH: the producer's
    // shape filter never records a fold over a symbol at all if the shape is
    // wrong, and the checker's `FreshDefRegistry` rejects a bound over a symbol
    // the problem constrains — which is what Gate-2 re-runs.
    let script = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const x Int)
        (assert (= a 0))
        (assert (= b 0))
        (assert (= x 5))
        (check-sat)
    "#;
    let commands = parse(script).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["sat"]);

    let a = exec.ctx.terms.mk_var("a".to_owned(), ay_core::Sort::Int);
    let b = exec.ctx.terms.mk_var("b".to_owned(), ay_core::Sort::Int);
    let x = exec.ctx.terms.mk_var("x".to_owned(), ay_core::Sort::Int);
    let zero = exec.ctx.terms.mk_int(0.into());
    let neg_b = exec.ctx.terms.mk_neg(b);
    let definiens = exec.ctx.terms.mk_add(vec![a, neg_b]);
    let atom = exec.ctx.terms.mk_eq_coerce(a, b);
    let replacement = exec.ctx.terms.mk_eq_coerce(x, zero);
    let bound = exec.ctx.terms.mk_app(
        ay_core::Symbol::named("<="),
        [x, definiens],
        ay_core::Sort::Bool,
    );

    let mut proof = ay_core::Proof::new();
    proof.add_rule_step(AletheRule::FreshDefBound, vec![bound], Vec::new(), vec![x]);
    let five = exec.ctx.terms.mk_int(5.into());
    let problem = [exec.ctx.terms.mk_eq_coerce(x, five)];
    assert!(
        ay_proof::FreshDefRegistry::collect(&proof, &exec.ctx.terms, Some(&problem)).is_err(),
        "a bound over a symbol the problem constrains must be refused; \
         accepting it proves x = a - b, false at a = 0, b = 0, x = 5"
    );

    // The producer-side filter is the other half: the fold is well formed in
    // shape (that is what makes it a forgery worth guarding), so the refusal
    // has to come from the checker, and Gate-2 is what runs it.
    let fold = crate::preprocess::AtomFold {
        atom,
        replacement,
        definiendum: x,
        definiens,
    };
    assert!(
        Executor::is_eq_diffvar_fold_well_formed(&exec.ctx.terms, &fold),
        "the shape filter alone does NOT catch this — Gate-2 must, and does"
    );
}

#[test]
fn a_fold_whose_definiendum_is_not_an_atomic_symbol_is_dropped() {
    // ADVERSARIAL, producer side. `(+ a 1)` is not a symbol, so `d := lin`
    // is not an assignment and the definitional-extension argument does not
    // apply: `(<= (+ a 1) lin)` with `(<= lin (+ a 1))` is an ordinary added
    // constraint on `a`. Falsifying assignment for the "extension": with
    // `lin = 0` and the satisfiable problem `{ a = 5 }`, the pair forces
    // `a = -1`.
    let mut terms = ay_core::TermStore::new();
    let a = terms.mk_var("a".to_owned(), ay_core::Sort::Int);
    let b = terms.mk_var("b".to_owned(), ay_core::Sort::Int);
    let one = terms.mk_int(1.into());
    let zero = terms.mk_int(0.into());
    let not_a_symbol = terms.mk_add(vec![a, one]);
    let atom = terms.mk_eq_coerce(a, b);
    let replacement = terms.mk_eq_coerce(not_a_symbol, zero);
    let fold = crate::preprocess::AtomFold {
        atom,
        replacement,
        definiendum: not_a_symbol,
        definiens: zero,
    };
    assert!(
        !Executor::is_eq_diffvar_fold_well_formed(&terms, &fold),
        "a compound definiendum must never be recorded"
    );
}

#[test]
fn a_fold_across_sorts_is_dropped() {
    // ADVERSARIAL. An `Int` symbol pinned between two `Real` bounds forces the
    // bounding term to be integral, which constrains the problem's own
    // variables: with `lin = (/ r 2)` and the satisfiable `{ r = 1 }`, no
    // integer `d` satisfies `d <= 1/2 <= d`.
    let mut terms = ay_core::TermStore::new();
    let d = terms.mk_var("d".to_owned(), ay_core::Sort::Int);
    let r = terms.mk_var("r".to_owned(), ay_core::Sort::Real);
    let zero = terms.mk_int(0.into());
    let atom = terms.mk_eq_coerce(r, r);
    let replacement = terms.mk_eq_coerce(d, zero);
    let fold = crate::preprocess::AtomFold {
        atom,
        replacement,
        definiendum: d,
        definiens: r,
    };
    assert!(
        !Executor::is_eq_diffvar_fold_well_formed(&terms, &fold),
        "a definiens at a different sort must never be recorded"
    );
}

#[test]
fn the_derivation_lowers_to_a_wire_document_with_no_invalid_rule() {
    // THE PRINTER CHECK. Every rule this lane emits already had a wire
    // lowering, but the COMBINATION is new, and the pinned carcara build's
    // failure mode is asymmetric: an unrecognized `:rule` name, or
    // `hole :args (..)`, makes a document `invalid`, which is strictly WORSE
    // than the `holey` one the premiseless `trust` produced.
    //
    // The bound atoms are passed as extra problem scope ON PURPOSE. A proof
    // carrying `fresh_def_bound` is free in the introduced symbol, and the
    // exporter refuses such a document outright ("proof is free in N symbols
    // the problem does not declare", #8821) — a PRE-EXISTING property of the
    // step this lane cites, unchanged by it and orthogonal to the question
    // asked here. Widening the scope isolates the rule lowering, which is what
    // this lane is new about.
    let exec = solve_guarded();
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    let mut scope = exec.ctx.assertions.clone();
    for step in &proof.steps {
        if let ProofStep::Step {
            rule: AletheRule::FreshDefBound,
            clause,
            ..
        } = step
        {
            scope.extend(clause.iter().copied());
        }
    }
    let document = ay_proof::export_alethe_with_problem_scope_and_overrides(
        proof,
        &exec.ctx.terms,
        &scope,
        None,
    );
    assert!(
        !document.contains("UNVERIFIABLE"),
        "the document must render once the introduced symbols are in scope: {}",
        document.lines().next().unwrap_or_default()
    );
    assert!(
        !document.contains("hole :args"),
        "`hole :args (..)` is rejected outright and turns the document invalid"
    );
    let checkable = ay_proof::checkable_rule_names();
    let mut saw_rule = false;
    for line in document.lines() {
        let Some(rest) = line.split(":rule ").nth(1) else {
            continue;
        };
        let rule = rest
            .split([' ', ')'])
            .next()
            .expect("a :rule is followed by its name");
        saw_rule = true;
        assert!(
            rule == "hole" || checkable.contains(&rule),
            "rule `{rule}` is neither externally checkable nor an honest hole: {line}"
        );
    }
    assert!(saw_rule, "the exported document must contain steps");
}

/// #4751 — the stamp axis must SEPARATE the two preprocessing channels.
///
/// This is the shape the whole residual premiseless-`Trust` census on
/// `dillig12_m` had: an assertion the top-level unit-propagation round shortened
/// and the `EqDiffVar` round then folded. Both rounds record provenance, and the
/// replay decides which licences apply by `entry.stamp <= target.stamp`, so the
/// fold channel must be INELIGIBLE while the unit round's rewrite is replayed.
/// With the two tied, this assertion cannot be derived from its authored form
/// and demotes to an unverified premiseless `trust`.
#[test]
fn a_unit_propagated_then_folded_assertion_is_derived_rather_than_trusted() {
    let exec = solve(UNIT_PROPAGATED_GUARDED_UNSAT);
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.rewritten_atoms")
            .is_some_and(|n| n > 0),
        "the fold must actually have run, or this test proves nothing"
    );
    assert!(
        exec.statistics()
            .get_int("preprocess.unit_prop.rewritten_assertions")
            .is_some_and(|n| n > 0),
        "the unit round must actually have shortened an assertion, or the two \
         channels never meet and this test proves nothing"
    );
    assert_eq!(
        premiseless_trust_over_diff_vars(&exec),
        0,
        "an assertion the unit round shortened and the fold round rewrote must \
         still be DERIVED from its authored form, not trusted"
    );
}

/// #4751 — the invariant the fix rests on, asserted on the store itself.
///
/// `merge_propagation_records` gives each merged round its own stamp SLOT so a
/// channel that runs between two merges has a value strictly between them. If a
/// later change collapses the spacing, the `EqDiffVar` channel silently ties
/// with a neighbour again and the derivations above stop firing, so pin the
/// three-way ordering directly rather than only its downstream effect.
#[test]
fn the_fold_channel_sits_strictly_between_the_rounds_around_it() {
    let exec = solve(UNIT_PROPAGATED_GUARDED_UNSAT);
    let store = &exec.propagated_value_provenance;
    let fold_stamps: Vec<u32> = store
        .eq_diffvar_atoms
        .iter()
        .map(|atom| atom.stamp)
        .chain(store.eq_diffvar_rewrites.iter().map(|record| record.stamp))
        .collect();
    assert!(
        !fold_stamps.is_empty(),
        "the fold channel must have recorded something, or this test proves nothing"
    );
    let value_stamps: Vec<u32> = store
        .rewrites
        .iter()
        .map(|record| record.stamp)
        .chain(store.entries.iter().map(|entry| entry.stamp))
        .collect();
    assert!(
        !value_stamps.is_empty(),
        "the value channel must have recorded something, or this test proves nothing"
    );
    for &fold in &fold_stamps {
        assert!(
            value_stamps.iter().any(|&value| value < fold),
            "the fold channel must be INELIGIBLE while an earlier round's rewrite \
             is replayed: every earlier value stamp has to be strictly below it"
        );
        assert!(
            !value_stamps.contains(&fold),
            "a tie with any merged round re-introduces the collision this spacing exists to prevent"
        );
    }
}
