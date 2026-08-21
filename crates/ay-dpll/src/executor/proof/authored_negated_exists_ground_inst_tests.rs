// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the negated-existential ground-instantiation artifact-firewall
//! translation.
//!
//! Split from the producer so the producer stays inside the repository's
//! unwaived 500-line file ratchet. Every test here is a GUARD-REMOVAL proof
//! for one fail-closed leg of that lane.

use super::*;

fn executor_with_assertions(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("negated-exists fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("negated-exists fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec
}

/// The Inc FPArith shape, in the cheapest theory that reproduces it: a
/// ground fact plus a negated existential whose body is true at a ground
/// term occurring only INSIDE that body.
const REFUTABLE: &str = r#"
    (set-logic UFLIA)
    (declare-const y Int)
    (assert (= y 0))
    (assert (not (exists ((d Int)) (and (>= d 0) (<= d 16) (= (- 0 d) y)))))
"#;

#[test]
fn translates_the_negated_exists_ground_instance_to_a_strict_proof() {
    let mut exec = executor_with_assertions(REFUTABLE);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        exec.try_translate_negated_exists_ground_instantiation_unsat(),
        "d := 0 refutes the negated existential against (= y 0)"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::QntNegExists,
                ..
            }
        )),
        "the certificate derives the dual universal via qnt_neg_exists"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )),
        "the certificate instantiates that universal via forall_inst"
    );
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let authored = exec.exact_concrete_authored_scope();
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok(),
        "every reachable assume must be an exact authored root"
    );

    // The certificate must also have a PROBLEM-SCOPED Alethe surface: an
    // external checker reads the original problem file, so a document that
    // needs a declaration of its own is not a certificate of that problem.
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &authored,
        None,
    )
    .expect("the certificate is resolvable from the problem scope");
    // Captured unless the run asks for `--nocapture`; this is how the
    // artifact is lifted out for an external carcara replay.
    println!("{document}");
    assert!(document.contains(":rule forall_inst"));
    assert!(
        !document.contains("(declare-"),
        "a certificate may never declare a symbol the problem does not have"
    );
    assert!(
        !document.contains(":rule trust"),
        "a trust step is not a proof; the honest escape hatch is `hole`"
    );
}

#[test]
fn satisfiable_query_cannot_mint_a_certificate() {
    // GUARD-REMOVAL PROOF: the same shape whose existential is genuinely
    // unwitnessed. No instance set refutes it, so the probe declines and
    // nothing installs.
    let mut exec = executor_with_assertions(
        r#"
            (set-logic UFLIA)
            (declare-const y Int)
            (assert (= y 5))
            (assert (not (exists ((d Int)) (and (>= d 0) (<= d 3) (= d y)))))
        "#,
    );
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        !exec.try_translate_negated_exists_ground_instantiation_unsat(),
        "a satisfiable query must never mint a refutation"
    );
    assert!(exec.last_proof.is_none());
}

#[test]
fn a_positive_exists_root_is_not_a_source() {
    // GUARD-REMOVAL PROOF: only a NEGATED existential entails the dual
    // universal. A positive one must be refused outright.
    let mut exec = executor_with_assertions(
        r#"
            (set-logic UFLIA)
            (declare-const y Int)
            (assert (= y 0))
            (assert (exists ((d Int)) (and (>= d 0) (= d y))))
        "#,
    );
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(!exec.try_translate_negated_exists_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());
}

#[test]
fn lane_attempt_budget_is_enforced() {
    // GUARD-REMOVAL PROOF (attempt budget): the identical executor
    // translates with a fresh budget (sibling test above); an exhausted
    // budget must decline without touching proof state.
    let mut exec = executor_with_assertions(REFUTABLE);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    exec.negated_exists_ground_inst_attempts
        .set(MAX_LANE_ATTEMPTS);
    assert!(!exec.try_translate_negated_exists_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());
}

#[test]
fn witnesses_mentioning_a_bound_name_are_not_proposed() {
    // NOT A GUARD-REMOVAL PROOF, and it was labelled as one. Review measured
    // that the assertion below is a TAUTOLOGY: `ground_witnesses_for_sort`
    // already filters by `term_avoids_names`, so re-asserting it cannot fail
    // for any implementation — and this test passed unchanged with the whole
    // translation stubbed to `return false`.
    //
    // It is kept as a CONTRACT test (the scan yields ground Int terms and none
    // mention a binder), not as evidence that the filter is load-bearing. The
    // filter in fact cannot fire at all: `ground_instantiation_candidates` has
    // no `Forall`/`Exists` arm, so it never descends under a binder and never
    // produces a term containing a `Var`. The premise stated here — "the raw
    // candidate scan descends into the existential body" — is false.
    //
    // The lane's real barrier is
    // `translates_the_negated_exists_ground_instance_to_a_strict_proof`, which
    // FAILS when the translation is stubbed.
    let exec = executor_with_assertions(REFUTABLE);
    let authored = exec.ctx.assertions.clone();
    let bound = exec.authored_binder_names(&authored);
    // The elaborator may alpha-rename, so read the binder off the root
    // rather than assuming the source spelling survived.
    let roots = exec.exact_authored_negated_exists_roots(&authored);
    let (_, _, bindings, _) = roots
        .first()
        .expect("the fixture asserts (not (exists ...))");
    assert!(
        bindings.iter().all(|(name, _)| bound.contains(name)),
        "every binder of the authored existential must be collected"
    );
    let witnesses = exec.ground_witnesses_for_sort(&authored, &Sort::Int, &bound);
    assert!(!witnesses.is_empty(), "the fixture has ground Int terms");
    for &witness in &witnesses {
        assert!(
            exec.term_avoids_names(witness, &bound),
            "no proposed witness may mention a bound name"
        );
    }
}

#[test]
fn bounded_tuples_respects_its_limit_and_leads_with_the_diagonal() {
    let a = TermId(1);
    let b = TermId(2);
    let columns = vec![vec![a, b], vec![a, b]];
    let tuples = bounded_tuples(&columns, 3);
    assert_eq!(tuples.len(), 3);
    assert_eq!(tuples[0], vec![a, a]);
    assert_eq!(tuples[1], vec![b, b]);
    assert!(bounded_tuples(&columns, 0).is_empty());
}
