// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ===========================================================================
// Array extensionality diff-witness certification (#ext-diff-cert).
//
// The injected axiom `(= a b) ∨ ¬(= (select a k) (select b k))` is NOT a
// tautology, so promotion is only sound when the proof also records what `k`
// is. Each acceptance test below has a twin that breaks exactly one provenance
// condition and asserts the gate REJECTS.
// ===========================================================================

/// A stand-in parsed AST: only the assertion COUNT matters for the
/// parsed-prefix boundary these tests exercise.
fn parsed_placeholder() -> ay_frontend::command::Term {
    ay_frontend::command::Term::Symbol("problem".to_string())
}

/// `(not (= a b))` over two array constants, plus the extensionality axiom the
/// eager array lane injects for that pair, in the `Generic`/trust shape
/// `push_array_axiom_assertion_site` records.
#[cfg(test)]
fn ext_axiom_fixture() -> (Executor, Proof, TermId, TermId, TermId) {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("ext_a", array_sort.clone());
    let b = exec.ctx.terms.mk_var("ext_b", array_sort);
    let k =
        array_extensionality_witness(&mut exec.ctx.terms, &mut exec.array_ext_witness_cache, a, b)
            .expect("fixture must mint an active witness");
    let eq_ab = exec.ctx.terms.mk_eq(a, b);
    let not_eq_ab = exec.ctx.terms.mk_not(eq_ab);
    let sel_a = exec.ctx.terms.mk_select(a, k);
    let sel_b = exec.ctx.terms.mk_select(b, k);
    let sel_eq = exec.ctx.terms.mk_eq(sel_a, sel_b);
    let not_sel_eq = exec.ctx.terms.mk_not(sel_eq);
    let ext_axiom = exec.ctx.terms.mk_or(vec![eq_ab, not_sel_eq]);
    assert!(exec.array_ext_witness_cache.record_generated_clause(
        &exec.ctx.terms,
        ext_axiom,
        vec![ArrayExtWitnessBinding {
            witness: k,
            array_a: a,
            array_b: b,
        }],
    ));

    // The problem asserted the disequality; the extensionality axiom is the
    // SOLVER's own injection, appended AFTER the problem's parsed prefix (the
    // boundary `proof_original_problem_assertions` reads).
    exec.ctx
        .add_assertion_with_parsed(not_eq_ab, parsed_placeholder());
    exec.ctx.assertions.push(ext_axiom);

    let mut proof = Proof::new();
    proof.add_assume(not_eq_ab, None);
    proof.add_theory_lemma("array", vec![ext_axiom]);
    (exec, proof, a, b, k)
}

#[test]
fn injected_extensionality_axiom_is_promoted_with_a_witness_introduction() {
    let (mut exec, mut proof, a, b, k) = ext_axiom_fixture();
    exec.promote_array_extensionality_axioms(&mut proof);

    assert!(
        proof
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())),
        "the injected extensionality axiom must stop being a trust lemma"
    );
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArrayExtensionality,
                    ..
                }
            ))
            .count(),
        1
    );
    let intro = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                clause,
                premises,
                args,
            } => Some((clause.clone(), premises.clone(), args.clone())),
            _ => None,
        })
        .expect("promotion must append a witness introduction");
    assert!(
        intro.0.is_empty() && intro.1.is_empty(),
        "the introduction is a definition: no clause, no premises"
    );
    assert_eq!(intro.2, vec![k, a, b]);

    exec.unsat_proof_extensionality_certified(&proof)
        .then_some(())
        .expect("a freshly introduced, once-bound witness must certify");
}

#[test]
fn injected_deep_extensionality_axiom_promotes_every_witness_link() {
    let mut exec = Executor::new();
    let inner_sort = Sort::array(Sort::Int, Sort::Int);
    let outer_sort = Sort::array(Sort::Int, inner_sort.clone());
    let a = exec.ctx.terms.mk_var("deep_ext_a", outer_sort.clone());
    let b = exec.ctx.terms.mk_var("deep_ext_b", outer_sort);
    let k0 = deep_array_extensionality_witness(
        &mut exec.ctx.terms,
        &mut exec.array_ext_witness_cache,
        a,
        b,
        0,
        Sort::Int,
    )
    .expect("outer deep witness");
    let a1 = exec.ctx.terms.mk_select(a, k0);
    let b1 = exec.ctx.terms.mk_select(b, k0);
    let k1 = deep_array_extensionality_witness(
        &mut exec.ctx.terms,
        &mut exec.array_ext_witness_cache,
        a,
        b,
        1,
        Sort::Int,
    )
    .expect("inner deep witness");
    let a2 = exec.ctx.terms.mk_select(a1, k1);
    let b2 = exec.ctx.terms.mk_select(b1, k1);
    let eq_ab = exec.ctx.terms.mk_eq(a, b);
    let not_eq_ab = exec.ctx.terms.mk_not(eq_ab);
    let leaf_eq = exec.ctx.terms.mk_eq(a2, b2);
    let not_leaf_eq = exec.ctx.terms.mk_not(leaf_eq);
    let ext_axiom = exec.ctx.terms.mk_or(vec![eq_ab, not_leaf_eq]);
    assert!(exec.array_ext_witness_cache.record_generated_clause(
        &exec.ctx.terms,
        ext_axiom,
        vec![
            ArrayExtWitnessBinding {
                witness: k0,
                array_a: a,
                array_b: b,
            },
            ArrayExtWitnessBinding {
                witness: k1,
                array_a: a1,
                array_b: b1,
            },
        ],
    ));
    exec.ctx
        .add_assertion_with_parsed(not_eq_ab, parsed_placeholder());
    exec.ctx.assertions.push(ext_axiom);

    let mut proof = Proof::new();
    proof.add_assume(not_eq_ab, None);
    proof.add_theory_lemma("array", vec![ext_axiom]);
    exec.promote_array_extensionality_axioms(&mut proof);

    let intros: Vec<Vec<TermId>> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                args,
                ..
            } => Some(args.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(intros, vec![vec![k0, a, b], vec![k1, a1, b1]]);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayExtensionality,
            ..
        }
    )));
    assert!(
        exec.unsat_proof_extensionality_certified(&proof),
        "the whole deep witness chain must pass strict provenance validation"
    );
}

#[test]
fn injected_deep_extensionality_axiom_never_partially_promotes() {
    let mut exec = Executor::new();
    let inner_sort = Sort::array(Sort::Int, Sort::Int);
    let outer_sort = Sort::array(Sort::Int, inner_sort);
    let a = exec.ctx.terms.mk_var("partial_ext_a", outer_sort.clone());
    let b = exec.ctx.terms.mk_var("partial_ext_b", outer_sort);
    let k0 = deep_array_extensionality_witness(
        &mut exec.ctx.terms,
        &mut exec.array_ext_witness_cache,
        a,
        b,
        0,
        Sort::Int,
    )
    .expect("outer deep witness");
    let a1 = exec.ctx.terms.mk_select(a, k0);
    let b1 = exec.ctx.terms.mk_select(b, k0);
    let k1 = deep_array_extensionality_witness(
        &mut exec.ctx.terms,
        &mut exec.array_ext_witness_cache,
        a,
        b,
        1,
        Sort::Int,
    )
    .expect("inner deep witness");
    let a2 = exec.ctx.terms.mk_select(a1, k1);
    let b2 = exec.ctx.terms.mk_select(b1, k1);
    let eq_ab = exec.ctx.terms.mk_eq(a, b);
    let leaf_eq = exec.ctx.terms.mk_eq(a2, b2);
    let not_leaf_eq = exec.ctx.terms.mk_not(leaf_eq);
    let ext_axiom = exec.ctx.terms.mk_or(vec![eq_ab, not_leaf_eq]);
    assert!(exec.array_ext_witness_cache.record_generated_clause(
        &exec.ctx.terms,
        ext_axiom,
        vec![ArrayExtWitnessBinding {
            witness: k0,
            array_a: a,
            array_b: b,
        }],
    ));

    let mut proof = Proof::new();
    proof.add_theory_lemma("array", vec![ext_axiom]);
    exec.promote_array_extensionality_axioms(&mut proof);
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            ..
        }
    )));
    assert!(matches!(
        proof.steps.as_slice(),
        [ProofStep::TheoryLemma { kind, .. }] if kind.is_trust()
    ));
}

#[test]
fn promoted_extensionality_is_rejected_when_the_witness_is_not_fresh() {
    // SOUNDNESS CRUX. The problem itself constrains `__ay_ext_diff_1_2`, so the
    // clause is no longer a conservative extension and the gate must refuse it
    // even though the promotion produced a perfectly-shaped introduction.
    let (mut exec, mut proof, _a, _b, k) = ext_axiom_fixture();
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let pinned = exec.ctx.terms.mk_eq(k, zero);
    // The pinning constraint is a PROBLEM assertion, so it extends the parsed
    // prefix; the injected axiom stays after it.
    let injected = exec.ctx.assertions.pop().expect("injected axiom");
    exec.ctx
        .add_assertion_with_parsed(pinned, parsed_placeholder());
    exec.ctx.assertions.push(injected);

    exec.promote_array_extensionality_axioms(&mut proof);
    assert!(
        !exec.unsat_proof_extensionality_certified(&proof),
        "a witness the problem also constrains must not certify"
    );
}

#[test]
fn promoted_extensionality_is_rejected_when_the_introduction_names_another_pair() {
    let (mut exec, mut proof, a, _b, k) = ext_axiom_fixture();
    let c = exec
        .ctx
        .terms
        .mk_var("ext_c", Sort::array(Sort::Int, Sort::Int));
    exec.promote_array_extensionality_axioms(&mut proof);

    // Tamper: rebind the witness to a different array pair.
    for step in &mut proof.steps {
        if let ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            args,
            ..
        } = step
        {
            *args = vec![k, a, c];
        }
    }
    assert!(
        !exec.unsat_proof_extensionality_certified(&proof),
        "an introduction for a different pair must not certify the clause"
    );
}

#[test]
fn qf_ax_store_flat_permutation_that_is_consistent_stays_sat() {
    // The soundness twin: the SAME store chains, but WITHOUT the
    // `(not (= i1 i2))` premise the permutation argument needs. The two
    // endpoints may legitimately differ (take `i1 = i2`, `e1 != e2`), so the
    // bridge must not help manufacture a refutation.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a1 () (Array Index Element))
        (declare-fun b1 () (Array Index Element))
        (declare-fun b2 () (Array Index Element))
        (declare-fun c1 () (Array Index Element))
        (declare-fun c2 () (Array Index Element))
        (declare-fun i1 () Index)
        (declare-fun i2 () Index)
        (declare-fun e1 () Element)
        (declare-fun e2 () Element)
        (assert (= b1 (store a1 i1 e1)))
        (assert (= b2 (store b1 i2 e2)))
        (assert (= c1 (store a1 i2 e2)))
        (assert (= c2 (store c1 i1 e1)))
        (assert (not (= b2 c2)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_ne!(
        exec.execute_all(&commands).unwrap(),
        vec!["unsat"],
        "a satisfiable store-flat permutation must never be refuted"
    );
}

#[test]
fn promoted_extensionality_is_rejected_when_the_introduction_is_removed() {
    let (mut exec, mut proof, _a, _b, _k) = ext_axiom_fixture();
    exec.promote_array_extensionality_axioms(&mut proof);
    proof.steps.retain(|step| {
        !matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                ..
            }
        )
    });
    assert!(
        !exec.unsat_proof_extensionality_certified(&proof),
        "an extensionality lemma with no introduction must not certify"
    );
}

#[test]
fn one_witness_shared_by_two_array_pairs_is_never_promoted() {
    // The solver should never mint one witness for two pairs; if it somehow
    // did, no single introduction could be true, so NEITHER axiom is promoted
    // and both stay trust.
    let (mut exec, mut proof, a, _b, k) = ext_axiom_fixture();
    let c = exec
        .ctx
        .terms
        .mk_var("ext_c", Sort::array(Sort::Int, Sort::Int));
    let eq_ac = exec.ctx.terms.mk_eq(a, c);
    let sel_a = exec.ctx.terms.mk_select(a, k);
    let sel_c = exec.ctx.terms.mk_select(c, k);
    let sel_eq = exec.ctx.terms.mk_eq(sel_a, sel_c);
    let not_sel_eq = exec.ctx.terms.mk_not(sel_eq);
    let second_axiom = exec.ctx.terms.mk_or(vec![eq_ac, not_sel_eq]);
    assert!(exec.array_ext_witness_cache.record_generated_clause(
        &exec.ctx.terms,
        second_axiom,
        vec![ArrayExtWitnessBinding {
            witness: k,
            array_a: a,
            array_b: c,
        }],
    ));
    exec.ctx.assertions.push(second_axiom);
    proof.add_theory_lemma("array", vec![second_axiom]);

    exec.promote_array_extensionality_axioms(&mut proof);
    assert!(
        proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                ..
            }
        )),
        "a witness shared across pairs must produce no introduction at all"
    );
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()))
            .count(),
        2,
        "both axioms must stay uncertified trust lemmas"
    );
}

#[test]
fn a_problem_asserted_extensionality_shaped_clause_is_never_promoted() {
    // Promotion is limited to assertions the SOLVER injected. A clause of the
    // same shape written by the USER is a problem premise, not a Skolem
    // definition, and must keep its `assume` provenance.
    let (mut exec, _proof, _a, _b, _k) = ext_axiom_fixture();
    let ext_axiom = exec.ctx.assertions[1];
    exec.ctx.assertions.clear();
    exec.ctx
        .add_assertion_with_parsed(ext_axiom, parsed_placeholder());
    let mut proof = Proof::new();
    proof.add_assume(ext_axiom, None);

    exec.promote_array_extensionality_axioms(&mut proof);
    assert!(
        matches!(proof.steps.as_slice(), [ProofStep::Assume(_)]),
        "a problem-asserted clause must stay an assume, got {:?}",
        proof.steps
    );
}

#[test]
fn a_negated_forall_goal_with_required_artifact_certifies_strict_unsat() {
    // HISTORY. This fixture used to pin the fail-closed downgrade: the
    // surface-override work bound (c25240fc9c) misreported the authored
    // `(not (forall ...))` root as unboundable, the whole presentation was
    // poisoned to a bare trust step, and the required artifact was rejected
    // (`unknown`, SelfCheckRejected, proof revoked). The bound now mirrors
    // the collector's `not`-shell descent for negated universals
    // (#forall-goal-boundary), so the SAME query must publish a certified
    // `unsat` whose retained presentation passes the unchanged strict
    // checker. The general revocation contract ("a rejected required
    // presentation is revoked") remains covered by
    // `checked_sidecar_is_independent_of_an_unrequested_alethe_presentation`.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic LIA)
        (declare-const y Int)
        (declare-const p Bool)
        (assert (not (forall ((x Int)) (or (<= (+ x 0) y) p))))
        (assert p)
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unsat"]);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("a certified required presentation must be retained");
    ay_proof::check_proof_strict(proof, exec.terms())
        .expect("the retained presentation must pass the unchanged strict checker");
    assert_eq!(
        exec.get_reason_unknown(),
        None,
        "a certified publication records no unknown reason"
    );
}
