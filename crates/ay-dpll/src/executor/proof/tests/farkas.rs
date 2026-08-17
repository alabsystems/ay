// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn test_failed_equality_farkas_promotion_stays_trusted_8866() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let x_eq_one = terms.mk_eq(x, one);
    let y_eq_two = terms.mk_eq(y, two);
    let clause = vec![terms.mk_not_raw(x_eq_one), terms.mk_not_raw(y_eq_two)];

    assert!(
        super::super::proof_farkas::synthesize_equality_farkas(&terms, &clause).is_none(),
        "precondition: the equality-specific Farkas synthesizer must fail"
    );

    let mut proof = Proof::new();
    let lemma_id = proof.add_theory_lemma("LIA", clause);

    Executor::promote_generic_theory_lemma_kinds_after_rewrite(&terms, &mut proof, None);

    let Some(ProofStep::TheoryLemma { kind, farkas, .. }) = proof.get_step(lemma_id) else {
        panic!("expected theory lemma step");
    };
    assert_eq!(
        *kind,
        TheoryLemmaKind::Generic,
        "failed Farkas synthesis must not leave LiaGeneric without coefficients"
    );
    assert!(farkas.is_none());

    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![lemma_id], vec![]);
    let report = ay_proof::terminal_trust_report(&proof);
    assert_eq!(report.trust_theory_lemma_on_path, 1);
    assert!(report.has_terminal_trust());

    let rendered = ay_proof::export_alethe(&proof, &terms);
    assert!(
        !rendered.contains("UNVERIFIABLE PROOF"),
        "failed synthesis must export as honest trust, not as an uncertified arithmetic rule:\n{rendered}"
    );
    // Terminal-trust detection reads the proof IR — `trust_theory_lemma_on_path`
    // and `has_terminal_trust()` are asserted above and are unchanged. The
    // printed name is `hole`: `trust` is not an Alethe rule, so emitting it
    // made the document `invalid` rather than merely unproved. `hole` is the
    // spec's placeholder and `terminal_trust` counts it identically
    // (`hole_rule_on_path`), so nothing becomes invisible.
    assert!(
        rendered.contains(":rule hole"),
        "failed synthesis should remain visible as an honest hole:\n{rendered}"
    );
    assert!(
        !rendered.contains(":rule trust"),
        "must not emit a rule name no Alethe checker implements:\n{rendered}"
    );
}

#[test]
fn c3_post_rewrite_promotion_declines_non_arithmetic_annotation_evidence() {
    use ay_core::{CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation};

    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let c = terms.mk_var("c", u);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let clause = vec![terms.mk_not_raw(eq_ab), terms.mk_not_raw(eq_bc), eq_ac];

    for (farkas, lia) in [
        (Some(FarkasAnnotation::from_ints(&[1, 1, 1])), None),
        (
            None,
            Some(LiaAnnotation::CuttingPlane(CuttingPlaneAnnotation {
                farkas: FarkasAnnotation::from_ints(&[1, 1, 1]),
                divisor: 2,
            })),
        ),
    ] {
        let mut proof = Proof::new();
        let lemma = proof.add_step(ProofStep::TheoryLemma {
            theory: "theory".to_string(),
            clause: clause.clone(),
            farkas: farkas.clone(),
            kind: TheoryLemmaKind::Generic,
            lia: lia.clone(),
        });

        Executor::promote_generic_theory_lemma_kinds_after_rewrite(&terms, &mut proof, None);

        let Some(ProofStep::TheoryLemma {
            kind,
            clause: retained,
            farkas: retained_farkas,
            lia: retained_lia,
            ..
        }) = proof.get_step(lemma)
        else {
            panic!("expected theory lemma");
        };
        assert_eq!(*kind, TheoryLemmaKind::Generic);
        assert_eq!(retained, &clause);
        assert_eq!(retained_farkas, &farkas);
        assert_eq!(retained_lia, &lia);
    }
}

#[test]
fn test_uncertified_arithmetic_lemma_kinds_demote_to_trust_8866() {
    let mut proof = Proof::new();
    let t = TermId::new(1);

    proof.add_step(ProofStep::TheoryLemma {
        theory: String::from("LRA"),
        clause: vec![t],
        farkas: None,
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    proof.add_step(ProofStep::TheoryLemma {
        theory: String::from("LIA"),
        clause: vec![t],
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });

    Executor::demote_uncertified_arithmetic_lemmas_to_trust(&mut proof);

    for step in &proof.steps {
        let ProofStep::TheoryLemma { kind, farkas, .. } = step else {
            panic!("expected theory lemma step");
        };
        assert_eq!(*kind, TheoryLemmaKind::Generic);
        assert!(farkas.is_none());
    }
}

#[test]
fn test_get_proof_no_check_sat() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (get-proof)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert!(outputs[0].contains("no check-sat has been performed"));
}

/// TrustVC's Ackermann termination gate proves the first lexicographic
/// component decreases under the `m != 0 && n == 0` path.  The formula is
/// linear integer arithmetic; a computed UNSAT must have a strict proof rather
/// than being withheld behind a Generic theory leaf.
#[test]
fn deductive_checks_ackermann_lexicographic_termination_is_strict_checkable() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-fun ack (Int Int) Int)
        (declare-const m Int)
        (declare-const n Int)
        (assert (! (<= 0 m) :named dn0))
        (assert (! (<= 0 n) :named dn1))
        (assert (!
          (and
            (< 0 m)
            (= 0 n)
            (or
              (and
                (or (< (+ m (- 1)) 0) (<= m (+ m (- 1))))
                (or (not (= m (+ m (- 1)))) (<= n 1)))
              (< m 0)
              (< n 0)))
          :named dn2))
        (check-sat)
    "#;
    let commands = parse(input).expect("TrustVC termination formula parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("formula executes");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "valid lexicographic decrease must carry a strict proof; retained={:#?}",
        exec.last_proof
    );
    let proof = exec.last_proof.as_ref().expect("proof after UNSAT");
    let quality = ay_proof::check_proof_strict(proof, &exec.ctx.terms)
        .expect("TrustVC termination proof must pass strict checking");
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn test_get_proof_rewrites_mod_div_auxiliary_symbols() {
    let benchmark_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt/regression/parity_xor_unsat.smt2");
    let benchmark = std::fs::read_to_string(&benchmark_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", benchmark_path.display()));

    let input = format!("(set-option :produce-proofs true)\n{benchmark}\n(get-proof)\n");
    let commands = parse(&input).expect("parse benchmark");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute benchmark");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs
        .get(1)
        .expect("expected get-proof output after unsat");

    assert!(
        !proof.contains("_mod_q_"),
        "proof leaked internal _mod_q witness:\n{proof}"
    );
    assert!(
        !proof.contains("_mod_r_"),
        "proof leaked internal _mod_r witness:\n{proof}"
    );
    assert!(
        !proof.contains("(declare-fun "),
        "Alethe proof must not contain top-level declarations:\n{proof}"
    );
    assert!(
        proof.contains("(mod "),
        "expected surface mod term in rewritten proof:\n{proof}"
    );
}

#[test]
fn test_trust_lemma_negation_preserves_checker_pivots() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let and_ab = terms.mk_and(vec![a, b]);
    let or_dual = terms.mk_or(vec![not_a, not_b]);
    let not_or_dual = terms.mk_not_raw(or_dual);

    let mut proof = Proof::new();
    proof.add_assume(and_ab, Some("h0".to_string()));
    proof.add_assume(not_a, Some("h1".to_string()));
    proof.add_assume(not_or_dual, Some("h2".to_string()));

    crate::executor::proof_resolution::empty_clause::derive_empty_via_trust_lemma(
        &mut terms, &mut proof,
    );

    let (summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "trust lemma fallback should remain checker-valid, got {error:?}"
    );
    assert_eq!(
        summary.total_steps,
        proof.len() as u32,
        "partial checker should account for the whole trust derivation"
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));
}
