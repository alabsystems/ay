// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Direct unit test for prune_to_empty_clause_derivation.
///
/// Constructs a proof with both reachable and unreachable steps, prunes it,
/// and verifies that only the reachable steps survive with correct remapped
/// premise indices.
#[test]
fn test_prune_to_empty_clause_derivation_removes_unreachable_steps() {
    use ay_core::{AletheRule, TermId};

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);
    let t3 = TermId::new(3);

    let mut proof = Proof::new();

    // Step 0: Assume(t1) — reachable (used by final resolution)
    let h0 = proof.add_assume(t1, None);
    // Step 1: Assume(t2) — reachable (used by final resolution)
    let h1 = proof.add_assume(t2, None);
    // Step 2: TheoryLemma [t3] — UNREACHABLE (not referenced by anything)
    let _unreachable = proof.add_theory_lemma("EUF", vec![t3]);
    // Step 3: Step(Trust) clause=[not(t1), not(t2)] — reachable (premise of step 4)
    let trust_step = proof.add_rule_step(
        AletheRule::Trust,
        vec![t1, t2], // clause content doesn't matter for pruning
        vec![],
        vec![],
    );
    // Step 4: Step(ThResolution) clause=[] — reachable (empty clause target)
    let _final_step = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![], // empty clause
        vec![h0, h1, trust_step],
        vec![],
    );

    assert_eq!(proof.len(), 5);

    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);

    // Step 2 (unreachable TheoryLemma) should be removed
    assert_eq!(
        proof.len(),
        4,
        "expected 4 steps after pruning, got {}",
        proof.len()
    );

    // Step 0, 1 should still be Assume
    assert!(matches!(proof.steps[0], ProofStep::Assume(t) if t == t1));
    assert!(matches!(proof.steps[1], ProofStep::Assume(t) if t == t2));

    // Step 2 (was step 3) should be Trust rule
    assert!(matches!(
        &proof.steps[2],
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        }
    ));

    // Step 3 (was step 4) should be ThResolution with remapped premises
    match &proof.steps[3] {
        ProofStep::Step {
            rule,
            clause,
            premises,
            ..
        } => {
            assert_eq!(*rule, AletheRule::ThResolution);
            assert!(clause.is_empty(), "final step should derive empty clause");
            // Old premises [0, 1, 3] should be remapped to [0, 1, 2]
            assert_eq!(premises, &[ProofId(0), ProofId(1), ProofId(2)]);
        }
        other => panic!("expected Step, got {other:?}"),
    }
}

#[test]
fn test_prune_to_selected_earlier_empty_clause() {
    use ay_core::{AletheRule, TermId};

    let early_term = TermId::new(1);
    let late_term = TermId::new(2);
    let mut proof = Proof::new();
    let early_assume = proof.add_assume(early_term, Some("early".to_string()));
    let early_empty = proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![early_assume],
        Vec::new(),
    );
    let late_assume = proof.add_assume(late_term, Some("late".to_string()));
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![late_assume],
        Vec::new(),
    );

    assert!(
        crate::executor::proof_resolution::prune_to_empty_clause_derivation_at(
            &mut proof,
            early_empty.0 as usize,
        )
    );
    assert_eq!(proof.steps.len(), 2);
    assert!(matches!(proof.steps[0], ProofStep::Assume(term) if term == early_term));
    assert!(matches!(
        &proof.steps[1],
        ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause,
            premises,
            ..
        } if clause.is_empty() && premises == &[ProofId(0)]
    ));
    assert_eq!(proof.named_steps.get("early"), Some(&ProofId(0)));
    assert!(!proof.named_steps.contains_key("late"));
}

#[test]
fn test_prune_remaps_only_reachable_named_assumptions() {
    use ay_core::{AletheRule, TermId};

    let unreachable_term = TermId::new(1);
    let reachable_term = TermId::new(2);
    let mut proof = Proof::new();
    let _unreachable = proof.add_assume(unreachable_term, Some("unreachable".to_string()));
    let reachable = proof.add_assume(reachable_term, Some("reachable".to_string()));
    let helper = proof.add_rule_step(AletheRule::Trust, vec![], vec![], vec![]);
    proof
        .named_steps
        .insert("not_an_assume".to_string(), helper);
    proof
        .named_steps
        .insert("dangling".to_string(), ProofId(u32::MAX));
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![reachable, helper],
        vec![],
    );

    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);

    assert!(!proof.named_steps.contains_key("unreachable"));
    assert!(!proof.named_steps.contains_key("not_an_assume"));
    assert!(!proof.named_steps.contains_key("dangling"));
    let remapped = proof.named_steps["reachable"];
    assert_eq!(remapped, ProofId(0));
    assert!(
        matches!(proof.steps.get(remapped.0 as usize), Some(ProofStep::Assume(term)) if *term == reachable_term)
    );
}

/// Pruning a proof with no empty clause should be a no-op.
#[test]
fn test_prune_no_empty_clause_is_noop() {
    use ay_core::TermId;

    let t1 = TermId::new(1);
    let mut proof = Proof::new();
    proof.add_assume(t1, None);
    proof.add_theory_lemma("LRA", vec![t1]);

    let original_len = proof.len();
    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);
    assert_eq!(
        proof.len(),
        original_len,
        "prune should be no-op without empty clause"
    );
}

/// Pruning a proof where all steps are reachable should not change it.
#[test]
fn test_prune_all_reachable_is_noop() {
    use ay_core::{AletheRule, TermId};

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(t1, None);
    let h1 = proof.add_assume(t2, None);
    let _final = proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, h1], vec![]);

    assert_eq!(proof.len(), 3);
    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);
    assert_eq!(proof.len(), 3, "all-reachable proof should not change");
}

#[test]
fn test_prune_all_reachable_sanitizes_named_metadata() {
    use ay_core::{AletheRule, TermId};

    let p = TermId::new(1);
    let not_p = TermId::new(2);
    let mut proof = Proof::new();
    let p_step = proof.add_assume(p, Some("p".to_string()));
    let not_p_step = proof.add_assume(not_p, Some("not_p".to_string()));
    let final_step = proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![p_step, not_p_step],
        vec![],
    );
    proof
        .named_steps
        .insert("not_an_assume".to_string(), final_step);
    proof
        .named_steps
        .insert("dangling".to_string(), ProofId(u32::MAX));

    crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);

    assert_eq!(proof.named_steps["p"], p_step);
    assert_eq!(proof.named_steps["not_p"], not_p_step);
    assert!(!proof.named_steps.contains_key("not_an_assume"));
    assert!(!proof.named_steps.contains_key("dangling"));
}

#[test]
fn test_theory_packet_resolution_derives_empty_clause() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let p = terms.mk_var("p", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let not_c = terms.mk_not(c);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(a, Some("h0".to_string()));
    proof.add_assume(b, Some("h1".to_string()));
    proof.add_assume(c, Some("h2".to_string()));
    proof.add_theory_lemma("EUF", vec![not_a, not_b, p]);
    proof.add_theory_lemma("LRA", vec![not_c, not_p]);

    assert!(
        crate::executor::proof_resolution::empty_clause::try_derive_empty_via_theory_packet_resolution(&terms, &mut proof),
        "expected two-lemma packet resolution to derive the empty clause"
    );
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Step { clause, .. }) if clause.is_empty()
    ));

    let (summary, error) = check_proof_partial(&proof, &terms);
    assert!(
        error.is_none(),
        "packet-derived proof should remain checker-valid, got {error:?} ({summary})"
    );
}

#[test]
fn test_proof_quality_metrics_in_statistics() {
    // Verify that proof quality metrics appear in :all-statistics after UNSAT (#4420)
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");

    let stats = &outputs[1];
    assert!(
        stats.contains(":proof-steps"),
        "Expected :proof-steps in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-verified"),
        "Expected :proof-verified in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-trust"),
        "Expected :proof-trust in statistics: {stats}"
    );
    assert!(
        stats.contains(":proof-complete"),
        "Expected :proof-complete in statistics: {stats}"
    );
}

#[test]
fn test_proof_quality_cleared_on_sat() {
    // Quality metrics should not carry over from a previous UNSAT (#4420)
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    // Now do a SAT check — quality should be cleared
    let input2 = r#"
        (reset)
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const y Real)
        (assert (> y 0))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands2 = parse(input2).unwrap();
    let outputs2 = exec.execute_all(&commands2).unwrap();
    assert_eq!(outputs2[0], "sat");

    let stats = &outputs2[1];
    // After SAT, proof-steps should not appear (no proof was generated)
    assert!(
        !stats.contains(":proof-steps"),
        "proof-steps should not appear after SAT: {stats}"
    );
}

#[test]
fn test_proof_quality_strict_check_via_api() {
    // Verify strict checking reports unsupported arithmetic lemmas instead of
    // panicking after #6686 downgraded bound axioms from LraFarkas to Generic.
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");

    // Access the proof and run strict check
    let proof = exec
        .last_proof
        .as_ref()
        .expect("proof should exist after UNSAT");
    let strict_result = ay_proof::check_proof_strict(proof, &exec.ctx.terms);

    // Arithmetic proofs now commonly include Generic theory lemmas, which
    // strict mode intentionally rejects until semantic validation exists.
    match strict_result {
        Ok(quality) => {
            assert!(
                quality.is_complete(),
                "strict-passing proof should be complete"
            );
        }
        Err(ay_proof::ProofCheckError::TrustStep { .. }) => {
            // Expected for trust-fallback proofs
        }
        Err(ay_proof::ProofCheckError::UnsupportedTheoryLemmaKind {
            kind: TheoryLemmaKind::Generic,
            ..
        }) => {
            // Expected for current arithmetic bound-axiom proofs (#6686).
        }
        Err(other) => {
            panic!("Unexpected strict check error: {other:?}");
        }
    }
}

#[cfg(feature = "proof-checker")]
#[test]
fn test_internal_proof_checker_records_partial_hole_metrics() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Bool);
    let not_x = exec.ctx.terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let hole = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, hole, h0);

    exec.run_internal_proof_check(&proof);
    let stats = exec.statistics();
    assert_eq!(stats.get_int("proof_checker_failures"), Some(0));
    assert_eq!(stats.get_int("proof_checker_skipped_hole_steps"), Some(1));
    assert_eq!(stats.get_int("proof_checker_checked_steps"), Some(2));
    assert_eq!(stats.get_int("proof_checker_total_steps"), Some(3));
}
