// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_rejects_generic_theory_lemma_accepted_by_partial_checker() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma("test", vec![p]);
    let assumption = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, lemma, assumption);

    let (_, partial_error) = check_proof_partial(&proof, &exec.ctx.terms);
    assert!(
        partial_error.is_none(),
        "regression fixture must reach the former partial-check acceptance gap"
    );
    exec.run_internal_proof_check(&proof);
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_self_certified(),
        "self-check must reject a Generic theory lemma that has no semantic validator"
    );
}

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_rejects_forged_named_theory_lemma_accepted_by_partial_checker() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("EUF", vec![p], TheoryLemmaKind::EufTransitive);
    let assumption = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, lemma, assumption);

    let (_, partial_error) = check_proof_partial(&proof, &exec.ctx.terms);
    assert!(
        partial_error.is_none(),
        "regression fixture must reach the former partial-check acceptance gap"
    );
    exec.run_internal_proof_check(&proof);
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_self_certified(),
        "self-check must semantically reject a forged named theory lemma"
    );
}

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_rejects_strict_refutation_from_non_problem_assumptions() {
    let mut exec = Executor::new();
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let not_p = exec.ctx.terms.mk_not(p);

    let mut proof = Proof::new();
    let p_assumption = proof.add_assume(p, None);
    let not_p_assumption = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, p_assumption, not_p_assumption);

    assert!(
        exec.check_proof_strict_derivation_with_datatypes(&proof)
            .is_ok(),
        "regression fixture must be a valid derivation independent of its authority"
    );
    assert!(matches!(
        exec.check_proof_strict_with_datatypes(&proof),
        Err(ay_proof::ProofCheckError::UnauthorizedAssumption { .. })
    ));
    exec.run_internal_proof_check(&proof);
    exec.last_proof = Some(proof);

    assert!(
        !exec.unsat_proof_self_certified(),
        "self-check must reject assumptions that are not authored by the active problem"
    );
}

#[cfg(feature = "proof-checker")]
#[test]
fn self_check_accepts_strict_boolean_refutation() {
    let commands = parse(
        "(set-logic QF_UF)\n\
         (declare-const p Bool)\n\
         (assert p)\n\
         (assert (not p))\n\
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

fn executor_with_single_proof_step(step: ProofStep) -> Executor {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.last_proof = Some(Proof::from_steps(vec![step]));
    assert!(
        exec.last_proof.is_some(),
        "fixture must retain its internal proof"
    );
    exec
}

#[test]
fn known_wire_gap_rejects_bare_required_string_content_theory() {
    let exec = executor_with_single_proof_step(ProofStep::TheoryLemma {
        theory: "String".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::StringContentAxiom,
        lia: None,
    });
    assert!(exec.unsat_proof_has_known_wire_gap());
}

#[test]
fn known_wire_gap_accepts_only_fixed_true_and_false_axiom_shapes() {
    for true_rule in [true, false] {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let source = exec.ctx.terms.mk_bool(true_rule);
        let literal = if true_rule {
            source
        } else {
            exec.ctx.terms.mk_not_raw(source)
        };
        exec.last_proof = Some(Proof::from_steps(vec![ProofStep::Step {
            rule: if true_rule {
                AletheRule::True
            } else {
                AletheRule::False
            },
            clause: vec![literal],
            premises: Vec::new(),
            args: vec![source],
        }]));
        assert!(
            !exec.unsat_proof_has_known_wire_gap(),
            "the exact fixed Boolean axiom is checker-supported"
        );
    }
}

#[test]
fn known_wire_gap_rejects_mutated_true_and_false_axiom_shapes() {
    let malformed_steps = [
        ProofStep::Step {
            rule: AletheRule::True,
            clause: Vec::new(),
            premises: Vec::new(),
            args: Vec::new(),
        },
        ProofStep::Step {
            rule: AletheRule::False,
            clause: Vec::new(),
            premises: vec![ProofId(0)],
            args: Vec::new(),
        },
    ];
    for step in malformed_steps {
        let exec = executor_with_single_proof_step(step);
        assert!(exec.unsat_proof_has_known_wire_gap());
    }

    let mut overridden = Executor::new();
    overridden.set_produce_proofs(true);
    let false_term = overridden.ctx.terms.mk_bool(false);
    let not_false = overridden.ctx.terms.mk_not_raw(false_term);
    overridden.last_proof = Some(Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::False,
        clause: vec![not_false],
        premises: Vec::new(),
        args: vec![false_term],
    }]));
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(false_term, "true".to_string());
    overridden.last_proof_term_overrides = Some(overrides);
    assert!(
        overridden.unsat_proof_has_known_wire_gap(),
        "a surface mutation of a fixed axiom must fail closed"
    );
}

#[test]
fn known_wire_gap_rejects_structural_and_source_surface_let_assumes() {
    let mut structural = Executor::new();
    structural.set_produce_proofs(true);
    let value = structural.ctx.terms.true_term();
    let term = structural
        .ctx
        .terms
        .mk_let(vec![("x".to_string(), value)], value);
    structural.last_proof = Some(Proof::from_steps(vec![ProofStep::Assume(term)]));
    assert!(structural.last_proof.is_some());
    assert!(structural.unsat_proof_has_known_wire_gap());

    for source in ["(let ((x true)) x)", "(let((x true))x)"] {
        let mut surface = Executor::new();
        surface.set_produce_proofs(true);
        let term = surface.ctx.terms.true_term();
        surface.last_proof = Some(Proof::from_steps(vec![ProofStep::Assume(term)]));
        let mut overrides = ay_core::kani_compat::DetHashMap::default();
        overrides.insert(term, source.to_string());
        surface.last_proof_term_overrides = Some(overrides);
        assert!(surface.last_proof.is_some());
        assert!(surface.unsat_proof_has_known_wire_gap(), "{source}");
    }
}

#[test]
fn known_wire_gap_allows_plain_euf_reflexive_theory() {
    let exec = executor_with_single_proof_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::EufReflexive,
        lia: None,
    });
    assert!(!exec.unsat_proof_has_known_wire_gap());
}

#[test]
fn terminal_policy_reads_hidden_internal_proof_and_respects_lifecycle() {
    let mut exec = Executor::new();
    exec.last_proof = Some(Proof::from_steps(vec![ProofStep::TheoryLemma {
        theory: "String".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::StringContentAxiom,
        lia: None,
    }]));
    assert!(!exec.is_producing_proofs());
    assert!(
        exec.last_proof().is_none(),
        "public artifact accessor must keep the internal proof hidden"
    );
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "strict publication policy must inspect the hidden internal proof"
    );

    exec.last_unsat_proof_reconstruction_suppressed = true;
    assert!(!exec.unsat_proof_has_known_wire_gap());

    exec.last_unsat_proof_reconstruction_suppressed = false;
    assert!(exec.unsat_proof_has_known_wire_gap());
    exec.invalidate_last_check_result();
    assert!(exec.last_proof.is_none());
    assert!(!exec.unsat_proof_has_known_wire_gap());
}

#[test]
fn terminal_trust_policy_reads_hidden_internal_proof() {
    let mut exec = Executor::new();
    exec.last_proof = Some(Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::Trust,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    }]));
    assert!(!exec.is_producing_proofs());
    assert!(exec.last_proof().is_none());
    assert!(exec.unsat_proof_terminal_trust_detected());
    exec.last_unsat_proof_reconstruction_suppressed = true;
    assert!(!exec.unsat_proof_terminal_trust_detected());
}

/// Verify that invalid proofs record a failure without panicking (#7959).
/// Previously, debug builds would panic via `debug_assert!(false, ...)`,
/// which triggered `catch_unwind` in downstream consumers (verification-consumer).
/// Now all builds log the error and record the failure in statistics.
#[cfg(feature = "proof-checker")]
#[test]
fn test_internal_proof_checker_records_failure_without_panic() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Bool);
    let y = exec.ctx.terms.mk_var("y", Sort::Bool);
    let not_x = exec.ctx.terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let h1 = proof.add_assume(not_x, None);
    proof.add_step(ProofStep::Resolution {
        clause: vec![y],
        pivot: x,
        clause1: h0,
        clause2: h1,
    });

    exec.run_internal_proof_check(&proof);
    let stats = exec.statistics();
    assert_eq!(stats.get_int(PROOF_CHECKER_FAILURES_KEY), Some(1));
    assert_eq!(stats.get_int(PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY), Some(0));
    assert_eq!(stats.get_int(PROOF_CHECKER_CHECKED_STEPS_KEY), Some(3));
    assert_eq!(stats.get_int(PROOF_CHECKER_TOTAL_STEPS_KEY), Some(3));
}

/// Verify that `:check-proofs-strict` option is read correctly (#4420).
#[test]
fn test_strict_proofs_option_defaults_to_false() {
    let exec = Executor::new();
    assert!(
        !exec.strict_proofs_enabled(),
        "strict proofs should default to disabled"
    );
}

/// Verify that strict proof mode runs end-to-end on a proof shape the
/// current strict checker can validate completely (#4420).
#[test]
fn test_strict_proof_mode_end_to_end() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
        (get-info :all-statistics)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "unsat");

    // Proof quality should be populated after strict checker runs.
    let stats = &outputs[1];
    assert!(
        stats.contains(":proof-steps"),
        "Expected :proof-steps in statistics: {stats}"
    );
    assert!(
        exec.statistics().proof_complete,
        "the typed proof-completeness source of truth must be set after strict validation"
    );
    assert_eq!(
        exec.statistics().get_int("proof_complete"),
        Some(1),
        "structured consumers must observe the same complete verdict"
    );
}

#[test]
fn proof_quality_updates_typed_completeness_for_complete_and_incomplete_evidence() {
    let mut exec = Executor::new();

    let mut complete = ay_proof::ProofQuality::default();
    complete.total_steps = 1;
    exec.populate_proof_quality_stats(&complete);
    assert!(exec.statistics().proof_complete);
    assert_eq!(exec.statistics().get_int("proof_complete"), Some(1));
    assert_eq!(exec.statistics().get_int("proof_trust"), Some(0));

    let mut incomplete = ay_proof::ProofQuality::default();
    incomplete.total_steps = 1;
    incomplete.trust_count = 1;
    exec.populate_proof_quality_stats(&incomplete);
    assert!(
        !exec.statistics().proof_complete,
        "a later incomplete proof quality must clear the typed field"
    );
    assert_eq!(exec.statistics().get_int("proof_complete"), Some(0));
    assert_eq!(exec.statistics().get_int("proof_trust"), Some(1));
}
