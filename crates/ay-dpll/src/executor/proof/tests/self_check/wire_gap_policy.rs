// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `executor::proof::tests` to preserve test FQNs.
//
// The publication-policy half of the self-check suite: the shared executor
// fixtures (single-step proof, symbolic LIA Farkas refutation, Alethe export)
// and every test of `unsat_proof_has_known_wire_gap` /
// `unsat_proof_terminal_trust_detected` — the gate that decides whether an
// internal proof carries EXTERNAL authority. Its sibling in `self_check.rs`
// covers the self-check verdict itself and the internal checker's statistics.

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

fn executor_with_symbolic_lia_farkas(coefficients: &[i64]) -> (Executor, TermId) {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("lia_wire_x", Sort::Int);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let lower = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
    let upper = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
    let not_lower = exec.ctx.terms.mk_not_raw(lower);
    let not_upper = exec.ctx.terms.mk_not_raw(upper);
    let mut proof = Proof::new();
    let lower_assumption = proof.add_assume(lower, None);
    let upper_assumption = proof.add_assume(upper, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![not_lower, not_upper],
        farkas: Some(FarkasAnnotation::from_ints(coefficients)),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    let reduced = proof.add_resolution(vec![not_upper], lower, lower_assumption, lemma);
    proof.add_resolution(Vec::new(), upper, upper_assumption, reduced);
    exec.last_proof = Some(proof);
    (exec, x)
}

fn export_executor_proof(exec: &Executor) -> String {
    let proof = exec.last_proof.as_ref().expect("fixture retains its proof");
    let overrides = exec.proof_export_term_overrides();
    let scope: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &exec.ctx.terms,
        &scope,
        overrides.as_ref(),
    )
    .expect("the diagnostic proof must remain printable")
}

#[test]
fn lia_farkas_promotion_is_shared_by_gate_and_printer() {
    let (exec, _) = executor_with_symbolic_lia_farkas(&[1, 1]);
    let quality = ay_proof::check_proof_strict(
        exec.last_proof.as_ref().expect("fixture retains its proof"),
        &exec.ctx.terms,
    )
    .expect("AY's strict checker must independently accept the actual certificate");
    assert!(quality.is_complete());
    assert!(
        !exec.unsat_proof_has_known_wire_gap(),
        "the exact checked Farkas promotion carries external authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule la_generic :args (1 1)"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");
}

#[test]
fn lia_farkas_mismatch_is_a_disclosed_hole_in_both_consumers() {
    let (exec, _) = executor_with_symbolic_lia_farkas(&[1, 0]);
    assert!(
        ay_proof::check_proof_strict(
            exec.last_proof.as_ref().expect("fixture retains its proof"),
            &exec.ctx.terms,
        )
        .is_err(),
        "AY's strict checker must reject the mismatched coefficients"
    );
    assert!(
        exec.unsat_proof_has_known_wire_gap(),
        "a coefficient mismatch must withhold external authority"
    );
    let wire = export_executor_proof(&exec);
    assert!(wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");
    assert!(!wire.contains(":rule la_generic"), "{wire}");
    assert!(
        !wire.contains(":args"),
        "a hole carries no Farkas args: {wire}"
    );
}

#[test]
fn lia_surface_override_barrier_is_shared_by_gate_and_printer() {
    let (mut exec, x) = executor_with_symbolic_lia_farkas(&[1, 1]);
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(x, "(+ lia_wire_x 1)".to_string());
    exec.last_proof_term_overrides = Some(overrides);

    assert!(exec.unsat_proof_has_known_wire_gap());
    let wire = export_executor_proof(&exec);
    assert!(wire.contains("(+ lia_wire_x 1)"), "{wire}");
    assert!(wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");
    assert!(!wire.contains(":rule la_generic"), "{wire}");

    // The barrier is per-CLAUSE, not per-document: what makes the promotion
    // honest is that the text the checker reads is the text the Farkas
    // validator accepted. An installed-but-EMPTY channel cannot change any
    // clause, so it is not a barrier. This still pins the exact state input —
    // gate and printer must answer identically for `Some(empty)`, neither may
    // follow a stricter branch than the other — but it now demands the checked
    // promotion instead of accepting a discarded certificate.
    let (mut empty, _) = executor_with_symbolic_lia_farkas(&[1, 1]);
    empty.last_proof_term_overrides = Some(ay_core::kani_compat::DetHashMap::default());
    assert!(!empty.unsat_proof_has_known_wire_gap());
    let wire = export_executor_proof(&empty);
    assert!(wire.contains(":rule la_generic :args (1 1)"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule lia_generic"), "{wire}");

    // The defect the narrowing removes: a channel installed for some OTHER
    // term must not discard THIS clause's certificate. The lemma's clause
    // renders byte-identically with and without the channel, so the promotion
    // stands — while the first half above shows an override that DOES reach
    // the clause still withholds it.
    let (mut unrelated, _) = executor_with_symbolic_lia_farkas(&[1, 1]);
    let other = unrelated.ctx.terms.mk_var("lia_wire_other", Sort::Int);
    let mut elsewhere = ay_core::kani_compat::DetHashMap::default();
    elsewhere.insert(other, "(+ lia_wire_other 1)".to_string());
    unrelated.last_proof_term_overrides = Some(elsewhere);
    assert!(!unrelated.unsat_proof_has_known_wire_gap());
    let wire = export_executor_proof(&unrelated);
    assert!(wire.contains(":rule la_generic :args (1 1)"), "{wire}");
    assert!(!wire.contains(":rule hole"), "{wire}");
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
