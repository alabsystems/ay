// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn native_strict_bv_lia_wire_gap(exec: &mut Executor, roots: &[TermId]) -> Proof {
    let mut proof = Proof::new();
    let assumes: Vec<ProofId> = roots.iter().map(|&root| proof.add_assume(root, None)).collect();
    let mut residual: Vec<TermId> =
        roots.iter().map(|&root| exec.ctx.terms.mk_not_raw(root)).collect();
    let mut current = proof.add_theory_lemma_with_kind(
        "BV_LIA",
        residual.clone(),
        TheoryLemmaKind::BvLiaTautology,
    );
    for (&root, &assume) in roots.iter().zip(&assumes) {
        let complement = exec.ctx.terms.mk_not_raw(root);
        residual.retain(|literal| *literal != complement);
        current = proof.add_resolution(residual.clone(), root, current, assume);
    }
    proof
}

#[test]
fn seq_extensional_companion_theorem_is_a_disclosed_wire_gap() {
    let exec = executor_with_single_proof_step(ProofStep::TheoryLemma {
        theory: "Sequence extensionality".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::SeqExtensionalCompanionContradiction,
        lia: None,
    });
    assert!(exec.unsat_proof_has_known_wire_gap());
}

#[test]
fn equality_chain_retries_native_strict_wire_gap_as_ground_evaluate() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("wire_retry_x", Sort::bitvec(8));
    let five = exec.ctx.terms.mk_bitvec(BigInt::from(5), 8);
    let ten = exec.ctx.terms.mk_bitvec(BigInt::from(10), 8);
    let roots = [exec.ctx.terms.mk_eq(x, five), exec.ctx.terms.mk_eq(x, ten)];
    add_authored_roots(&mut exec, &roots);

    let mut proof = native_strict_bv_lia_wire_gap(&mut exec, &roots);
    let quality = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect("the starting internal BV/LIA certificate must be native-strict");
    assert!(quality.is_complete());
    assert!(exec.proof_has_known_wire_gap(&proof));
    let before = format!("{:?}", proof.steps);
    let checks_before = exec.strict_check_invocations.get();

    exec.run_authored_replacement_cascade(&mut proof);

    assert_eq!(
        exec.strict_check_invocations.get() - checks_before,
        2,
        "wire-gap retry needs one classification and one candidate replay"
    );
    assert_ne!(format!("{:?}", proof.steps), before);
    let quality = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect("the exact-root equality-chain replacement must replay strictly");
    assert!(quality.is_complete());
    assert!(!exec.proof_has_known_wire_gap(&proof));
    let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &roots,
        None,
    )
    .expect("the replacement must export against the exact problem scope");
    assert!(wire.contains(":rule evaluate"), "{wire}");
    assert!(!wire.contains(":rule hole") && !wire.contains(":rule trust"), "{wire}");
}

#[test]
fn unmatched_symbolic_bv_wire_gap_does_not_scan_unrelated_cascade_members() {
    let mut exec = Executor::new();
    let value = exec
        .ctx
        .terms
        .mk_var("unmatched_symbolic_wire_gap", Sort::bitvec(16));
    let theorem = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let root = exec.ctx.terms.mk_not_raw(theorem);
    add_authored_roots(&mut exec, &[root]);

    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "BV",
        vec![theorem],
        TheoryLemmaKind::BvBitBlast,
    );
    proof.add_resolution(Vec::new(), theorem, assume, lemma);
    assert!(
        exec.check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete())
    );
    assert!(exec.proof_has_known_wire_gap(&proof));
    let before = format!("{:?}", proof.steps);
    let checks_before = exec.strict_check_invocations.get();

    exec.run_authored_replacement_cascade(&mut proof);

    assert_eq!(format!("{:?}", proof.steps), before);
    assert_eq!(
        exec.strict_check_invocations.get() - checks_before,
        1,
        "an unmatched native-strict wire gap needs one classification replay"
    );
    assert!(exec.proof_has_known_wire_gap(&proof));
}

#[test]
fn equality_chain_retry_declines_sat_transient_and_unsupported_endpoints() {
    let mut equal = Executor::new();
    let x = equal.ctx.terms.mk_var("equal_endpoint_x", Sort::bitvec(8));
    let five = equal.ctx.terms.mk_bitvec(BigInt::from(5), 8);
    let root = equal.ctx.terms.mk_eq(x, five);
    add_authored_roots(&mut equal, &[root, root]);
    let mut equal_proof = Proof::new();
    terminal_empty_trust(&mut equal_proof, None);
    let original = format!("{:?}", equal_proof.steps);
    equal.replace_with_exact_authored_equality_chain_refutation(
        &mut equal_proof,
        RepairEntry::Check,
    );
    assert_eq!(format!("{:?}", equal_proof.steps), original);

    let mut transient = Executor::new();
    let y = transient.ctx.terms.mk_var("transient_endpoint_y", Sort::bitvec(8));
    let five = transient.ctx.terms.mk_bitvec(BigInt::from(5), 8);
    let ten = transient.ctx.terms.mk_bitvec(BigInt::from(10), 8);
    let y_is_five = transient.ctx.terms.mk_eq(y, five);
    let y_is_ten = transient.ctx.terms.mk_eq(y, ten);
    transient.ctx.assertions.extend([y_is_five, y_is_ten]);
    let mut transient_proof = Proof::new();
    terminal_empty_trust(&mut transient_proof, None);
    let original = format!("{:?}", transient_proof.steps);
    transient.replace_with_exact_authored_equality_chain_refutation(
        &mut transient_proof,
        RepairEntry::Check,
    );
    assert_eq!(format!("{:?}", transient_proof.steps), original);

    let mut unsupported = Executor::new();
    let string = unsupported.ctx.terms.mk_var("unsupported_endpoint_string", Sort::String);
    let one = unsupported.ctx.terms.mk_string("one".to_string());
    let two = unsupported.ctx.terms.mk_string("two".to_string());
    let string_is_one = unsupported.ctx.terms.mk_eq(string, one);
    let string_is_two = unsupported.ctx.terms.mk_eq(string, two);
    add_authored_roots(&mut unsupported, &[string_is_one, string_is_two]);
    let mut unsupported_proof = Proof::new();
    terminal_empty_trust(&mut unsupported_proof, None);
    let original = format!("{:?}", unsupported_proof.steps);
    unsupported.replace_with_exact_authored_equality_chain_refutation(
        &mut unsupported_proof,
        RepairEntry::Check,
    );
    assert_eq!(format!("{:?}", unsupported_proof.steps), original);
}
