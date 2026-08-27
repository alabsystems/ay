// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Strict-wire policy coverage for conditional array store-permutation proofs.
// Textually included by `test_proof_artifact.rs` to preserve the existing test FQN.

const STORE_PERMUTATION_BINDER_COLLISION_UNSAT: &str = r#"
    (declare-fun a () (Array Int Int))
    (declare-fun i () Int)
    (declare-fun j () Int)
    (declare-fun x () Int)
    (declare-fun w () Int)
    (assert (not (= i j)))
    (assert (not (= (store (store a i x) j w)
                    (store (store a j w) i x))))
"#;

const STORE_PERMUTATION_HOLE_FREE_UNSAT: &str = r#"
    (declare-fun a () (Array Int Int))
    (declare-fun i () Int)
    (declare-fun j () Int)
    (declare-fun v () Int)
    (declare-fun w () Int)
    (assert (not (= i j)))
    (assert (not (= (store (store a i v) j w)
                    (store (store a j w) i v))))
"#;

#[cfg(test)]
fn store_permutation_solver(script: &str) -> Solver {
    let mut solver = Solver::try_new(Logic::QfAuflia).expect("QF_AUFLIA solver");
    solver
        .parse_smtlib2(script)
        .expect("store-permutation fixture must parse");
    solver
}

#[cfg(test)]
fn assert_strict_wire_declines_store_permutation(script: &str) {
    let mut strict = store_permutation_solver(script);
    strict
        .try_set_option(":check-proofs-strict", "true")
        .expect("enable strict wire proof mode");
    assert!(
        !strict.is_producing_proofs(),
        "strict-only mode must exercise the hidden mandatory proof"
    );
    assert!(strict.check_sat().is_unknown());
    assert_eq!(strict.unknown_reason(), Some(UnknownReason::ProofTrusted));
}

/// Pin the conservative strict-wire policy for a natively strict,
/// non-Generic proof kind whose lowering is conditional. The user symbol `x`
/// makes one instance honestly holey, while the sibling lowers successfully;
/// strict mode declines both without attempting an unbounded render.
#[test]
fn strict_wire_policy_rejects_conditional_store_permutation_kind() {
    let mut diagnostic = store_permutation_solver(STORE_PERMUTATION_BINDER_COLLISION_UNSAT);
    diagnostic.set_produce_proofs(true);
    assert!(
        diagnostic.check_sat().is_unsat(),
        "diagnostic artifact mode preserves native semantic publication"
    );
    let proof = diagnostic.last_proof().expect("retained native proof");
    let terminal = ay_proof::terminal_trust_report(proof);
    assert!(
        !terminal.has_terminal_trust(),
        "anti-vacuity: native terminal-trust must be false so the known-wire-gap policy runs: {terminal:?}"
    );
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayStorePermutation,
            ..
        }
    )));
    let native_quality = diagnostic
        .last_strict_proof_quality()
        .expect("strict result")
        .expect("native store-permutation validator must accept");
    assert!(
        native_quality.is_complete(),
        "anti-vacuity: quality alone cannot see this print-time hole: {native_quality:?}"
    );
    let artifact = diagnostic
        .export_last_unsat_artifact()
        .expect("requested diagnostic artifact");
    assert!(
        artifact.alethe.contains(":rule hole"),
        "{}",
        artifact.alethe
    );
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));

    let mut self_checked = store_permutation_solver(STORE_PERMUTATION_BINDER_COLLISION_UNSAT);
    self_checked.set_produce_proofs(true);
    self_checked.executor.set_self_check(true);
    assert!(
        self_checked.check_sat().is_unsat(),
        "self-check is native semantic validation, not a wire-completeness promise"
    );
    assert!(
        self_checked.last_proof().is_some(),
        "self-check control must retain the proof it validated"
    );

    let mut proof_checked = store_permutation_solver(STORE_PERMUTATION_BINDER_COLLISION_UNSAT);
    proof_checked.set_verification_level(VerificationLevel::ProofChecked);
    assert!(
        proof_checked.check_sat().is_unsat(),
        "ProofChecked is native semantic validation"
    );

    assert_strict_wire_declines_store_permutation(STORE_PERMUTATION_BINDER_COLLISION_UNSAT);

    let mut control_diagnostic = store_permutation_solver(STORE_PERMUTATION_HOLE_FREE_UNSAT);
    control_diagnostic.set_produce_proofs(true);
    assert!(control_diagnostic.check_sat().is_unsat());
    let control_artifact = control_diagnostic
        .export_last_unsat_artifact()
        .expect("hole-free control artifact");
    assert!(
        !control_artifact.alethe.contains(":rule hole")
            && !control_artifact.alethe.contains(":rule trust"),
        "hole-free control drifted:\n{}",
        control_artifact.alethe
    );

    assert_strict_wire_declines_store_permutation(STORE_PERMUTATION_HOLE_FREE_UNSAT);
}
