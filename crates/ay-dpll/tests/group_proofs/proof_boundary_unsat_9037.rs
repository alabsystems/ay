// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for #9037: proof-enabled early UNSAT exits must still
//! leave `Executor::last_proof()` populated before crossing check-sat boundary.

use ay_dpll::Executor;
use ay_frontend::parse;

fn execute_script(smt: &str) -> (Executor, Vec<String>) {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\n{smt}"));
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{smt}"));
    (exec, outputs)
}

fn assert_unsat_with_last_proof(smt: &str) {
    let (exec, outputs) = execute_script(smt);
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    assert!(
        exec.last_proof().is_some(),
        "proof-enabled UNSAT must populate last_proof; outputs={outputs:?}"
    );
}

#[test]
fn qf_s_ground_folded_false_unsat_keeps_proof() {
    assert_unsat_with_last_proof(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (assert (= (str.++ "a" "b") "ac"))
        (check-sat)
        (get-proof)
        "#,
    );
}

/// The datatype OCCURS CHECK: `(= x (cons 0 x))` asserts that a value of the
/// inductive type `List` is a proper subterm of itself, which no finite term
/// satisfies. GENUINELY UNSAT — by inspection, and z3 confirms `unsat`.
///
/// WHY THE EXPECTATION MOVED (was: `unknown` + revoked artifacts).
/// The old `unknown` was a CHECKER-COVERAGE downgrade, not a solver limit: AY
/// runs the occurs check and refutes the query correctly, but Alethe has no
/// strict rule for the argument, so it exports as a `Generic` theory lemma and
/// `check_proof_strict` rejects those BY RULE NAME — a correct answer thrown
/// away at the publication funnel.
///
/// AY has since gained the deferred-trust discharge path
/// (`Executor::discharge_trust_steps_for_certification`), which replaces
/// "reject by name" with "verify": a fresh forged-UNSAT guard must not
/// re-decide the problem as definitive SAT, every NON-trust step must still
/// clear the full strict boundary, and each deferred trust clause must be
/// independently discharged — here via the context-dependent fallback, which
/// re-decides the ORIGINAL authored assertions in a fresh `Executor` and
/// requires UNSAT. The VERDICT is thus certified by an independent re-solve and
/// `unsat` publishes.
///
/// PROMOTED (2026-08-19): the occurs check is now the typed, strictly
/// validated `DatatypeAcyclicDirect` rule, so the INTERNAL refutation is
/// trust-free and certification no longer needs the re-solve fallback. Two
/// boundaries deliberately unchanged and still pinned below: the
/// registry-free strict check keeps rejecting (no constructor authority —
/// fail-closed like every datatype kind), and the EXTERNAL wire still prints
/// an honest `hole` (carcara has no datatype acyclicity rule), so
/// `:check-proofs-strict` continues to withhold on the wire gap.
#[test]
fn dt_occurs_check_publishes_uncheckable_certificate() {
    let smt = r#"
        (set-option :produce-proofs true)
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
        (declare-const x List)
        (declare-const n Int)
        (assert (= n 0))
        (assert (= x (cons 0 x)))
        (check-sat)
        (get-proof)
        "#;
    let (exec, outputs) = execute_script(smt);
    // Genuinely UNSAT: no finite List value is a proper subterm of itself.
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));

    // The verdict is certified (independent re-solve), so artifacts publish.
    let proof = exec
        .last_proof()
        .expect("a certified UNSAT must publish its proof artifacts");
    assert!(
        outputs
            .get(1)
            .is_some_and(|output| !output.contains("proof is not available")),
        "get-proof must succeed after certified publication: {outputs:?}"
    );

    // PROMOTED (2026-08-19): AY gained the real occurs-check rule this
    // test's original strict-rejection guard existed to detect —
    // `TheoryLemmaKind::DatatypeAcyclicDirect`, an iterative bounded
    // constructor-containment walk with the datatype registry as constructor
    // identity authority. The internal refutation is now TRUST-FREE.
    assert!(
        !exec.unsat_proof_terminal_trust_detected(),
        "the occurs-check refutation must be internally trust-free now that \
         DatatypeAcyclicDirect is a real validated rule"
    );

    // FAIL-CLOSED GUARD: without the datatype registry the checker has no
    // constructor authority, so the REGISTRY-FREE strict check must keep
    // rejecting rather than accept a datatype claim it cannot authenticate.
    let strict = ay_proof::check_proof_strict(proof, exec.terms());
    assert!(
        strict.is_err(),
        "registry-free strict check must stay fail-closed on datatype \
         acyclicity: {strict:?}"
    );

    // The EXTERNAL wire has no carcara acyclicity rule: the document stays
    // honestly holey, never dressed up as externally checkable.
    let alethe = outputs.get(1).expect("get-proof output");
    assert!(
        alethe.contains(":rule hole") || alethe.contains(":rule trust"),
        "the external wire gap must be disclosed as an unproved step:\n{alethe}"
    );
}
