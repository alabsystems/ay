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
/// THE PROOF IS NOT EXTERNALLY CHECKABLE, and this test still pins that. The
/// re-solve certifies the CONCLUSION, not the document: the occurs-check step
/// still prints as `(step t2 (cl (not (= n 0)) (not (= x (cons 0 x)))) :rule
/// hole)`, so `check_proof_strict` must keep REJECTING it and `--self-check`
/// answers `unknown` here while default mode answers `unsat`. The
/// strict-rejection assertion below is what fires if AY ever gains a real
/// occurs-check proof rule, demanding this test be promoted.
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

    // SOUNDNESS GUARD: the occurs check has no strict Alethe rule, so the
    // document must stay honestly unproved — never dressed up as checkable.
    let strict = ay_proof::check_proof_strict(proof, exec.terms());
    assert!(
        strict.is_err(),
        "datatype occurs-check has no strict certificate; the checker must not \
         accept a fabricated one: {strict:?}"
    );
    let alethe = outputs.get(1).expect("get-proof output");
    assert!(
        alethe.contains(":rule hole") || alethe.contains(":rule trust"),
        "the uncheckable gap must be disclosed as an unproved step:\n{alethe}"
    );
}
