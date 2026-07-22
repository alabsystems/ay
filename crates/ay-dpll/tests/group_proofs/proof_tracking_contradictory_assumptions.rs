// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

use ay_core::{AletheRule, ProofStep};
use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof, check_proof_strict, ProofQuality};
use ntest::timeout;

fn assert_last_unsat_proof_is_valid(exec: &Executor) {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof(proof, exec.terms())
        .expect("internal proof checker rejected proof for UNSAT result");
}

fn assert_last_unsat_proof_strict(exec: &Executor) -> ProofQuality {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof_strict(proof, exec.terms()).expect("strict proof checker rejected proof")
}

#[test]
#[timeout(5_000)]
fn test_check_sat_assuming_contradictory_assumptions_emits_resolution_contradiction() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BOOL)
        (declare-const a Bool)
        (check-sat-assuming (a (not a)))
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert_last_unsat_proof_is_valid(&exec);
    assert_last_unsat_proof_strict(&exec);

    let internal_proof = exec
        .last_proof()
        .expect("expected proof object for contradictory assumptions");
    assert!(
        internal_proof
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::TheoryLemma { .. })),
        "expected contradictory assumptions to avoid theory lemmas, got {:?}",
        internal_proof.steps
    );
    assert!(
        internal_proof.steps.iter().all(|step| {
            !matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    ..
                }
            )
        }),
        "expected direct SAT resolution path, found th_resolution in {:?}",
        internal_proof.steps
    );
    assert!(
        matches!(
            internal_proof.steps.last(),
            Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
        ),
        "expected final empty-clause resolution step, got {:?}",
        internal_proof.steps.last()
    );

    let proof = &outputs[1];
    assert!(
        proof.matches("(assume ").count() >= 2,
        "expected assumption steps for contradictory assumptions, got:\n{proof}"
    );
    assert!(
        proof.contains(":rule resolution"),
        "expected direct resolution for contradictory assumptions:\n{proof}"
    );
    assert!(
        !proof.contains(":rule th_resolution"),
        "expected contradictory assumptions to avoid th_resolution fallback:\n{proof}"
    );
    assert!(
        proof.contains("(cl)"),
        "expected empty clause contradiction in proof:\n{proof}"
    );
}

/// (#b22) Two contradictory BV equality assumptions `(= x bv1)` / `(= x bv2)`
/// fold to UNSAT before the proof-producing SAT solver records any conflict,
/// so the proof reconstructs with no Assume leaves. Previously this produced an
/// empty `proof.steps` and panicked `build_unsat_proof produced an empty proof`.
/// The fix seeds the check-sat-assuming assumptions as Assume steps so the
/// trust-lemma fallback can close the proof. This must yield UNSAT with a
/// non-empty proof that derives the empty clause and passes the proof checker.
#[test]
#[timeout(5_000)]
fn test_check_sat_assuming_bv_contradictory_equalities_no_empty_proof_panic_b22() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (check-sat-assuming ((= x (_ bv1 2)) (= x (_ bv2 2))))
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");

    // The proof must be non-empty and derive the empty clause (the bug was an
    // empty-proof postcondition panic).
    let internal_proof = exec
        .last_proof()
        .expect("expected proof object for contradictory BV assumptions");
    assert!(
        !internal_proof.steps.is_empty(),
        "expected non-empty proof for contradictory BV assumptions"
    );
    assert!(
        internal_proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { clause, .. } | ProofStep::Resolution { clause, .. }
                if clause.is_empty()
        )),
        "expected the proof to derive the empty clause, got {:?}",
        internal_proof.steps
    );
    assert_last_unsat_proof_is_valid(&exec);

    let proof = &outputs[1];
    assert!(
        proof.matches("(assume ").count() >= 2,
        "expected the two BV equality assumptions as Assume steps, got:\n{proof}"
    );
    assert!(
        proof.contains("(cl)"),
        "expected empty clause contradiction in proof:\n{proof}"
    );
}
