// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Proof witness export tests for #6778.
//!
//! Verifies that `ExecuteTypedDetails.unsat_proof` is populated on the
//! UNSAT path when proof production is enabled, and `None` otherwise.

use super::*;
use ay_dpll::api::{ProofAcceptanceMode, StrictProofVerdict};

#[test]
fn test_verified_result_carries_unsat_proof_6778() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-proofs", "true"));
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    // x > 0 AND x < 0 → UNSAT
    program.assert(x.clone().real_gt(Expr::real(0)));
    program.assert(x.real_lt(Expr::real(0)));
    program.check_sat();

    let details = execute_typed_with_details(&program).unwrap();
    assert!(
        matches!(details.result, ExecuteTypedResult::Verified),
        "expected Verified (UNSAT), got: {:?}",
        details.result
    );

    let proof = details
        .unsat_proof
        .expect("UNSAT with produce-proofs should carry proof artifact");
    assert!(
        !proof.alethe.is_empty(),
        "proof artifact should have non-empty Alethe text"
    );
    assert!(
        proof
            .lrat_certificate
            .as_ref()
            .is_some_and(|bytes| !bytes.is_empty()),
        "proof artifact should carry non-empty LRAT bytes"
    );
    assert!(
        matches!(&proof.strict_verdict, StrictProofVerdict::Verified(_)),
        "LRA proof witness should export a successful strict verdict: {:?}",
        proof.strict_verdict,
    );
    assert_eq!(
        proof.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "execute_direct proof witness should be acceptable in strict mode",
    );
}

#[test]
fn program_level_options_are_applied_by_direct_execution() {
    let mut program = AYProgram::new();
    // Exercise the metadata API used by ProgramBuilder, not an explicit
    // Constraint::SetOption command. A leading colon is accepted consistently
    // by direct execution and text rendering.
    program.set_option(":produce-proofs", "true");
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    program.assert(x.clone().real_gt(Expr::real(0)));
    program.assert(x.real_lt(Expr::real(0)));
    program.check_sat();

    assert!(
        program
            .to_string()
            .contains("(set-option :produce-proofs true)"),
        "a leading colon must be rendered exactly once"
    );
    let details = execute_typed_with_details(&program).unwrap();
    assert!(matches!(details.result, ExecuteTypedResult::Verified));
    assert!(
        details.unsat_proof.is_some(),
        "execute_direct must apply AYProgram::set_option metadata"
    );
}

#[test]
fn test_sat_result_has_no_proof_6778() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    // x > 0 → SAT
    program.assert(x.real_gt(Expr::real(0)));
    program.check_sat();

    let details = execute_typed_with_details(&program).unwrap();
    assert!(
        matches!(details.result, ExecuteTypedResult::Counterexample(_)),
        "expected SAT counterexample, got: {:?}",
        details.result
    );
    assert!(
        details.unsat_proof.is_none(),
        "SAT result should not carry proof artifact"
    );
}

#[test]
fn test_proof_witness_has_theory_lemma_evidence_6778() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-proofs", "true"));
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    let y = program.declare_const("y", Sort::real());
    // x > y AND y > x → UNSAT (requires LRA theory reasoning)
    program.assert(x.clone().real_gt(y.clone()));
    program.assert(y.real_gt(x));
    program.check_sat();

    let details = execute_typed_with_details(&program).unwrap();
    assert!(
        matches!(details.result, ExecuteTypedResult::Verified),
        "expected Verified (UNSAT), got: {:?}",
        details.result
    );

    let proof = details
        .unsat_proof
        .expect("UNSAT with theory contradiction should carry proof");
    assert!(
        proof.quality.theory_lemma_count > 0,
        "proof from theory contradiction should have theory_lemma_count > 0, got: {}",
        proof.quality.theory_lemma_count
    );
    assert!(
        !proof.farkas_certificates.is_empty(),
        "theory contradiction should export Farkas certificates"
    );
    assert!(
        !proof.restricted_rule_subset,
        "theory proof witness should remain outside the restricted-rule-subset subset",
    );
}
