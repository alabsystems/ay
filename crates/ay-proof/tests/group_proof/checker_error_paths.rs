// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for ProofCheckError variants that were previously uncovered.
// Covers: EmptyProof, NoClauseProducingSteps, FinalClauseNotEmpty,
// MissingPremise, PremiseHasNoClause, UnsupportedResolutionArity,
// InvalidDrup, and the NonPriorPremise dead-code finding.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermStore};
use ay_proof::{check_proof, ProofCheckError};

#[test]
fn test_rejects_empty_proof() {
    let terms = TermStore::new();
    let proof = Proof::new();

    let err = check_proof(&proof, &terms).expect_err("empty proof must be rejected");
    assert_eq!(err, ProofCheckError::EmptyProof);
}

#[test]
fn test_rejects_no_clause_producing_steps() {
    let terms = TermStore::new();
    let mut proof = Proof::new();
    // An anchor produces None in derived_clauses, so the proof has steps
    // but no clause-producing steps.
    proof.add_step(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![],
    });

    let err = check_proof(&proof, &terms).expect_err("proof with only anchors must be rejected");
    assert_eq!(err, ProofCheckError::NoClauseProducingSteps);
}

#[test]
fn test_rejects_final_clause_not_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);

    let err = check_proof(&proof, &terms)
        .expect_err("proof ending with non-empty clause must be rejected");
    assert_eq!(
        err,
        ProofCheckError::FinalClauseNotEmpty { step: ProofId(0) }
    );
}

#[test]
fn test_rejects_missing_premise() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    // Reference premise ProofId(99) which doesn't exist.
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![ProofId(0), ProofId(99)],
        vec![],
    );

    let err = check_proof(&proof, &terms).expect_err("referencing nonexistent premise must fail");
    assert_eq!(
        err,
        ProofCheckError::MissingPremise {
            step: ProofId(1),
            premise: ProofId(99),
        }
    );
}

#[test]
fn test_self_referencing_premise_caught_as_missing() {
    // NonPriorPremise is unreachable under sequential processing:
    // at step idx, derived_clauses.len() == idx, so
    // premise_idx >= derived_clauses.len() (MissingPremise) fires
    // before premise_idx >= step_idx (NonPriorPremise) can be checked.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![ProofId(0), ProofId(1)],
        vec![],
    );

    let err = check_proof(&proof, &terms).expect_err("self-referencing premise must fail");
    assert_eq!(
        err,
        ProofCheckError::MissingPremise {
            step: ProofId(1),
            premise: ProofId(1),
        },
        "self-reference caught by MissingPremise (NonPriorPremise is unreachable dead code)"
    );
}

#[test]
fn test_rejects_premise_pointing_to_anchor() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![],
    });
    proof.add_assume(x, None);
    proof.add_assume(not_x, None);
    // Step 3 references anchor step 0 as premise (no clause).
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![ProofId(0), ProofId(1)],
        vec![],
    );

    let err = check_proof(&proof, &terms).expect_err("premise pointing to anchor must fail");
    assert_eq!(
        err,
        ProofCheckError::PremiseHasNoClause {
            step: ProofId(3),
            premise: ProofId(0),
        }
    );
}

#[test]
fn test_rejects_unsupported_resolution_arity() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    let y = terms.mk_var("y", Sort::Bool);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    let p2 = proof.add_assume(y, None);
    // Resolution with 3 premises — only binary supported.
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![p0, p1, p2], vec![]);

    let err = check_proof(&proof, &terms).expect_err("ternary resolution must be rejected");
    assert_eq!(
        err,
        ProofCheckError::UnsupportedResolutionArity {
            step: ProofId(3),
            rule: "resolution".to_string(),
            premise_count: 3,
        }
    );
}

#[test]
fn test_rejects_invalid_drup() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    // Clause (y) is NOT RUP-derivable from just {(x)}.
    proof.add_rule_step(AletheRule::Drup, vec![y], vec![], vec![]);

    let err = check_proof(&proof, &terms).expect_err("non-derivable DRUP clause must be rejected");
    assert_eq!(err, ProofCheckError::InvalidDrup { step: ProofId(1) });
}
