// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Documents two proof checker verification gaps related to strict mode
// and generic rule validation. See sat-debuggability epic #4172.

use super::common;

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermStore, TheoryLemmaKind};
use ay_proof::{check_proof, check_proof_strict, ProofCheckError};

/// Strict mode now rejects theory lemmas without a strict semantic validator.
///
/// `check_proof_strict` is the highest-rigor validation mode available.
/// The bogus generic theory lemma from `common::build_unsound_theory_lemma_proof`
/// is now rejected before it can smuggle an arbitrary clause into the proof.
#[test]
fn test_strict_mode_rejects_unsupported_theory_lemma_kind() {
    let (terms, proof) = common::build_unsound_theory_lemma_proof();

    let err = check_proof_strict(&proof, &terms)
        .expect_err("strict mode must reject unsupported theory lemmas");
    assert_eq!(
        err,
        ProofCheckError::UnsupportedTheoryLemmaKind {
            step: ProofId(2),
            kind: TheoryLemmaKind::Generic,
        }
    );
}

/// Non-strict mode still accepts generic Alethe rules without semantic
/// validation (the catch-all in `validate_generic_step` allows anything).
/// This is intentional: non-strict mode trusts the solver.
///
/// Strict mode now rejects unvalidated generic rules (#6537).
#[test]
fn test_non_strict_accepts_bogus_generic_rule() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let bogus = proof.add_step(ProofStep::Step {
        rule: AletheRule::LaGeneric,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, bogus, h0);

    // Non-strict mode accepts the bogus step (known gap in non-strict).
    check_proof(&proof, &terms).expect("non-strict checker accepts bogus la_generic step");
}

/// Strict mode now rejects unvalidated generic rules (#6537).
///
/// Previously, the catch-all `_ => {}` in `validate_generic_step` accepted
/// ~40 Alethe rule variants without any semantic validation, even in strict
/// mode. Now strict mode rejects any rule that lacks a semantic validator.
#[test]
fn test_strict_mode_rejects_unvalidated_generic_rule() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let bogus = proof.add_step(ProofStep::Step {
        rule: AletheRule::LaGeneric,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, bogus, h0);

    let err = check_proof_strict(&proof, &terms)
        .expect_err("strict mode must reject unvalidated la_generic step");
    assert_eq!(
        err,
        ProofCheckError::UnvalidatedRule {
            step: ProofId(1),
            rule: "la_generic".to_string(),
        }
    );
}
