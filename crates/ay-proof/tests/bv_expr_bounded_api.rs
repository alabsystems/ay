// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External-crate coverage for the bounded BV expression proof API.

use std::time::Duration;

use ay_proof::{
    export_bv_blast_proof_expr_bounded, BvBlastProof, BvBlastValidateLimits, BvExpr,
    BvExprProofBudget, BvExprProofBudgetError,
};

fn finite_replay_limits(proof: &BvBlastProof) -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: Some(ay_core::time::Instant::now() + Duration::from_secs(5)),
        max_vars: proof.vars.len(),
        max_bit_lemmas: proof.bit_lemmas.len(),
        max_clauses: proof.clauses.len(),
        max_clause_literals: proof
            .clauses
            .iter()
            .map(|clause| clause.lits.len())
            .max()
            .unwrap_or(0),
        max_original_literals: proof.clauses.iter().map(|clause| clause.lits.len()).sum(),
        max_resolution_steps: proof.refutation.steps.len(),
        max_derived_literals: proof
            .refutation
            .steps
            .iter()
            .map(|step| step.clause.len())
            .sum(),
        max_work: 50_000_000,
    }
}

#[test]
fn public_reexports_construct_and_run_without_internal_limit_types() {
    let budget = BvExprProofBudget::conservative(Duration::from_secs(2), 4096)
        .expect("finite public budget");
    assert_eq!(budget.timeout(), Duration::from_secs(2));
    assert_eq!(budget.max_resolution_steps(), 4096);

    let expression = BvExpr::leaf("external_consumer", 1);
    let proof = export_bv_blast_proof_expr_bounded(&expression, &expression, &budget)
        .expect("ordinary bounded proof");
    proof
        .validate_with_limits(&finite_replay_limits(&proof))
        .expect("bounded proof replays within finite consumer limits");
}

#[test]
fn public_constructor_rejects_an_absent_wall_budget() {
    assert_eq!(
        BvExprProofBudget::conservative(Duration::ZERO, 4096),
        Err(BvExprProofBudgetError::ZeroTimeout)
    );
}
