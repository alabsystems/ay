// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused tests for bounded authored-root collection in the BV/LIA rebuild.

use super::*;
use crate::executor_types::{SolveResult, UnknownReason};

#[test]
fn root_collection_is_bounded_and_deduplicated() {
    let mut terms = TermStore::new();
    let repeated = terms.mk_var("bv_lia_repeated_root", Sort::Bool);
    let repeated_roots = vec![repeated; ay_proof::MAX_BV_LIA_QUERY_ROOTS * 4];
    assert_eq!(
        collect_bounded_bv_lia_roots(&terms, &repeated_roots),
        Some(vec![repeated])
    );

    let distinct: Vec<_> = (0..=ay_proof::MAX_BV_LIA_QUERY_ROOTS)
        .map(|index| terms.mk_var(format!("bv_lia_distinct_root_{index}"), Sort::Bool))
        .collect();
    assert_eq!(
        collect_bounded_bv_lia_roots(&terms, &distinct[..ay_proof::MAX_BV_LIA_QUERY_ROOTS]),
        Some(distinct[..ay_proof::MAX_BV_LIA_QUERY_ROOTS].to_vec())
    );
    assert!(collect_bounded_bv_lia_roots(&terms, &distinct).is_none());
}

fn assumption_epoch_fixture() -> (Executor, TermId, TermId) {
    let commands = ay_frontend::parse(
        "(set-option :produce-proofs true)\n\
         (declare-const proof_epoch_base Bool)\n\
         (assert proof_epoch_base)",
    )
    .expect("proof epoch fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("proof epoch fixture must elaborate");
    let base = executor.ctx.assertions[0];
    let assumption = executor.ctx.terms.mk_not_raw(base);
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[assumption]);
    executor.last_assumptions = Some(vec![assumption]);
    (executor, base, assumption)
}

#[test]
fn internal_bv_lia_rebuild_authority_includes_exact_bound_assumptions() {
    let (executor, base, assumption) = assumption_epoch_fixture();
    assert_eq!(
        executor.authenticated_authored_roots_for_internal_certificate(),
        vec![base, assumption],
        "the strict internal proof must cover the exact check-sat-assuming query"
    );
}

#[test]
fn internal_bv_lia_rebuild_authority_rejects_mismatched_assumption_window() {
    let (mut executor, _, assumption) = assumption_epoch_fixture();
    let unrelated = executor
        .ctx
        .terms
        .mk_var("proof_epoch_unrelated", Sort::Bool);
    executor.last_assumptions = Some(vec![unrelated]);
    assert!(
        executor
            .authenticated_authored_roots_for_internal_certificate()
            .is_empty(),
        "a solver-visible assumption window different from the bound epoch must fail closed"
    );
    executor.last_assumptions = Some(vec![assumption]);
    assert!(!executor
        .authenticated_authored_roots_for_internal_certificate()
        .is_empty());

    executor.last_assumptions = Some(vec![assumption, unrelated]);
    assert!(executor
        .authenticated_authored_roots_for_internal_certificate()
        .is_empty());
}

#[test]
fn internal_bv_lia_rebuild_authority_rejects_mismatched_provenance() {
    let (mut executor, _, _) = assumption_epoch_fixture();
    let unrelated = executor
        .ctx
        .terms
        .mk_var("proof_epoch_foreign_provenance", Sort::Bool);
    let provenance = executor
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("public solve installs provenance");
    provenance.original_problem_assertions = vec![unrelated];
    assert!(executor
        .authenticated_authored_roots_for_internal_certificate()
        .is_empty());

    executor.proof_problem_assertion_provenance = None;
    assert!(executor
        .authenticated_authored_roots_for_internal_certificate()
        .is_empty());
}

#[test]
fn assumption_is_load_bearing_for_internal_bv_lia_rebuild() {
    let (mut executor, base, assumption) = assumption_epoch_fixture();
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    executor.last_proof = Some(proof);
    executor.refresh_authenticated_bv_lia_internal_certificate_for_publication();
    let rebuilt = executor
        .last_proof
        .as_ref()
        .expect("the proof remains available");
    ay_proof::check_proof_strict(rebuilt, &executor.ctx.terms)
        .expect("base plus its exact negated assumption has a strict certificate");
    ay_proof::validate_reachable_assumes_in_problem_scope(rebuilt, &[base, assumption])
        .expect("the proof uses only the exact query roots");
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(rebuilt, &[base]).is_err(),
        "the satisfiable base alone must not authorize a proof that omits its load-bearing assumption"
    );
}

#[test]
fn internal_bv_lia_rebuild_authority_rejects_reused_assumption_slot() {
    let commands = ay_frontend::parse(
        "(set-option :produce-proofs true)\n\
         (declare-const proof_epoch_stale_base Bool)\n\
         (assert proof_epoch_stale_base)",
    )
    .expect("stale proof epoch fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("stale proof epoch fixture must elaborate");
    let checkpoint = executor.ctx.terms.rollback_checkpoint();
    let assumption = executor
        .ctx
        .terms
        .mk_var("proof_epoch_stale_assumption", Sort::Bool);
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[assumption]);
    executor.last_assumptions = Some(vec![assumption]);

    executor.ctx.terms.rollback_to(checkpoint);
    let replacement = executor
        .ctx
        .terms
        .mk_var("proof_epoch_replacement", Sort::Bool);
    assert_eq!(replacement, assumption, "the canary must reuse the term id");
    assert!(
        executor
            .authenticated_authored_roots_for_internal_certificate()
            .is_empty(),
        "a replaced term entry must retire internal proof authority"
    );
}

include!("proof_original_rebuild_bv_lia_tests/seq_extensional_companion.rs");
