// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for nested finite-array UNSAT authority.

use super::*;

/// A complete extensionality contradiction over a genuinely nested,
/// finite Bool array. This was historically quarantined as Unknown: it has
/// neither a strict translated proof nor an array-free residue, while the
/// exact Bool/BV checker can replay all four finite cells.
fn load_nested_finite_bool_array_contradiction() -> Executor {
    let commands = ay_frontend::parse(
        "(set-logic QF_AX) \
         (declare-const nested_auth_a (Array Bool (Array Bool Bool))) \
         (declare-const nested_auth_b (Array Bool (Array Bool Bool))) \
         (assert (not (= nested_auth_a nested_auth_b))) \
         (assert (= (select (select nested_auth_a false) false) \
                    (select (select nested_auth_b false) false))) \
         (assert (= (select (select nested_auth_a false) true) \
                    (select (select nested_auth_b false) true))) \
         (assert (= (select (select nested_auth_a true) false) \
                    (select (select nested_auth_b true) false))) \
         (assert (= (select (select nested_auth_a true) true) \
                    (select (select nested_auth_b true) true)))",
    )
    .expect("nested finite-array fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("nested finite-array fixture must elaborate");
    executor
}

fn nested_finite_bool_array_contradiction_executor() -> Executor {
    let mut executor = load_nested_finite_bool_array_contradiction();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    executor
}

fn solved_pending_nested_finite_bool_array() -> (Executor, SolveResult) {
    let mut executor = nested_finite_bool_array_contradiction_executor();
    let decision_roots = executor.ctx.assertions.clone();
    let proposed = executor
        .check_sat()
        .expect("nested finite-array contradiction must solve");
    assert!(proposed.is_unsat());
    // The production solve may already carry a stronger strict proof or
    // completed SAT-resolution sidecar. Remove both, then re-enter the same
    // final quarantine on the exact public roots to isolate this authority.
    executor.last_checked_sat_refutation = None;
    executor.last_proof = None;
    let proposed =
        executor.quarantine_unverified_nested_array_unsat(&decision_roots, None, proposed);
    assert!(proposed.is_unsat());
    assert!(
        executor.pending_nested_array_bool_bv_unsat.is_some(),
        "the final quarantine must seal exact finite-array authority"
    );
    (executor, proposed)
}

#[test]
fn strict_proof_prefilter_rejects_stale_or_foreign_query_scope() {
    let commands = ay_frontend::parse(
        "(set-logic QF_UF) \
         (declare-const nested_auth_strict_scope Bool) \
         (assert nested_auth_strict_scope) \
         (assert (not nested_auth_strict_scope))",
    )
    .expect("strict-proof scope fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("strict-proof scope fixture must elaborate");
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    assert!(executor
        .check_sat()
        .expect("strict Boolean contradiction must solve")
        .is_unsat());
    executor.last_checked_sat_refutation = None;
    assert!(executor.last_proof.is_some());
    assert!(executor.nested_array_unsat_proof_authority_is_current());

    let foreign = executor
        .ctx
        .terms
        .mk_fresh_var("nested_auth_foreign_assumption", CoreSort::Bool);
    executor.last_assumptions = Some(vec![foreign]);
    assert!(!executor.nested_array_unsat_proof_authority_is_current());
    executor.last_assumptions = None;

    let original_provenance = executor
        .proof_problem_assertion_provenance
        .clone()
        .expect("public solve must retain authored-root provenance");
    executor
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("provenance remains installed")
        .original_problem_assertions
        .push(foreign);
    assert!(!executor.nested_array_unsat_proof_authority_is_current());
    executor.proof_problem_assertion_provenance = Some(original_provenance);

    executor
        .ctx
        .process_command(&ay_frontend::Command::Push(1))
        .expect("direct frontend mutation must succeed");
    assert!(!executor.nested_array_unsat_proof_authority_is_current());
}

#[test]
fn pending_nested_array_authority_binds_once_into_checked_bool_bv() {
    let (mut executor, proposed) = solved_pending_nested_finite_bool_array();

    // Isolate the affine lane from every stronger authority. The expensive
    // exact finite-array replay already happened and must not be repeated.
    executor.last_checked_sat_refutation = None;
    executor.last_proof = None;
    let published = executor.certify_unsat_for_publication(proposed, &[]);
    assert!(published.is_unsat());
    assert!(executor.pending_nested_array_bool_bv_unsat.is_none());
    let certificate = executor
        .take_unsat_certificate()
        .expect("the moved finite-array theorem must mint one certificate");
    assert!(matches!(
        certificate.0,
        UnsatCertificateKind::CheckedBoolBv(_)
    ));
    assert!(
        executor.take_unsat_certificate().is_none(),
        "both pending authority and the public token are one-shot"
    );
}

#[test]
fn pending_nested_array_authority_rejects_append_only_term_growth() {
    let (mut executor, proposed) = solved_pending_nested_finite_bool_array();
    let _unrelated = executor
        .ctx
        .terms
        .mk_fresh_var("nested_auth_late_suffix", CoreSort::Bool);

    let published = executor.certify_unsat_for_publication(proposed, &[]);
    assert!(published.is_unknown());
    assert!(executor.pending_nested_array_bool_bv_unsat.is_none());
    assert!(executor.take_unsat_certificate().is_none());
    assert_eq!(
        executor.unknown_reason(),
        Some(UnknownReason::SelfCheckRejected)
    );
}

#[test]
fn pending_nested_array_authority_is_retired_by_lifecycle_boundaries() {
    let (mut epoch, _) = solved_pending_nested_finite_bool_array();
    epoch.begin_public_solve(false);
    assert!(epoch.pending_nested_array_bool_bv_unsat.is_none());

    let (mut reset, _) = solved_pending_nested_finite_bool_array();
    reset.reset_solve_session_state();
    assert!(reset.pending_nested_array_bool_bv_unsat.is_none());

    let (mut non_unsat, _) = solved_pending_nested_finite_bool_array();
    assert!(non_unsat
        .certify_unsat_for_publication(SolveResult::Unknown, &[])
        .is_unknown());
    assert!(non_unsat.pending_nested_array_bool_bv_unsat.is_none());

    let (mut invalidated, _) = solved_pending_nested_finite_bool_array();
    invalidated.invalidate_last_check_result();
    assert!(invalidated.pending_nested_array_bool_bv_unsat.is_none());
}

#[test]
fn only_identical_current_assumption_rebind_preserves_pending_authority() {
    let (mut identical, proposed) = solved_pending_nested_finite_bool_array();
    identical.bind_unsat_query_assumptions(&[]);
    assert!(
        identical.pending_nested_array_bool_bv_unsat.is_some(),
        "an exact idempotent wrapper bind must preserve current evidence"
    );
    assert!(identical
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
    assert!(matches!(
        identical
            .last_unsat_certificate
            .as_ref()
            .map(|certificate| &certificate.0),
        Some(UnsatCertificateKind::CheckedBoolBv(_))
    ));

    let (mut changed, _) = solved_pending_nested_finite_bool_array();
    let foreign = changed.ctx.assertions[0];
    changed.bind_unsat_query_assumptions(&[foreign]);
    assert!(
        changed.pending_nested_array_bool_bv_unsat.is_none(),
        "a mismatching late bind must consume pending evidence"
    );
    assert!(matches!(
        changed.mint_unsat_certificate(&[foreign]),
        Err(UnsatCertificationError::AssumptionEpochMismatch)
    ));
}

#[test]
fn pending_nested_array_authority_is_ordered_assumption_bound() {
    let mut executor = load_nested_finite_bool_array_contradiction();
    let first = executor
        .ctx
        .terms
        .mk_fresh_var("nested_auth_assumption_first", CoreSort::Bool);
    let second = executor
        .ctx
        .terms
        .mk_fresh_var("nested_auth_assumption_second", CoreSort::Bool);
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[first, second]);
    assert!(matches!(
        executor.prepare_pending_nested_array_bool_bv_unsat(),
        Ok(true)
    ));

    assert!(matches!(
        executor.mint_unsat_certificate(&[second, first]),
        Err(UnsatCertificationError::AssumptionEpochMismatch)
    ));
    assert!(executor.pending_nested_array_bool_bv_unsat.is_none());
}

#[test]
fn strict_proof_demand_never_accepts_pending_semantic_authority() {
    let (mut after_seal, proposed) = solved_pending_nested_finite_bool_array();
    after_seal.set_produce_proofs(true);
    assert!(
        after_seal
            .certify_unsat_for_publication(proposed, &[])
            .is_unknown(),
        "a late artifact demand must require the artifact itself"
    );
    assert!(after_seal.pending_nested_array_bool_bv_unsat.is_none());
    assert!(after_seal.take_unsat_certificate().is_none());

    let mut before_seal = nested_finite_bool_array_contradiction_executor();
    before_seal.set_produce_proofs(true);
    assert!(matches!(
        before_seal.prepare_pending_nested_array_bool_bv_unsat(),
        Ok(false)
    ));
    assert!(before_seal.pending_nested_array_bool_bv_unsat.is_none());
}

#[test]
fn pending_nested_array_authority_declines_objectives_and_extensions() {
    let mut objective = load_nested_finite_bool_array_contradiction();
    let objective_term = objective
        .ctx
        .terms
        .mk_fresh_var("nested_auth_objective", CoreSort::Int);
    objective.ctx.add_objective(ay_frontend::Objective {
        direction: ay_frontend::ObjectiveDirection::Maximize,
        term: objective_term,
    });
    objective.begin_public_solve(false);
    objective.bind_unsat_query_assumptions(&[]);
    assert!(matches!(
        objective.prepare_pending_nested_array_bool_bv_unsat(),
        Ok(false)
    ));
    assert!(objective.pending_nested_array_bool_bv_unsat.is_none());

    let mut extension = nested_finite_bool_array_contradiction_executor();
    let declared = extension.ctx.terms.mk_bool(true);
    let declared_entry = extension
        .ctx
        .terms
        .entry_stamp(declared)
        .expect("declared extension term must be live");
    let epoch = extension
        .unsat_query_epoch
        .as_mut()
        .expect("fixture must have a public epoch");
    epoch.declared_extension.push(declared);
    epoch.declared_extension_entries.push(declared_entry);
    let extension_result = extension.prepare_pending_nested_array_bool_bv_unsat();
    assert!(
        !matches!(extension_result, Ok(true)),
        "declared extensions must never seal pending authority: {extension_result:?}"
    );
    assert!(extension.pending_nested_array_bool_bv_unsat.is_none());
}

#[test]
fn competition_raw_discards_current_pending_and_rejects_stale_pending() {
    let mut current = load_nested_finite_bool_array_contradiction();
    current.set_competition_mode(true);
    current.begin_public_solve(false);
    current.bind_unsat_query_assumptions(&[]);
    let roots = current.ctx.assertions.clone();
    let proposed = current.check_sat().expect("competition fixture must solve");
    assert!(proposed.is_unsat());
    let proposed = current.quarantine_unverified_nested_array_unsat(&roots, None, proposed);
    assert!(proposed.is_unsat());
    assert!(current.pending_nested_array_bool_bv_unsat.is_some());
    assert!(current
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
    assert!(current.pending_nested_array_bool_bv_unsat.is_none());
    assert!(matches!(
        current
            .last_unsat_certificate
            .as_ref()
            .map(|certificate| &certificate.0),
        Some(UnsatCertificateKind::CompetitionRaw(_))
    ));

    let mut stale = load_nested_finite_bool_array_contradiction();
    stale.set_competition_mode(true);
    stale.begin_public_solve(false);
    stale.bind_unsat_query_assumptions(&[]);
    assert!(matches!(
        stale.prepare_pending_nested_array_bool_bv_unsat(),
        Ok(true)
    ));
    let _late = stale
        .ctx
        .terms
        .mk_fresh_var("nested_auth_competition_late", CoreSort::Bool);
    assert!(stale
        .certify_unsat_for_publication(SolveResult::unsat(), &[])
        .is_unknown());
    assert!(stale.pending_nested_array_bool_bv_unsat.is_none());
    assert!(stale.take_unsat_certificate().is_none());
}
