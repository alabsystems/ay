// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Resource, composition, and publication regressions for checked SAT refutations.

#[test]
fn fired_interrupt_cancels_trace_conversion_before_sidecar_refresh() {
    let (mut executor, proposition, _) = contradictory_unit_executor();
    // The successful solve has already consumed its large clause-trace
    // payload after minting the sidecar. Install a fresh, solver-stamped
    // candidate so this regression reaches the conversion boundary whose
    // caller-control propagation it exercises.
    let mut sat = ay_sat::Solver::new(1);
    sat.enable_clause_trace();
    sat.add_clause(vec![Literal::positive(Variable::new(0))]);
    sat.add_clause(vec![Literal::negative(Variable::new(0))]);
    assert!(sat.solve().into_inner().is_unsat());
    executor.last_clause_trace = sat.take_clause_trace();
    let mut var_to_term = HashMap::default();
    var_to_term.insert(0, proposition);
    executor.last_var_to_term = Some(var_to_term);
    executor.set_interrupt(Arc::new(AtomicBool::new(true)));

    let error = CheckedSatRefutation::build(&mut executor)
        .expect_err("a fired caller interrupt must reject SAT-refutation conversion");
    assert!(
        matches!(
            error,
            CheckedSatRefutationError::CertificationResource(ResolutionValidationError::Cancelled)
        ),
        "unexpected checked-refutation cancellation error: {error:?}"
    );
}

#[test]
fn post_replay_phases_share_work_and_byte_allowances() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(41, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(7, vec![Literal::negative(Variable::new(0))], true);
    trace.add_clause_with_hints(90, Vec::new(), false, vec![41, 7]);
    let validated =
        validate_clause_trace_resolution(&trace, 1, &ResolutionValidationLimits::unbounded())
            .expect("two contrary units have a checked refutation");

    let mut work_limits = ResolutionValidationLimits::unbounded();
    work_limits.max_work = validated.validation_work();
    let mut work_meter = CheckedRefutationMeter::resume(work_limits, None, None, &validated)
        .expect("the exact already-consumed work fits");
    assert!(matches!(
        work_meter.charge(1, 0),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            ..
        })
    ));

    let mut byte_limits = ResolutionValidationLimits::unbounded();
    byte_limits.max_bytes = validated.retained_bytes();
    let mut byte_meter = CheckedRefutationMeter::resume(byte_limits, None, None, &validated)
        .expect("the exact retained trace payload fits");
    assert!(matches!(
        byte_meter.charge(0, 1),
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        })
    ));
}

#[test]
fn post_replay_phase_observes_inherited_interrupt() {
    let mut trace = ClauseTrace::new();
    trace.add_clause(41, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(7, vec![Literal::negative(Variable::new(0))], true);
    trace.add_clause_with_hints(90, Vec::new(), false, vec![41, 7]);
    let validated =
        validate_clause_trace_resolution(&trace, 1, &ResolutionValidationLimits::unbounded())
            .expect("two contrary units have a checked refutation");
    let fired = Arc::new(AtomicBool::new(true));

    assert!(matches!(
        CheckedRefutationMeter::resume(
            ResolutionValidationLimits::unbounded(),
            Some(fired),
            None,
            &validated,
        ),
        Err(ResolutionValidationError::Cancelled)
    ));
}

#[test]
fn composition_normalization_is_precharged_before_allocation_and_sort() {
    let clause: Vec<TermId> = (0..4096).rev().map(TermId).collect();
    let mut meter = CheckedRefutationMeter::unbounded();
    meter.limits.max_work = 1000;

    let error = normalize_clause_metered(&clause, &mut meter)
        .expect_err("a wide normalization must consume the aggregate work allowance");
    assert!(matches!(
        error,
        ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            limit: 1000,
            ..
        }
    ));
}

#[test]
fn authored_root_copy_is_precharged_before_allocation() {
    let roots = [TermId(0), TermId(1)];
    let mut meter = CheckedRefutationMeter::unbounded();
    meter.limits.max_bytes = size_of::<TermId>();

    let error = metered_term_id_copy(&roots, &mut meter)
        .expect_err("the retained root copy must consume the aggregate byte allowance");
    assert!(matches!(
        error,
        ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            ..
        }
    ));
}

#[test]
fn exact_assumption_mapping_preserves_order_polarity_and_fails_on_ambiguity() {
    let mut terms = TermStore::new();
    let proposition = terms.mk_var("mapped_p", Sort::Bool);
    let not_proposition = terms.mk_not_raw(proposition);
    let mut map = HashMap::default();
    map.insert(0, proposition);
    let literals = exact_assumption_sat_literals(
        &[not_proposition, proposition],
        &map,
        &terms,
        1,
        &mut CheckedRefutationMeter::unbounded(),
    )
    .expect("both polarities have one exact SAT mapping");
    assert_eq!(
        literals,
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(0)),
        ]
    );

    map.insert(1, proposition);
    let error = exact_assumption_sat_literals(
        &[proposition],
        &map,
        &terms,
        2,
        &mut CheckedRefutationMeter::unbounded(),
    )
    .expect_err("two SAT variables for one assumption are not exact authority");
    assert!(matches!(
        error,
        CheckedSatRefutationError::AmbiguousAssumptionMapping {
            assumption_index: 0,
            assumption,
        } if assumption == proposition
    ));
}

#[test]
fn generic_premise_requires_exact_positive_semantic_memo_entry() {
    let mut terms = TermStore::new();
    let proposition = terms.mk_var("semantic_generic_p", Sort::Bool);
    let mut proof = Proof::new();
    let generic =
        proof.add_theory_lemma_with_kind("theory", vec![proposition], TheoryLemmaKind::Generic);

    let authenticate = || {
        ay_proof::authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
            &proof,
            &terms,
            None,
            None,
            &[],
            &mut |_, _| true,
        )
        .expect("the proof kernel must separate the Generic obligation")
    };

    let key = vec![TheoryLit::new(proposition, false)];
    let mut rejected_memo = ConflictSemanticVerifyMemo::default();
    rejected_memo.insert(key.clone(), false);
    let error = SemanticallyCompletedPremiseClauses::complete(
        authenticate(),
        &rejected_memo,
        &terms,
        &mut CheckedRefutationMeter::unbounded(),
    )
    .expect_err("a memoized semantic rejection is not premise authority");
    assert!(matches!(
        error,
        CheckedSatRefutationError::DeferredGenericNotSemanticallyVerified { step }
            if step == generic
    ));

    let mut accepted_memo = ConflictSemanticVerifyMemo::default();
    accepted_memo.insert(key, true);
    let completed = SemanticallyCompletedPremiseClauses::complete(
        authenticate(),
        &accepted_memo,
        &terms,
        &mut CheckedRefutationMeter::unbounded(),
    )
    .expect("the exact current semantic verifier verdict discharges the obligation");
    assert_eq!(completed.clause(generic), Some([proposition].as_slice()));
}

#[test]
fn mismatched_same_id_trace_and_fragment_are_rejected() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Bool);
    let not_q = terms.mk_not_raw(q);

    let mut trace_a = ClauseTrace::new();
    trace_a.add_clause(5, vec![Literal::positive(Variable::new(0))], true);
    trace_a.add_clause(9, vec![Literal::negative(Variable::new(0))], true);
    trace_a.add_clause_with_hints(12, Vec::new(), false, vec![5, 9]);
    let validated_a = validate_clause_trace_resolution(
        &trace_a,
        1,
        &ResolutionValidationLimits {
            deadline: None,
            max_original_clauses: 8,
            max_original_literals: 8,
            max_derived_steps: 8,
            max_derived_literals: 8,
            max_hints: 8,
            max_work: 128,
            max_bytes: 64 * 1024,
        },
    )
    .expect("trace A is structurally valid");

    let mut trace_b = ClauseTrace::new();
    trace_b.add_clause(5, vec![Literal::positive(Variable::new(1))], true);
    trace_b.add_clause(9, vec![Literal::negative(Variable::new(1))], true);
    trace_b.add_clause_with_hints(12, Vec::new(), false, vec![5, 9]);
    let mut map_b = HashMap::default();
    map_b.insert(1, q);
    let fragment_b = SatProofManager::new(&map_b, &mut terms)
        .build_exact_original_proof_fragment(&trace_b, &[q, not_q])
        .expect("trace B units have exact authored authority");
    let authenticated_b =
        ay_proof::authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
            fragment_b.proof(),
            &terms,
            None,
            None,
            &[q, not_q],
            &mut |_, _| true,
        )
        .expect("trace B fragment is strictly authenticated");
    let authenticated_b = SemanticallyCompletedPremiseClauses::complete(
        authenticated_b,
        &ConflictSemanticVerifyMemo::default(),
        &terms,
        &mut CheckedRefutationMeter::unbounded(),
    )
    .expect("trace B fragment has no deferred Generic premise");

    let error = verify_exact_composition(
        &validated_a,
        &fragment_b,
        &authenticated_b,
        None,
        &map_b,
        &[],
        &mut terms,
        &mut CheckedRefutationMeter::unbounded(),
    )
    .expect_err("same stable IDs cannot join evidence from different traces");
    assert!(matches!(
        error,
        CheckedSatRefutationError::BindingSourceMismatch { trace_id: 5 }
    ));
}

#[test]
fn checked_sidecar_is_independent_of_an_unrequested_alethe_presentation() {
    let (mut accepted, _, _) = contradictory_unit_executor();
    let mut trust_proof = Proof::new();
    trust_proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    accepted.last_proof = Some(trust_proof);
    let result = accepted.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(result.is_unsat());
    assert!(accepted.admit_command_solve_result(result).is_unsat());
    assert!(!accepted.last_command_unsat_was_strictly_verified());
    assert!(accepted.last_command_unsat_was_independently_verified());
    assert!(!accepted.last_command_unsat_was_exact_semantically_verified());

    let (mut malformed, _, _) = contradictory_unit_executor();
    malformed.last_proof = Some(Proof::new());
    let result = malformed.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(result.is_unsat());
    assert!(malformed.admit_command_solve_result(result).is_unsat());
    assert!(!malformed.last_command_unsat_was_strictly_verified());
    assert!(malformed.last_command_unsat_was_independently_verified());
    assert!(!malformed.last_command_unsat_was_exact_semantically_verified());

    // An explicit proof request promises that the Alethe presentation
    // itself checks. The same independent theorem cannot satisfy that
    // stronger artifact contract when the presentation is malformed.
    let (mut required, _, _) = contradictory_unit_executor();
    required.set_produce_proofs(true);
    required.last_proof = Some(Proof::new());
    let result = required.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(result.is_unknown());
    assert!(required.take_unsat_certificate().is_none());
}

#[test]
fn changed_source_stamp_retires_checked_sidecar() {
    let (mut executor, _, _) = contradictory_unit_executor();
    let mut trust_proof = Proof::new();
    trust_proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    executor.last_proof = Some(trust_proof);

    executor
        .ctx
        .process_command(&Command::Push(1))
        .expect("direct frontend mutation succeeds");
    let result = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(result.is_unknown());
    assert!(executor.take_unsat_certificate().is_none());
}

#[test]
fn missing_authoritative_namespace_and_nonempty_assumptions_decline() {
    let (mut unstamped, _) = unstamped_contradictory_unit_executor();
    unstamped.refresh_checked_sat_refutation();
    assert!(unstamped.last_checked_sat_refutation.is_none());

    let (mut assuming, proposition) = unstamped_contradictory_unit_executor();
    assuming.bind_unsat_query_assumptions(&[proposition]);
    assuming.refresh_checked_sat_refutation();
    assert!(assuming.last_checked_sat_refutation.is_none());
}

#[test]
fn finite_replay_limits_remain_explicit() {
    let executor = Executor::new();
    let limits = validation_limits(&executor);
    assert!(limits.max_original_clauses < usize::MAX);
    assert!(limits.max_derived_steps < usize::MAX);
    assert!(limits.max_work < u64::MAX);
    assert!(limits.max_bytes < usize::MAX);
}
