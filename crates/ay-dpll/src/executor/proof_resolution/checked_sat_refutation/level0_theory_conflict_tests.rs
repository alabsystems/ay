// #cert-level0-theory-conflict — a level-0 theory conflict used to be
// DISCARDED before it could be recorded (the `TheoryModelCheck::Conflict` arm
// of `solve/theory_backend.rs`, now routed through
// `conflict_analysis_lrat_specialized/level0_conflict.rs::
// declare_level0_theory_conflict_unsat`). `finalize_unsat_proof` then stamped
// `trace.mark_empty()` (`finalize_unsat.rs`) onto a trace that held NO
// derivation, producing a trace that CLAIMED UNSAT and could not back it.
//
// These tests pin the producer fix and its boundary:
//   * when the theory supplies a real explanation it is recorded, so the trace
//     really does carry a derived empty clause; and
//   * recording confers NO authority — the instance still DECLINES, now on the
//     honest reason (the recorded T-lemma has no registered proof).
//
// The companion shape — a theory UNSAT with no explanation at all — records
// nothing and must never mint.

/// Enter the theory producer directly. The ordinary public route may first
/// prove congruence by a checked preprocessing lemma and never build this
/// unregistered level-0 theory-conflict trace.
#[cfg(test)]
fn unregistered_level0_uf_lia_executor() -> Executor {
    let input = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/smt/QF_UFLIA/unsat_congruence_to_lia.smt2"
    ));
    let mut commands = ay_frontend::parse(input).expect("parse producer fixture");
    assert!(matches!(
        commands.pop(),
        Some(ay_frontend::Command::CheckSat)
    ));
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("install exact assertions");
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    assert!(executor
        .solve_uf_lia()
        .expect("theory producer solve")
        .is_unsat());
    executor
}

#[cfg(test)]
fn level0_theory_conflict_executor(relative_path: &str) -> Executor {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative_path);
    let input = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let commands = ay_frontend::parse(&input).expect("parse the benchmark");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute the benchmark");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{relative_path} must stay UNSAT, got {outputs:?}",
    );
    executor
}

#[cfg(test)]
fn level0_theory_conflict_trace_error(executor: &Executor) -> Option<ClauseTraceResolutionError> {
    let trace = executor
        .last_clause_trace
        .as_ref()
        .expect("the proof-enabled solve retains its SAT clause trace");
    let num_vars = trace
        .entries()
        .iter()
        .flat_map(|entry| entry.clause.iter())
        .map(|literal| literal.variable().index() + 1)
        .max()
        .unwrap_or(1);
    let limits = ResolutionValidationLimits {
        deadline: None,
        max_original_clauses: 1 << 16,
        max_original_literals: 1 << 20,
        max_derived_steps: 1 << 16,
        max_derived_literals: 1 << 20,
        max_hints: 1 << 20,
        max_work: 1 << 24,
        max_bytes: 64 * 1024 * 1024,
    };
    validate_clause_trace_resolution(trace, num_vars, &limits).err()
}

/// A level-0 theory model conflict with a NON-EMPTY conflict clause: the theory
/// handed over a real explanation, so `declare_level0_theory_conflict_unsat`
/// records the conflict lemma and the trace now carries a genuine derived
/// empty clause.
///
/// The certificate must still fail closed: recording a T-lemma as an
/// `is_original` trace entry confers NO authority, because the exact fragment
/// independently re-derives authority for every original entry
/// (`sat_proof_manager/exact_fragment/build_steps.rs`) and never trusts the
/// flag. Part (b) below is the soundness half of this test.
#[test]
fn level0_theory_conflict_records_derivation_without_conferring_authority() {
    let mut executor = unregistered_level0_uf_lia_executor();

    // (a) The trace no longer claims an UNSAT it never derived.
    let trace_error = level0_theory_conflict_trace_error(&executor);
    assert!(
        !matches!(
            trace_error,
            Some(ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty)
                | Some(ClauseTraceResolutionError::NoDerivedEmptyClause)
        ),
        "a recorded level-0 theory conflict must leave a derived empty clause, \
         not a bare UNSAT marker: {trace_error:?}"
    );
    assert!(
        trace_error.is_none(),
        "the recorded level-0 conflict chain must resolve: {trace_error:?}"
    );

    // (b) SOUNDNESS HALF: no certificate is minted, and the decline is the
    // honest authority decline — the recorded T-lemma has no registered proof.
    assert!(
        executor.last_checked_sat_refutation.is_none(),
        "recording the theory conflict must NOT by itself mint a refutation"
    );
    let error = CheckedSatRefutation::build(&mut executor)
        .err()
        .expect("a T-lemma with no registered proof must not authenticate");
    assert!(
        matches!(
            error,
            CheckedSatRefutationError::OriginalProof(
                ExactOriginalProofError::UnauthenticatedOriginalClause { .. }
            )
        ),
        "expected the exact fragment to refuse the unproven theory lemma, got: {error}"
    );
}

#[test]
fn public_congruence_route_keeps_a_checked_unsat_verdict() {
    let mut solver = crate::api::Solver::new(crate::api::Logic::All);
    solver
        .parse_smtlib2(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../benchmarks/smt/QF_UFLIA/unsat_congruence_to_lia.smt2"
        )))
        .expect("public fixture");
    let details = solver.try_check_sat_with_details().expect("public solve");
    let result = &details.result;
    assert!(result.is_unsat(), "{details:?}");
    assert!(result.has_unsat_emission_witness(), "{details:?}");
    assert!(
        result.was_unsat_strictly_verified()
            || result.was_unsat_independently_verified()
            || result.was_unsat_exact_semantically_verified()
            || result.was_unsat_corroborated(),
        "{details:?}"
    );
}

/// Produce the unexplained boundary directly: six independent authored Bool
/// units are satisfiable, while the actual SAT callback deliberately reports
/// an empty theory conflict. The real producer may mark UNSAT, but it has no
/// explanation to record and no refutation to authenticate.
#[cfg(test)]
fn unexplained_level0_callback_executor() -> Executor {
    let mut executor = Executor::new();
    let propositions: Vec<_> = (0..6)
        .map(|index| {
            executor
                .ctx
                .terms
                .mk_var(format!("unexplained_{index}"), Sort::Bool)
        })
        .collect();
    executor.ctx.assertions = propositions.clone();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);

    let mut sat = ay_sat::Solver::new(propositions.len());
    sat.set_preprocess_enabled(false);
    sat.enable_clause_trace();
    for index in 0..propositions.len() {
        sat.add_clause(vec![Literal::positive(Variable::new(index as u32))]);
    }
    let original_ids_before = sat.issued_original_clause_id_max();
    let mut callback_calls = 0;
    let result = sat.solve_with_theory(|current| {
        callback_calls += 1;
        assert_eq!(current.current_decision_level(), 0);
        for index in 0..propositions.len() {
            assert_eq!(current.value(Variable::new(index as u32)), Some(true));
        }
        // The missing explanation is the test input. No trace entry, proof
        // annotation, scope stamp or successful checked result is fabricated.
        ay_sat::TheoryPropResult::Conflict(Vec::new())
    });
    assert!(
        result.into_inner().is_unsat(),
        "exercise the real empty-conflict producer"
    );
    assert_eq!(callback_calls, 1);
    assert_eq!(
        sat.issued_original_clause_id_max(),
        original_ids_before,
        "an empty explanation installs no original theory lemma"
    );
    let trace = sat
        .take_clause_trace()
        .expect("actual solver-produced trace");
    assert_eq!(trace.solver_num_vars(), Some(propositions.len()));
    assert!(trace
        .scope_assumptions()
        .is_some_and(|scope| scope.is_empty()));
    assert!(!trace.is_truncated());
    assert!(
        trace.has_empty_clause(),
        "the producer supplies only the UNSAT marker"
    );
    assert_eq!(trace.len(), propositions.len());
    let mut variables = Vec::new();
    for entry in trace.entries().iter() {
        assert!(entry.is_original);
        assert!(entry.resolution_hints.is_empty());
        assert_eq!(
            entry.clause.len(),
            1,
            "no explanation or derived empty is recorded"
        );
        let literal = entry.clause[0];
        assert!(
            literal.is_positive(),
            "all-true satisfies the entire recorded clause set"
        );
        variables.push(literal.variable().index());
    }
    variables.sort_unstable();
    assert_eq!(variables, (0..propositions.len()).collect::<Vec<_>>());

    executor.last_clause_trace = Some(trace);
    executor.last_var_to_term = Some(
        propositions
            .iter()
            .copied()
            .enumerate()
            .map(|(index, term)| (index as u32, term))
            .collect(),
    );
    assert!(executor.checked_sat_refutation_query_scope().is_some());
    assert!(executor
        .checked_sat_refutation_query_assumptions()
        .is_some_and(|assumptions| assumptions.is_empty()));
    assert!(executor.last_clausification_proofs.is_none());
    assert!(executor.last_original_clause_theory_proofs.is_none());
    executor.refresh_checked_sat_refutation();
    executor
}

/// A real empty theory callback supplies no explanation. The actual trace is
/// six independent authored units plus the producer's bare UNSAT marker.
/// Every no-mint assertion stays unconditional; the exact structural decline
/// also rules out a vacuous missing-map or unsupported-query failure.
#[test]
fn unexplained_level0_theory_conflict_never_mints() {
    let mut executor = unexplained_level0_callback_executor();

    let trace_error = level0_theory_conflict_trace_error(&executor);
    assert!(
        trace_error.is_some(),
        "a trace with no derivation must never resolve into a refutation"
    );
    assert!(matches!(
        trace_error,
        Some(ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty)
    ));

    assert!(
        executor.last_checked_sat_refutation.is_none(),
        "an unexplained theory UNSAT must never mint a refutation"
    );
    let built = CheckedSatRefutation::build(&mut executor);
    assert!(
        built.is_err(),
        "an unexplained theory UNSAT must never mint a refutation"
    );
    assert!(matches!(
        built,
        Err(CheckedSatRefutationError::StructuralTrace(
            ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty
        ))
    ));
}

/// Preserving the six actual equality causes repairs chain_10's explanation:
/// it now records a nonempty theory lemma and a genuine terminal derivation.
/// Keep that real public route as the positive counterpart to the deliberate
/// empty-explanation input above, including independent strict native proof.
#[test]
fn retained_level0_chain_explanation_mints_a_strict_native_proof() {
    let mut executor = level0_theory_conflict_executor("benchmarks/smt/QF_UF/chain_10.smt2");
    let trace_error = level0_theory_conflict_trace_error(&executor);
    assert!(
        trace_error.is_none(),
        "the retained explanation must resolve: {trace_error:?}"
    );
    let trace = executor
        .last_clause_trace
        .as_ref()
        .expect("actual retained chain trace");
    assert!(
        trace
            .entries()
            .iter()
            .any(|entry| entry.is_original && entry.clause.len() > 1),
        "a nonempty retained explanation must accompany the unit assertions"
    );
    assert!(
        trace
            .entries()
            .iter()
            .any(|entry| !entry.is_original && entry.clause.is_empty()),
        "the real producer must record a derived empty clause"
    );
    assert!(executor.last_checked_sat_refutation.is_some());
    assert!(executor.checked_sat_refutation_authorizes_current_query());
    let checked = CheckedSatRefutation::build(&mut executor)
        .expect("the actual retained chain explanation must authenticate");
    let native = checked
        .native_proof
        .as_ref()
        .expect("actual native proof presentation");
    assert!(executor
        .check_proof_strict_with_datatypes(native)
        .expect("independent strict validation of the real native proof")
        .is_complete());
}

/// The third shape, and the one this producer fix exists to make REACHABLE:
/// the recorded level-0 theory conflict clause is itself an array theory
/// lemma, so the intrinsic array-clause authority arm
/// (`sat_proof_manager/exact_fragment/intrinsic_authority.rs`) re-derives it
/// from the clause alone and the refutation MINTS.
///
/// This is an interaction between two independent halves, and neither half
/// pins it on its own:
///   * without the producer fix the trace has no derived empty clause at all
///     (`EmptyMarkerWithoutDerivedEmpty`), so authority is never even
///     consulted; and
///   * without the intrinsic array arm the recorded lemma is an
///     `is_original` entry with no registered proof and DECLINES on
///     `UnauthenticatedOriginalClause`.
///
/// Nothing else in the suite covers the composition, so a regression in
/// either half would silently drop this mint. The mint is legitimate on its
/// merits: the recorded clause is a read-over-write row chain, discharged
/// against `(not (= i1 i2))` and `(not (= i1 i3))`, i.e. an array-theory
/// tautology the strict checker re-derives via `arrays_row` / `arrays_idx` /
/// `trans` — the exported Alethe carries `unproved_steps=0` and
/// `trust_free=yes`.
#[test]
fn level0_array_theory_conflict_mints_through_intrinsic_authority() {
    let mut executor =
        level0_theory_conflict_executor("benchmarks/smt/QF_AX/nested_store_chain.smt2");

    // The producer half: the trace carries a real derivation.
    let trace_error = level0_theory_conflict_trace_error(&executor);
    assert!(
        trace_error.is_none(),
        "the recorded level-0 array conflict chain must resolve: {trace_error:?}"
    );

    // The authority half: the recorded array lemma is re-derived from the
    // clause alone, so the refutation authenticates end to end.
    CheckedSatRefutation::build(&mut executor).unwrap_or_else(|error| {
        panic!(
            "a recorded level-0 array row-chain lemma must authenticate through \
             the intrinsic array authority arm, got: {error}"
        )
    });
}
