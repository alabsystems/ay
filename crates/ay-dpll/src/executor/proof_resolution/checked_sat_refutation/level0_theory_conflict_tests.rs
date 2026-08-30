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
fn level0_theory_conflict_trace_error(
    executor: &Executor,
) -> Option<ClauseTraceResolutionError> {
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
    let mut executor =
        level0_theory_conflict_executor("benchmarks/smt/QF_UFLIA/unsat_congruence_to_lia.smt2");

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

/// The companion shape (`theory_callback.rs::handle_conflict_clause`, and the
/// level-0 arm when the conflict clause is empty): the theory reported UNSAT
/// with NO explanation whatsoever. No receipt exists and none can be built, so
/// nothing is recorded and the trace still carries only the bare UNSAT marker.
///
/// `chain_10`'s recorded clause set is six unit clauses over six distinct
/// atoms — propositionally SATISFIABLE. Nothing may EVER mint from it, and
/// this test is the fail-closed pin on that.
///
/// The decline stays imprecise on purpose. Stamping
/// `mark_proof_work_exhausted()` to make it honest was measured to abandon SAT
/// proof reconstruction (`sat_proof_manager/mod.rs`), degenerate the SMT proof
/// to a `TheoryLemma { Generic }`, and turn published UNSAT verdicts into
/// `unknown`. See the comment at the producer.
#[test]
fn unexplained_level0_theory_conflict_never_mints() {
    let mut executor = level0_theory_conflict_executor("benchmarks/smt/QF_UF/chain_10.smt2");

    let trace_error = level0_theory_conflict_trace_error(&executor);
    assert!(
        trace_error.is_some(),
        "a trace with no derivation must never resolve into a refutation"
    );

    assert!(
        executor.last_checked_sat_refutation.is_none(),
        "an unexplained theory UNSAT must never mint a refutation"
    );
    assert!(
        CheckedSatRefutation::build(&mut executor).is_err(),
        "an unexplained theory UNSAT must never mint a refutation"
    );
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
