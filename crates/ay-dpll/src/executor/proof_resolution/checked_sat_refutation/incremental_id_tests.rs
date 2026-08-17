/// The solver's stable clause ids must stay unique, so the trace this lane is
/// handed is resolvable.
///
/// `next_original_clause_id` (input clauses plus the unscoped theory-lemma
/// axiom lane) and `next_clause_id` (conflict-analysis derivations) are two
/// cursors over ONE id space. Only the original -> derived direction used to
/// be synced, so the first input clause or theory lemma added AFTER conflict
/// analysis had consumed ids re-issued an id already stamped on a live clause.
/// `ClauseTraceResolutionError::DuplicateClauseId` then refused the whole
/// trace, because a hint naming that id has two possible antecedents.
///
/// The query below is the smallest incremental shape that reproduced it: the
/// first `(check-sat)` is SAT but forces conflict analysis, and the assertions
/// added afterwards enter the same persistent SAT solver.
#[test]
fn incremental_solve_keeps_stable_clause_ids_unique() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (or a b))
        (assert (or (not a) (> x 3)))
        (assert (or (not b) (< x 1)))
        (check-sat)
        (assert (> x 100))
        (assert (< x 0))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(input).expect("parse the incremental query");
    let mut executor = Executor::new();
    let outputs = executor.execute_all(&commands).expect("execute the query");
    assert_eq!(outputs, vec!["sat".to_string(), "unsat".to_string()]);

    let trace = executor
        .last_clause_trace
        .as_ref()
        .expect("the proof-enabled incremental solve retains its SAT clause trace");
    let mut first_index: HashMap<u64, usize> = HashMap::default();
    for (index, entry) in trace.entries().iter().enumerate() {
        if let Some(first) = first_index.insert(entry.id, index) {
            panic!(
                "clause trace id {} is duplicated at entries {first} and {index}",
                entry.id
            );
        }
    }

    // Run the production converter. Every other refusal remains legitimate;
    // only a malformed stable-id namespace is forbidden here.
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
    if let Err(error) = validate_clause_trace_resolution(trace, num_vars, &limits) {
        assert!(
            !matches!(
                error,
                ClauseTraceResolutionError::DuplicateClauseId { .. }
                    | ClauseTraceResolutionError::ZeroClauseId { .. }
            ),
            "the solver handed the checked-refutation lane a malformed id namespace: {error}"
        );
    }

    let proof = executor
        .last_proof()
        .expect("a :produce-proofs UNSAT publishes a refutation");
    ay_proof::check_proof_strict(proof, executor.terms())
        .expect("the strict checker must accept the emitted refutation");
}
