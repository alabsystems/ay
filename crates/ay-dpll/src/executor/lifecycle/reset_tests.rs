// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn direct_reset_revokes_every_query_artifact() {
    let mut executor = Executor::new();
    let old_term = executor.ctx.terms.true_term();
    let old_deadline = ay_core::time::Instant::now() + Duration::from_mins(1);
    executor.set_deadline(Some(old_deadline));
    assert_eq!(
        executor
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("mint a checked SAT certificate"),
        SolveResult::Sat
    );
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(Model::empty());
    executor.last_lrat_certificate = Some(vec![1]);
    executor.last_proof_rebuild_originals.push(old_term);
    executor.last_proof_raw_original_assertions.push(old_term);
    executor
        .last_proof_expanded_let_sources
        .push((old_term, 0, "(let ((x true)) x)".to_string()));
    executor.pareto_state = Some(optimization::ParetoState::default());
    // An unattained (epsilon) optimum for objective 0 and an unavailable
    // lexicographic suffix at objective 1, as `optimize_lex` leaves them after
    // an unattained prefix. Both name the old problem's objectives by
    // declaration index, which the next problem's objectives reuse.
    let sup = num_rational::BigRational::from_integer(4.into());
    let eps_coeff = num_rational::BigRational::from_integer((-1).into());
    executor
        .infinitesimal_objectives
        .insert(0, (sup, eps_coeff));
    executor.unavailable_objectives.insert(1);
    executor.self_check_authored_assertions = Some(vec![old_term]);
    executor.independent_gate_authored_assertions = Some(vec![old_term]);

    executor.reset();

    assert!(executor.last_result.is_none());
    assert!(executor.last_model.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_lrat_certificate.is_none());
    assert!(executor.last_proof_rebuild_originals.is_empty());
    assert!(executor.last_proof_raw_original_assertions.is_empty());
    assert!(executor.last_proof_expanded_let_sources.is_empty());
    assert!(executor.pareto_state.is_none());
    assert!(
        executor.infinitesimal_objectives.is_empty(),
        "an epsilon optimum survived the reset"
    );
    assert!(
        executor.unavailable_objectives.is_empty(),
        "an unavailable-suffix marker survived the reset"
    );
    assert!(executor.self_check_authored_assertions.is_none());
    assert!(executor.independent_gate_authored_assertions.is_none());
    assert_eq!(executor.solve_deadline.get(), None);
    assert_eq!(executor.certification_deadline.get(), None);
}

#[test]
fn command_reset_revokes_solve_local_authored_windows() {
    let mut executor = Executor::new();
    let old_term = executor.ctx.terms.true_term();
    executor.self_check_authored_assertions = Some(vec![old_term]);
    executor.independent_gate_authored_assertions = Some(vec![old_term]);

    assert!(executor
        .execute(&Command::Reset)
        .expect("SMT reset executes")
        .is_none());

    assert!(executor.self_check_authored_assertions.is_none());
    assert!(executor.independent_gate_authored_assertions.is_none());
}

#[test]
fn command_reset_assertions_revokes_solve_local_authored_windows() {
    let mut executor = Executor::new();
    let old_term = executor.ctx.terms.true_term();
    executor.ctx.assertions.push(old_term);
    executor.self_check_authored_assertions = Some(vec![old_term]);
    executor.independent_gate_authored_assertions = Some(vec![old_term]);

    assert!(executor
        .execute(&Command::ResetAssertions)
        .expect("SMT reset-assertions executes")
        .is_none());

    assert!(executor.ctx.assertions.is_empty());
    assert!(executor.self_check_authored_assertions.is_none());
    assert!(executor.independent_gate_authored_assertions.is_none());
    assert!(executor.independent_gate_query_roots().unwrap().is_empty());
}

/// `(reset)` rebuilds every executor field that describes a problem, a query or
/// the session's history, and keeps the host's configuration.
///
/// The frontend replaces its term store on `(reset)`, so any `TermId` the
/// executor keeps names a term of the NEXT problem, or none. On 36a5da9d7 the
/// first field below survived the reset and crashed the next query's read-pin
/// repair (`index out of bounds: the len is 7 but the index is 247`).
#[test]
fn command_reset_rebuilds_session_state_and_keeps_host_configuration() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let mut executor = Executor::new();
    executor.set_self_check(true);
    executor.set_produce_proofs(true);
    executor.set_competition_mode(true);
    executor.set_timeout(Some(Duration::from_secs(7)));
    executor.set_memory_limit(Some(1 << 30));
    executor.set_random_seed(11);
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let deadline = ay_core::time::Instant::now() + Duration::from_mins(5);
    executor.set_deadline(Some(deadline));

    executor.last_rejected_array_assertion = Some(TermId(247));
    executor.qfax_refinement_clause = Some(vec![(TermId(9), true)]);
    executor.qfax_isolated_retry_done = true;
    executor.bv_subst_retry_done = true;
    executor.residue_probe_failures = 3;
    executor.eqdv_retention_off_declined_at_steps.set(5);
    executor.cegar_emitted_lemmas.insert(TermId(12));
    executor
        .recorded_var_substitutions
        .insert(TermId(1), TermId(2));
    executor.row_seeded_terms.insert(TermId(3));
    executor.bool_arg_orphan_index.insert(TermId(4), TermId(5));
    executor.incremental_mode = true;

    assert!(executor
        .execute(&Command::Reset)
        .expect("SMT reset executes")
        .is_none());

    assert_eq!(executor.last_rejected_array_assertion, None);
    assert!(executor.qfax_refinement_clause.is_none());
    assert!(!executor.qfax_isolated_retry_done);
    assert!(!executor.bv_subst_retry_done);
    assert_eq!(executor.residue_probe_failures, 0);
    assert_eq!(executor.eqdv_retention_off_declined_at_steps.get(), 0);
    assert!(executor.cegar_emitted_lemmas.is_empty());
    assert!(executor.recorded_var_substitutions.is_empty());
    assert!(executor.row_seeded_terms.is_empty());
    assert!(executor.bool_arg_orphan_index.is_empty());
    assert!(!executor.incremental_mode);

    assert!(executor.self_check());
    assert!(executor.is_producing_proofs());
    assert!(executor.competition_mode());
    assert_eq!(executor.timeout(), Some(Duration::from_secs(7)));
    assert_eq!(executor.memory_limit, Some(1 << 30));
    assert_eq!(executor.random_seed, Some(11));
    assert_eq!(executor.current_random_seed(), 11);
    assert!(executor
        .solve_interrupt
        .as_ref()
        .is_some_and(|flag| Arc::ptr_eq(flag, &interrupt)));
    assert_eq!(executor.solve_deadline.get(), Some(deadline));
}

/// SMT-LIB `(reset)` returns options to their initial values. The resource
/// options a script set go back to the HOST's values; the ones the host set
/// and the script never touched stay.
///
/// Measured before this fix, in one resident session: `(set-option :timeout
/// 1)`, `(reset)`, then a query a fresh process answers `unsat` answered
/// `unknown (timeout)`, because `(reset)` carried every resource field over
/// as host configuration.
#[test]
fn command_reset_restores_script_set_resource_options_to_the_host_values() {
    let mut executor = Executor::new();
    // Host configuration.
    executor.set_timeout(Some(Duration::from_secs(7)));
    executor.set_memory_limit(Some(1 << 30));
    executor.set_random_seed(11);
    let host_resource_limit = executor.resource_limit();
    let host_ground_budget = executor.ground_budget_enabled();
    assert!(host_ground_budget, "the default ground budget is on");

    let script = ay_frontend::parse(
        "(set-option :timeout 1)\
         (set-option :rlimit 0)\
         (set-option :max-memory 3)\
         (set-option :random-seed 99)\
         (set-option :timeout 2)",
    )
    .expect("script parses");
    executor.execute_all(&script).expect("options apply");
    assert_eq!(executor.timeout(), Some(Duration::from_millis(2)));
    assert_eq!(executor.resource_limit(), None);
    assert!(!executor.ground_budget_enabled());
    assert_eq!(executor.memory_limit, Some(3 << 20));
    assert_eq!(executor.random_seed, Some(99));
    assert_eq!(executor.current_random_seed(), 99);

    assert!(executor
        .execute(&Command::Reset)
        .expect("SMT reset executes")
        .is_none());

    assert_eq!(
        executor.timeout(),
        Some(Duration::from_secs(7)),
        "the host's timeout, not either value the script set"
    );
    assert_eq!(executor.resource_limit(), host_resource_limit);
    assert_eq!(executor.ground_budget_enabled(), host_ground_budget);
    assert_eq!(executor.memory_limit, Some(1 << 30));
    assert_eq!(executor.random_seed, Some(11));
    assert_eq!(executor.current_random_seed(), 11);

    // A second window that sets nothing keeps the host values across a
    // further reset, and a script `:rlimit` with a budget is undone too.
    let script = ay_frontend::parse("(set-option :rlimit 5)").expect("script parses");
    executor.execute_all(&script).expect("option applies");
    assert_eq!(executor.resource_limit(), Some(5));
    executor
        .execute(&Command::Reset)
        .expect("SMT reset executes");
    assert_eq!(executor.resource_limit(), host_resource_limit);
    assert_eq!(executor.timeout(), Some(Duration::from_secs(7)));
}

/// The measured crash, at the executor boundary: a QF_AUFLIA query whose model
/// the strict array oracle rejects, `(reset)`, then a QF_UFLIA query. The
/// second answer must be the fresh executor's.
#[test]
fn a_query_after_reset_decides_as_a_fresh_executor() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let read = |relative: &str| {
        let path = root.join(relative);
        std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
            .replace("(exit)", "")
    };
    let first = ay_frontend::parse(&read(
        "tests/group_auflia/data/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2",
    ))
    .expect("parse the first query");
    let second = ay_frontend::parse(&read(
        "../../benchmarks/smt/QF_UFLIA/sat_nested_function.smt2",
    ))
    .expect("parse the second query");

    let fresh = Executor::new()
        .execute_all(&second)
        .expect("second query in a fresh executor");
    assert_eq!(fresh, ["sat"]);

    let mut executor = Executor::new();
    assert_eq!(executor.execute_all(&first).expect("first query"), ["sat"]);
    assert!(executor.execute(&Command::Reset).expect("reset").is_none());
    assert_eq!(
        executor
            .execute_all(&second)
            .expect("second query after reset"),
        fresh
    );
}
