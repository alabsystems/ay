// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! The trust defect shapes measured THROUGH THIS LANE.
//!
//! `trust-router::in_process_ay_backend` reads the native `AYProgram` bridge —
//! `execute_incremental` — not the SMT-LIB text lane. A shape closed only in
//! the text lane is not closed for trust, and a test that pins it only there
//! reads as coverage it does not have. `ay-dpll`'s
//! `executor_tests::quantifier::trust_defect_shapes` pins the text lane; this
//! file pins the SAME shapes here, and asserts the two agree.
//!
//! # What made them disagree
//!
//! `parse_logic` mapped the attested SMT-LIB names with no [`Logic`] variant
//! (`FP`, `ANIA`, `ABVFP`, …) onto `Logic::All`. That keeps the right
//! CAPABILITY — `ALL` admits more than any named logic — and throws away the
//! ROUTE, which is not the same thing: `ALL` is also the one value that sends
//! `Executor::detect_logic_category` to CONTENT detection, and content
//! detection runs AFTER quantifier preprocessing, over whatever ground
//! assertions survive it.
//!
//! For `∀q:Float64. fp.isNaN(q)` nothing survives it — the single `forall` is
//! unhandled, so the ground window is EMPTY — and content detection of zero
//! assertions infers `QF_UF`. Measured, before the fix:
//!
//! | lane | `ctx.logic()` | category | MBQI | verdict |
//! |---|---|---|---|---|
//! | text, `(set-logic FP)` | `FP` | `QfFp` | 2 rounds, 6 probed | `unsat` |
//! | native, `set_logic("FP")` | `ALL` | `QfUf` | 3 rounds, 11 probed | `Unknown("(incomplete quantifier-unhandled)")` |
//!
//! Both lanes entered the MBQI refutation rescue and both asked MBQI; under
//! `QfUf` the FP theory never ran, so the rescue's ground instance
//! `fp.isNaN(+0.0)` was an uninterpreted atom that nothing refutes. The
//! declared name now reaches the executor (`Declaration::SmtLibName` ->
//! `Solver::try_new_with_smtlib_logic`), and the native row is
//! `QfFp` / 2 rounds / 6 probed / `unsat` — identical to the text lane.
//!
//! [`Logic`]: ay_dpll::api::Logic

use super::*;

/// `Sort::floating_point(11, 53)` — `Float64`.
fn float64() -> Sort {
    Sort::floating_point(11, 53)
}

/// THE `FP` SHAPE, through the lane trust actually reads.
///
/// `∀q:Float64. fp.isNaN(q)` is UNSATISFIABLE, and its truth is established
/// without trusting the answer under test: `fp.isNaN(+0.0)` is false — a
/// GROUND floating-point fact, pinned on its own by
/// `ay-dpll`'s `trust_defect_shapes::closed` — and a universal with a false
/// instance is false.
#[test]
fn fp_universal_is_refuted_through_the_native_bridge() {
    let mut program = AYProgram::new();
    program.set_logic("FP");
    program.assert(Expr::forall(
        vec![("q".to_string(), float64())],
        Expr::var("q", float64()).fp_is_nan(),
    ));
    program.check_sat();

    let outcomes = execute_all_typed(&program).expect("program must execute");
    assert_eq!(outcomes.len(), 1);
    assert!(
        matches!(outcomes[0].result, ExecuteTypedResult::Verified),
        "trust shape `FP`: refuted at +0.0 by an MBQI FP candidate. This lane \
         answered `Unknown(\"(incomplete quantifier-unhandled)\")` while the \
         SMT-LIB text lane answered `unsat`, because the declared `FP` was \
         replaced by `ALL` on the way in. Got: {:?}",
        outcomes[0].result
    );
}

/// The SAME query, through `execute_incremental` by its public name, because
/// that is the entry point `trust-router::in_process_ay_backend` calls. The
/// test above goes through `execute_all_typed`; both reach
/// `incremental::execute_incremental_impl`, and pinning the named one means a
/// future split of the two cannot quietly stop measuring this.
#[test]
fn fp_universal_is_refuted_through_execute_incremental() {
    let mut program = AYProgram::new();
    program.set_logic("FP");
    program.assert(Expr::forall(
        vec![("q".to_string(), float64())],
        Expr::var("q", float64()).fp_is_nan(),
    ));
    program.check_sat();

    let outcomes = crate::execute_direct::execute_incremental(&program).expect("must execute");
    assert!(
        matches!(outcomes[0].result, ExecuteTypedResult::Verified),
        "got: {:?}",
        outcomes[0].result
    );
}

/// NON-VACUITY, and the soundness direction. The declared name now decides the
/// route, so a name that routes to the FP theory must not thereby start
/// REFUTING satisfiable FP universals. `∀q:Float64. fp.isNaN(q) ∨ ¬fp.isNaN(q)`
/// is a tautology — true in every model, so truth-SAT — and the finitely many
/// MBQI candidates can never exhaust `Float64`. It must not come back `unsat`.
#[test]
fn a_tautological_fp_universal_is_never_refuted_through_the_native_bridge() {
    let mut program = AYProgram::new();
    program.set_logic("FP");
    let q = || Expr::var("q", float64());
    program.assert(Expr::forall(
        vec![("q".to_string(), float64())],
        q().fp_is_nan().or(q().fp_is_nan().not()),
    ));
    program.check_sat();

    let outcomes = execute_all_typed(&program).expect("program must execute");
    assert!(
        !matches!(outcomes[0].result, ExecuteTypedResult::Verified),
        "a tautological FP universal must never be refuted: every MBQI \
         candidate satisfies it, so an `unsat` here would be a wrong verdict. \
         Got: {:?}",
        outcomes[0].result
    );
}

/// The DECLARED LOGIC reaches the executor. This is the mechanism the two
/// tests above depend on, pinned directly so a regression names its own cause
/// rather than showing up only as a lost verdict.
///
/// `FP` has no [`Logic`] variant (`"FP".parse::<Logic>()` is an `Err`), so
/// before the fix this lane had no way to spell it and substituted `ALL`.
///
/// [`Logic`]: ay_dpll::api::Logic
#[test]
fn an_attested_name_without_a_logic_variant_still_reaches_the_executor() {
    assert!(
        "FP".parse::<ay_dpll::api::Logic>().is_err(),
        "non-vacuity: if `Logic` ever grows an `FP` variant this test stops \
         measuring the by-name path and should move to a name that has none"
    );
    assert!(ay_dpll::api::Solver::try_new_with_smtlib_logic("FP").is_ok());
    // The lane installs it by NAME rather than substituting `ALL`. The name
    // WHITELIST is still this lane's (`is_smt_lib_logic`) — the constructor is
    // as lenient about names as `(set-logic ...)` is — and
    // `test_logic_names::fabricated_logic_names_are_still_refused` pins that
    // a made-up name never gets this far.
    let mut program = AYProgram::new();
    program.set_logic("FP");
    assert_eq!(
        super::super::logic::parse_logic(&program).expect("FP is attested"),
        super::super::logic::Declaration::SmtLibName("FP".to_string())
    );
}

/// The `(set-option ...)` commands `trust-router`'s `build_program` emits for
/// the backend `a_binder_survives_its_own_retained_source` runs
/// (`InProcessAyBackend::new().with_timeout(30_000)`), in its order:
/// `:produce-proofs true`, the `:timeout 30000` wall backstop, and the
/// `:rlimit 100000` conflict budget of `VcEffort::builtin()`, which trust
/// sends on every query (`qsat_refused_sat_resolve` does not re-solve after
/// a resource stop, so a budget that ended the route or the gate would end
/// the query `unknown` on trust's lane). Then one closed assertion and its
/// `check-sat`, under `logic`.
fn closed_program_under_produce_proofs(logic: &str, sentence: Expr) -> AYProgram {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.set_logic(logic);
    program.add_constraint(Constraint::set_option(":produce-proofs", "true"));
    program.add_constraint(Constraint::set_option(":timeout", "30000"));
    program.add_constraint(Constraint::set_option(":rlimit", "100000"));
    program.assert(sentence);
    program.check_sat();
    program
}

/// `∀q:Int. ∃r:Int. body(q, r)`.
fn forall_exists_int(body: fn(Expr, Expr) -> Expr) -> Expr {
    let (q, r) = (Expr::var("q", Sort::int()), Expr::var("r", Sort::int()));
    Expr::forall(
        vec![("q".to_string(), Sort::int())],
        Expr::exists(vec![("r".to_string(), Sort::int())], body(q, r)),
    )
}

/// THE CLOSED `∀∃` SHAPE UNDER `:produce-proofs`, through the lane trust
/// reads (`trust-router`'s `a_binder_survives_its_own_retained_source`, row
/// `nested-forall-exists`).
///
/// Truth first, from the formula alone: `∀q:Int. ∃r:Int. r > q` is TRUE
/// (take `r = q + 1`), so it is satisfiable and must come back with a model.
///
/// The QSAT route decides it `sat` and hands its witness to the SAT
/// emission, whose quantified model gate cannot confirm the alternation when
/// a certificate is demanded (the strategy route's checked ground refutation
/// of `¬(q < q + 1)` has no strict proof). The route used to end the query
/// there, `Unknown("incomplete")`, with the nested-CEGQI lane that decides it
/// stood down; without `:produce-proofs` the same program answered `sat`.
///
/// The control below is decided by the route's own `unsat`, so it never
/// reaches the refused-sat re-solve (`qsat_refused_sat_resolve`), and the
/// verdict alone would stay `sat` if the route stopped handing this `sat` to
/// the emission and the legacy lanes answered instead. So this test also
/// pins what that path records: the gate refused the route's `sat`, the
/// query was solved exactly once more, and the answer is a `sat` the
/// independent model gate confirmed (the re-solve resets the statistics, so
/// that is its own emission's result).
#[test]
fn closed_forall_exists_is_decided_through_the_native_bridge_under_produce_proofs() {
    for logic in ["LIA", "ALL"] {
        let program =
            closed_program_under_produce_proofs(logic, forall_exists_int(|q, r| r.int_gt(q)));
        let outcomes = crate::execute_direct::execute_incremental(&program).expect("must execute");
        assert!(
            matches!(outcomes[0].result, ExecuteTypedResult::Counterexample(_)),
            "`{logic}`: `∀q ∃r. r > q` is a true closed sentence, so it is satisfiable and \
             must come back as a counterexample under `:produce-proofs`; got: {:?}",
            outcomes[0].result
        );
        let stats = &outcomes[0]
            .solve_details
            .as_ref()
            .expect("a counterexample carries its solve details")
            .statistics;
        let publish = stats.get_string("qsat.publish");
        assert_eq!(
            publish,
            Some("sat-gate-refused"),
            "`{logic}`: the gate refused the route's `sat`"
        );
        assert_eq!(
            stats.get_int("qsat.refused_sat_resolves"),
            Some(1),
            "`{logic}`: the refused `sat` was solved once more"
        );
        assert_eq!(
            stats.get_string("model_check_gate.result"),
            Some("confirmed-sat"),
            "`{logic}`: the re-solve's `sat` passed the model gate (publish={publish:?})"
        );
    }
}

/// The CONTROL for the test above: `∀q:Int. ∃r:Int. r > q ∧ r < q` is FALSE
/// (take any `q`: no `r` is both above and below it), so it is unsatisfiable
/// and must be refuted. It keeps the closed `∀∃` row from being satisfied by
/// a lane that answers `sat` for every closed alternation.
#[test]
fn false_closed_forall_exists_is_refuted_through_the_native_bridge_under_produce_proofs() {
    for logic in ["LIA", "ALL"] {
        let control = closed_program_under_produce_proofs(
            logic,
            forall_exists_int(|q, r| r.clone().int_gt(q.clone()).and(r.int_lt(q))),
        );
        let outcomes = crate::execute_direct::execute_incremental(&control).expect("must execute");
        assert!(
            matches!(outcomes[0].result, ExecuteTypedResult::Verified),
            "`{logic}`: `∀q ∃r. r > q ∧ r < q` is a false closed sentence, so it is \
             unsatisfiable and must be refuted under `:produce-proofs`; got: {:?}",
            outcomes[0].result
        );
    }
}
