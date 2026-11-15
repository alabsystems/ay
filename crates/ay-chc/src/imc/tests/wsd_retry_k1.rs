// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Workstream D, WP-D1-E (DESIGN_lra_interp_tpa.md §4.1): IMC's budget-shaped
//! base-check retry and its k→1 witness step.

use super::*;

/// Golem `test_IMC_simple` / `test_IMC_simple_safe`: x' = 0; x' = x + 1;
/// bad = x > 1 (unsafe) or x < 0 (safe).
fn counter_problem(unsafe_bound: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let s1 = problem.declare_predicate("s1", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xp = ChcVar::new("xp", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(xp.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp)]),
    ));
    let bad = if unsafe_bound {
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(1))
    } else {
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0))
    };
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(s1, vec![ChcExpr::var(x)])], Some(bad)),
        ClauseHead::False,
    ));
    problem
}

/// x' = 0; x' = 1 - x; bad = x > 1. `x <= 1` is 2-inductive but not
/// 1-inductive (x = -5 steps to 6); `0 <= x <= 1` is 1-inductive.
fn flip_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let s1 = problem.declare_predicate("s1", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xp = ChcVar::new("xp", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(xp.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::sub(ChcExpr::int(1), ChcExpr::var(x.clone())),
            )),
        ),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn config() -> ImcConfig {
    ImcConfig {
        base: ChcEngineConfig::default(),
        max_k: 10,
        max_iters_per_k: 100,
        query_timeout: Duration::from_secs(2),
        total_timeout: Duration::from_secs(20),
        proof_interpolants: Some(false),
    }
}

fn solve_with_forced_base_unknowns(problem: ChcProblem, count: usize, permille: u32) -> ImcResult {
    TEST_FORCE_BASE_UNKNOWN.with(|cell| cell.set((count, permille)));
    let result = ImcSolver::new(problem, config()).solve();
    TEST_FORCE_BASE_UNKNOWN.with(|cell| cell.set((0, 0)));
    result
}

/// A budget-shaped base-check `Unknown` is retried once and the run ends with
/// the verdict the undisturbed run reaches: the retry re-asks the same query,
/// so it never flips an answer (Safe and Unsafe systems).
#[test]
fn budget_shaped_base_unknown_is_retried_and_never_flips_the_verdict() {
    for unsafe_bound in [true, false] {
        let baseline = ImcSolver::new(counter_problem(unsafe_bound), config()).solve();
        let retried = solve_with_forced_base_unknowns(counter_problem(unsafe_bound), 1, 1000);
        assert_eq!(
            std::mem::discriminant(&baseline),
            std::mem::discriminant(&retried),
            "retry changed the verdict class (unsafe_bound={unsafe_bound}): {baseline:?} vs {retried:?}"
        );
        if unsafe_bound {
            assert!(matches!(retried, ImcResult::Unsafe(_)), "{retried:?}");
        } else {
            assert!(matches!(retried, ImcResult::Safe(_)), "{retried:?}");
        }
    }
}

/// A base-check `Unknown` that returned early (well under the cap) is not
/// budget-shaped: IMC exits `Unknown` exactly as before, without a retry.
#[test]
fn early_base_unknown_exits_without_retry() {
    let result = solve_with_forced_base_unknowns(counter_problem(true), 1, 100);
    assert!(matches!(result, ImcResult::Unknown), "{result:?}");
}

/// The flip system over Reals (the k→1 converter is wired for Real state
/// only, D-6 / INV-8): x' = 0.0; x' = 1 - x; bad = x > 1.
fn flip_problem_real() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let s1 = problem.declare_predicate("s1", vec![ChcSort::Real]);
    let x = ChcVar::new("x", ChcSort::Real);
    let xp = ChcVar::new("xp", ChcSort::Real);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(xp.clone()), ChcExpr::Real(0, 1))),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::sub(ChcExpr::Real(1, 1), ChcExpr::var(x.clone())),
            )),
        ),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::Real(1, 1))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn flip_ts_real() -> (ImcSolver, TransitionSystem, ChcVar) {
    let problem = flip_problem_real();
    let ts = TransitionSystem::from_chc_problem(&problem).expect("transition system");
    let x = ts.state_vars()[0].clone();
    (ImcSolver::new(problem, config()), ts, x)
}

fn flip_ts() -> (ImcSolver, TransitionSystem, ChcVar) {
    let problem = flip_problem();
    let ts = TransitionSystem::from_chc_problem(&problem).expect("transition system");
    let x = ts.state_vars()[0].clone();
    (ImcSolver::new(problem, config()), ts, x)
}

fn zero_to_one(x: &ChcVar) -> ChcExpr {
    ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    )
}

/// A fixpoint whose candidate fails 1-inductiveness is completed by the k→1
/// converter; its (self-validated) result becomes the Safe model (without a
/// conversion the same candidate is refused, see the next test).
#[test]
fn non_inductive_candidate_is_completed_by_the_k_to_1_converter() {
    let (solver, ts, x) = flip_ts();
    let two_inductive = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(1));
    assert_eq!(
        validate_inductive_invariant(&ts, &two_inductive, |q| {
            check_sat_with_timeout(q, Duration::from_secs(2))
        }),
        Some("inductiveness"),
        "fixture: x <= 1 must fail only 1-inductiveness"
    );
    let convert: TestKTo1Converter = |_, k, ts| {
        assert_eq!(k, 2);
        Some(zero_to_one(&ts.state_vars()[0]))
    };
    TEST_K_TO_1_CONVERTER.with(|cell| cell.set(Some(convert)));
    let result = solver.build_safe_result(
        &ts,
        &two_inductive,
        2,
        Instant::now(),
        Duration::from_secs(20),
    );
    TEST_K_TO_1_CONVERTER.with(|cell| cell.set(None));
    assert!(
        matches!(result, ImcResult::Safe(_)),
        "expected Safe from the converted invariant, got {result:?}"
    );
}

/// Without a conversion the non-inductive candidate is refused (Unknown), as
/// before the k→1 step existed.
#[test]
fn non_inductive_candidate_without_conversion_is_unknown() {
    let (solver, ts, x) = flip_ts();
    let two_inductive = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(1));
    let refuse: TestKTo1Converter = |_, _, _| None;
    TEST_K_TO_1_CONVERTER.with(|cell| cell.set(Some(refuse)));
    let result = solver.build_safe_result(
        &ts,
        &two_inductive,
        2,
        Instant::now(),
        Duration::from_secs(20),
    );
    TEST_K_TO_1_CONVERTER.with(|cell| cell.set(None));
    assert!(matches!(result, ImcResult::Unknown), "{result:?}");
}

/// The k→1 converter is consulted only when the candidate fails the
/// `inductiveness` leg: `C ⇒ inv` alone says nothing about the query, and a
/// failed `init` leg cannot be repaired by any `C` with `init ⇒ C ⇒ inv`.
/// Here `reached = x >= 1` is strengthened to `x >= 1 ∧ ¬(x > 1)`, which
/// fails `init ⇒ inv` (init is x = 0): the answer stays Unknown and the
/// converter is never called.
#[test]
fn k_to_1_converter_is_not_consulted_on_a_non_inductiveness_leg() {
    let (solver, ts, x) = flip_ts();
    let reached = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1));
    let never: TestKTo1Converter = |_, _, _| {
        panic!("k->1 converter consulted on a non-inductiveness leg");
    };
    TEST_K_TO_1_CONVERTER.with(|cell| cell.set(Some(never)));
    let result =
        solver.build_safe_result(&ts, &reached, 2, Instant::now(), Duration::from_secs(20));
    TEST_K_TO_1_CONVERTER.with(|cell| cell.set(None));
    assert!(matches!(result, ImcResult::Unknown), "{result:?}");
}

/// End to end with WP-D1-P's `convert_path` (C-P1) on the Real flip system:
/// the 2-inductive `x <= 1` is turned into a 1-inductive invariant and IMC
/// answers Safe.
#[test]
fn two_inductive_candidate_is_converted_by_convert_path() {
    let (solver, ts, x) = flip_ts_real();
    let two_inductive = ChcExpr::le(ChcExpr::var(x), ChcExpr::Real(1, 1));
    let result = solver.build_safe_result(
        &ts,
        &two_inductive,
        2,
        Instant::now(),
        Duration::from_secs(20),
    );
    assert!(matches!(result, ImcResult::Safe(_)), "{result:?}");
}
