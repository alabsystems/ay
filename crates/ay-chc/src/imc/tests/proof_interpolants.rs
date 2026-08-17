// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Rank-4 inc-3 keystone: with proof-derived interpolation FORCED ON, IMC
/// must produce the same verdict as the default cascade path (Safe here),
/// because every proof-derived interpolant is verified with the existing
/// Craig validation and any failure falls back to the cascade.
#[test]
fn test_imc_proof_interpolants_same_verdict_safe() {
    let build_problem = || {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let xp = ChcVar::new("xp", ChcSort::Int);

        // Init: xp >= 1 => Inv(xp)
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(xp.clone()), ChcExpr::int(1))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(xp.clone())]),
        ));
        // Step: Inv(x) ∧ xp >= 1 => Inv(xp)
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(xp.clone()), ChcExpr::int(1))),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(xp)]),
        ));
        // Bad: Inv(x) ∧ x <= 0 => false
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0))),
            ),
            ClauseHead::False,
        ));
        problem
    };

    let config_with = |proof_interpolants: Option<bool>| ImcConfig {
        base: ChcEngineConfig::default(),
        max_k: 3,
        max_iters_per_k: 10,
        query_timeout: Duration::from_secs(2),
        total_timeout: Duration::from_secs(20),
        proof_interpolants,
    };

    // Default path (cascade): Safe.
    let default_result = ImcSolver::new(build_problem(), config_with(Some(false))).solve();
    assert!(
        matches!(default_result, ImcResult::Safe(_)),
        "cascade path must prove Safe, got {default_result:?}"
    );

    // Proof path FORCED ON: identical verdict (proof-derived interpolants are
    // verified-or-fall-back, so the verdict class cannot change).
    let proof_result = ImcSolver::new(build_problem(), config_with(Some(true))).solve();
    assert!(
        matches!(proof_result, ImcResult::Safe(_)),
        "proof-interpolant path must preserve the Safe verdict, got {proof_result:?}"
    );
}

/// Rank-4 inc-3: forcing the proof path on an UNSAFE problem must preserve
/// the Unsafe verdict (interpolation only runs on UNSAT bounded checks; the
/// counterexample path is untouched).
#[test]
fn test_imc_proof_interpolants_same_verdict_unsafe() {
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
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    let solver = ImcSolver::new(
        problem,
        ImcConfig {
            base: ChcEngineConfig::default(),
            max_k: 10,
            max_iters_per_k: 100,
            query_timeout: Duration::from_secs(2),
            total_timeout: Duration::from_secs(20),
            proof_interpolants: Some(true),
        },
    );
    let result = solver.solve();
    assert!(
        matches!(&result, ImcResult::Unsafe(cex) if cex.steps.len() == 3),
        "proof-interpolant path must preserve the Unsafe verdict, got {result:?}"
    );
}
