// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #6293: empty counterexamples must be checked against the
/// original problem instead of being rejected blindly when BV confirmation is active.
#[test]
fn test_bv_trivial_cex_validates_against_original_problem_6293() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    // Init: x = 0 => inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Safety: inv(x) /\ x = 0 => false (trivially violated by init)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::False,
    ));

    // Use enable_preprocessing: false to bypass BvToBool (which would
    // eliminate BV sorts and clear bv_abstracted). This tests the raw
    // BV-to-Int abstraction guard.
    let config = PortfolioConfig {
        external_cancellation: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        strict_proofs: false,
        ..PortfolioConfig::test_default()
    };
    let solver = PortfolioSolver::new(problem, config);

    // The bv_abstracted flag should be true since preprocessing is off
    // and the problem has BV sorts
    assert!(
        solver.bv_abstracted,
        "Problem with BV sorts (no preprocessing) should set bv_abstracted"
    );

    // Create a trivial counterexample (like PDR would generate for init-violates-safety)
    let trivial_cex = Counterexample {
        steps: Vec::new(),
        witness: None,
        ground_derivation: None,
    };

    // validate_unsafe should confirm this against the original BV problem.
    let result = solver.validate_unsafe(&trivial_cex);
    assert!(
        matches!(result, ValidationResult::Valid),
        "Trivial CEX should validate against the original BV problem, got: {result:?}"
    );
}

fn create_bv_init_unsafe_problem_6289() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_sequential_portfolio_confirms_bv_unsafe_6293() {
    let problem = create_bv_init_unsafe_problem_6289();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_secs(2)),
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "Sequential portfolio must confirm genuine BV Unsafe results, got: {result:?}"
    );
}

#[test]
fn test_parallel_portfolio_confirms_bv_unsafe_6293() {
    let problem = create_bv_init_unsafe_problem_6289();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::with_engine_config(2, false, None)),
        ],
        parallel: true,
        timeout: Some(Duration::from_secs(2)),
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "Parallel portfolio must confirm genuine BV Unsafe results, got: {result:?}"
    );
}

/// Mixed Int+BV predicate: the per-argument sort check in validate_unsafe
/// must not reject witnesses where the Int argument legitimately has
/// SmtValue::Int after concretization. Before #6293 fix, a predicate-wide
/// `has_bv_args` audit would reject the legitimate Int(0) witness for the
/// first (Int-sorted) argument with "BV-to-Int counterexample has Int-domain
/// values for BV-sorted predicate arguments (spurious)".
#[test]
fn test_validate_unsafe_accepts_mixed_int_and_bv_witness_6293() {
    use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
    use crate::smt::SmtValue;

    // Problem with mixed (Int, BitVec(8)) predicate.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::BitVec(8)]);
    let n = ChcVar::new("n", ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(n.clone()), ChcExpr::var(x.clone())]),
    ));

    // Safety: inv(n, x) /\ x = 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(n), ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::False,
    ));

    let config = PortfolioConfig {
        external_cancellation: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        strict_proofs: false,
        ..PortfolioConfig::test_default()
    };
    let solver = PortfolioSolver::new(problem, config);

    assert!(
        solver.bv_abstracted,
        "Mixed Int+BV problem should set bv_abstracted"
    );

    // Create a witness where the Int arg has SmtValue::Int (legitimate)
    // and the BV arg has SmtValue::BitVec (already concretized)
    let canonical_int = format!("__p{}_a0", inv.index());
    let canonical_bv = format!("__p{}_a1", inv.index());
    let mut instances = FxHashMap::default();
    instances.insert(canonical_int, SmtValue::Int(0));
    instances.insert(canonical_bv, SmtValue::BitVec(0, 8));

    let cex = Counterexample::with_witness(
        Vec::new(),
        DerivationWitness {
            query_clause: None,
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: inv,
                level: 0,
                state: ChcExpr::Bool(true),
                incoming_clause: None,
                premises: Vec::new(),
                instances,
            }],
        },
    );

    let result = solver.validate_unsafe(&cex);
    // The critical assertion: a mixed Int+BV witness must NOT be rejected
    // by the sort-mismatch defense-in-depth check. That check would produce
    // an error containing "Int-domain values for BV-sorted predicate arguments".
    // Any other validation outcome (Valid or Invalid for a different reason)
    // proves the per-argument sort check works correctly.
    if let ValidationResult::Invalid(reason) = &result {
        assert!(
            !reason.contains("Int-domain values for BV-sorted"),
            "Mixed Int+BV witness was incorrectly rejected by sort check: {reason}"
        );
    }
}
