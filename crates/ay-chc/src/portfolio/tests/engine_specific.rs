// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::single_loop::SingleLoopTransformation;

#[test]
fn test_portfolio_tpa_only_unsafe() {
    use crate::tpa::TpaConfig;
    use std::time::Duration;

    let problem = create_unsafe_problem();
    let config = PortfolioConfig::tpa_only(TpaConfig {
        max_power: 10,
        timeout_per_power: Duration::from_secs(5),
        ..TpaConfig::default()
    });
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(_) => {
            // Expected: TPA finds counterexample in unsafe problem
        }
        PortfolioResult::Safe(_) => {
            panic!("Problem is unsafe, should not be safe");
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            // TPA may return Unknown due to validation rejection of spurious CEX
            // This is acceptable - TPA without strengthening may produce spurious results
        }
    }
}

#[test]
fn test_portfolio_tpa_only_safe() {
    use crate::tpa::TpaConfig;
    use std::time::Duration;

    let problem = create_safe_problem();
    let config = PortfolioConfig::tpa_only(TpaConfig {
        max_power: 10,
        timeout_per_power: Duration::from_secs(5),
        ..TpaConfig::default()
    });
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(_) => {
            // TPA proved safe - ideal outcome
        }
        PortfolioResult::Unsafe(_) => {
            panic!(
                "SOUNDNESS BUG: TPA returned Unsafe on a SAFE problem.\n\
                 TPA limitations may cause Unknown, but Unsafe is always wrong for safe problems."
            );
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            // Expected: TPA without strengthening cannot prove safe systems
        }
    }
}

#[test]
fn test_set_pdr_user_hints_applies_to_all_pdr_engines() {
    use crate::lemma_hints::LemmaHint;
    use crate::PredicateId;

    let mut config = PortfolioConfig::production_default();
    let hint = LemmaHint {
        predicate: PredicateId::new(0),
        formula: ChcExpr::Bool(true),
        source: "test",
        priority: 50,
    };

    config.set_pdr_user_hints(vec![hint]);

    // Verify all PDR engines got the hints
    for engine in &config.engines {
        if let EngineConfig::Pdr(pdr) = engine {
            assert_eq!(
                pdr.user_hints.len(),
                1,
                "each PDR engine should have exactly 1 hint"
            );
            assert_eq!(pdr.user_hints[0].source, "test", "hint source should match");
        }
    }
}

#[test]
fn test_portfolio_decomposition_engine() {
    let problem = create_multi_predicate_chain_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Decomposition(DecompositionConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            // Decomposition should find invariants for P1 and P2
            assert!(!model.is_empty(), "model should have invariants");
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            // Acceptable: decomposition might return NotApplicable which converts to Unknown
        }
        PortfolioResult::Unsafe(_) => {
            panic!("Multi-predicate chain problem is safe");
        }
    }
}

#[test]
fn test_trl_singleloop_unsafe_replay_confirms_or_stays_unknown() {
    // inc-9 (gate g3): SingleLoop TRL Unsafe is no longer suppressed
    // unconditionally. It is replay-confirmed by bounded BMC on the input
    // problem: on this genuinely-unsafe multipred problem the result is
    // either a verified witness-bearing Unsafe (replay confirmed) or
    // Unknown (replay out of budget) — NEVER Safe, and never a
    // witness-free Unsafe.
    let problem = create_multi_predicate_unsafe_problem();
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Trl(TrlConfig::default())],
        parallel: false,
        timeout: Some(Duration::from_secs(30)),
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(cex) => {
            assert!(
                cex.witness.as_ref().is_some_and(|w| !w.entries.is_empty()),
                "replay-confirmed SingleLoop Unsafe must carry a verified derivation witness"
            );
        }
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {}
        PortfolioResult::Safe(_) => {
            panic!("multi-predicate unsafe problem must never be Safe");
        }
    }
}

#[test]
fn test_trl_array_problem_returns_unknown_instead_of_panicking() {
    let problem = ChcParser::parse(include_str!(
        "../../../../../benchmarks/chc/array_bv_safe.smt2"
    ))
    .expect("array_bv_safe benchmark should parse");
    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Trl(TrlConfig::default())],
        parallel: false,
        timeout: None,
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
        matches!(result, PortfolioResult::Unknown | PortfolioResult::Safe(_)),
        "TRL must not panic on array-sorted CHC, got {result:?}"
    );
}

#[test]
fn test_trl_singleloop_safe_backtranslation_reverses_canonical_state_vars_before_validation() {
    let problem = create_multi_predicate_chain_problem();
    let predicates = problem.predicates();
    let p1 = predicates[0].id;
    let p2 = predicates[1].id;

    let mut tx = SingleLoopTransformation::new(problem.clone());
    let sys = tx.transform().expect("SingleLoop transform should succeed");
    let loc_p1 = sys
        ._location_vars
        .get(&p1)
        .expect("P1 location variable should exist")
        .clone();
    let loc_p2 = sys
        ._location_vars
        .get(&p2)
        .expect("P2 location variable should exist")
        .clone();
    let arg_p1 = sys
        ._arg_vars
        .get(&(p1, 0))
        .expect("P1 argument variable should exist")
        .clone();
    let arg_p2 = sys
        ._arg_vars
        .get(&(p2, 0))
        .expect("P2 argument variable should exist")
        .clone();

    // Safe state-space invariant over SingleLoop vars:
    //   P1 states require x = 0
    //   P2 states require x = 1
    // Location variables are Int-sorted (0=inactive, 1=active), so express
    // "inactive" as `loc == 0` rather than `not(loc)` (which is ill-typed).
    let state_space_inv = ChcExpr::and(
        ChcExpr::or(
            ChcExpr::eq(ChcExpr::var(loc_p1.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(arg_p1), ChcExpr::int(0)),
        ),
        ChcExpr::or(
            ChcExpr::eq(ChcExpr::var(loc_p2.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(arg_p2), ChcExpr::int(1)),
        ),
    );

    // Simulate TRL's returned synthetic model: vars/formula renamed to canonical
    // `__p0_a{i}` names, which the old adapter incorrectly fed straight into
    // SingleLoop back-translation.
    let canonical_vars: Vec<ChcVar> = sys
        .state_vars
        .iter()
        .enumerate()
        .map(|(i, var)| ChcVar::new(format!("__p{}_a{i}", p1.index()), var.sort.clone()))
        .collect();
    let to_canonical: Vec<(ChcVar, ChcExpr)> = sys
        .state_vars
        .iter()
        .cloned()
        .zip(canonical_vars.iter().cloned().map(ChcExpr::var))
        .collect();
    let canonical_formula = state_space_inv.substitute(&to_canonical);

    let mut synthetic_model = InvariantModel::new();
    synthetic_model.set(
        p1,
        PredicateInterpretation::new(canonical_vars, canonical_formula),
    );

    let translated =
        translate_trl_singleloop_safe_model(&problem, &tx, &sys.state_vars, &synthetic_model)
            .expect("adapter should recover the SingleLoop state-space invariant");

    let solver = PortfolioSolver::new(
        problem,
        PortfolioConfig {
            external_cancellation: None,
            engines: vec![EngineConfig::Trl(TrlConfig::default())],
            parallel: false,
            timeout: None,
            parallel_timeout: None,
            verbose: false,

            enable_preprocessing: false,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: None,
            strict_proofs: false,
        },
    );
    assert!(
        matches!(solver.validate_safe(&translated), ValidationResult::Valid),
        "recovered TRL SingleLoop invariant must validate on the original multi-predicate problem: {translated:?}",
    );
}
