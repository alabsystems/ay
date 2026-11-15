// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

const ENGINE_TYPES: [EngineType; 11] = [
    EngineType::Pdr,
    EngineType::Bmc,
    EngineType::Pdkind,
    EngineType::Tpa,
    EngineType::Trl,
    EngineType::Kind,
    EngineType::Decomposition,
    EngineType::Imc,
    EngineType::Lawi,
    EngineType::Dar,
    EngineType::Cegar,
];

fn engine_counts(portfolio: &PortfolioConfig) -> [usize; 11] {
    ENGINE_TYPES.map(|engine_type| {
        portfolio
            .engines
            .iter()
            .filter(|engine| engine.engine_type() == engine_type)
            .count()
    })
}

/// Fix C (8cd8c6474): a cyclic array multi-predicate problem gets the
/// Unsafe-only BMC lane (max_depth 30, `acyclic_safe` false) in the
/// multi-pred lineup. heap__swaparray_000 is the instance that lane was added
/// for; its end-to-end test now lands before the portfolio is built, so this
/// pins the lineup entry directly.
#[test]
fn multi_pred_lineup_keeps_fix_c_unsafe_only_bmc_for_cyclic_arrays() {
    let problem = ChcParser::parse(include_str!(
        "../../tests/fixtures/chc_comp/llreve/heap__swaparray_000.smt2"
    ))
    .expect("parse heap__swaparray_000");
    let features = ProblemClassifier::classify(&problem);
    assert!(features.uses_arrays && features.has_cycles);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let config = adaptive.multi_pred_linear_portfolio_config(
        PdrConfig::default(),
        PdrConfig::portfolio_variant_with_splits(),
        &features,
    );
    assert!(
        config.engines.iter().any(|engine| matches!(
            engine,
            EngineConfig::Bmc(bmc) if bmc.max_depth == 30 && !bmc.acyclic_safe
        )),
        "the cyclic-array multi-pred lineup must keep Fix C's Unsafe-only BMC lane"
    );
}

fn sorted_engine_fingerprints(portfolio: &PortfolioConfig) -> Vec<String> {
    let mut fingerprints = portfolio
        .engines
        .iter()
        .map(|engine| format!("{engine:?}"))
        .collect::<Vec<_>>();
    fingerprints.sort();
    fingerprints
}

#[test]
fn feature_selection_prioritizes_scalar_bv_without_dropping_fallbacks() {
    let solver = AdaptivePortfolio::new(
        create_identity_simple_loop(ChcSort::BitVec(8)),
        AdaptiveConfig::with_budget(Duration::from_secs(30), false).with_max_engines(None),
    );
    let mut portfolio = PortfolioConfig::production_default();
    let original_len = portfolio.engines.len();
    let original_counts = engine_counts(&portfolio);
    let original_fingerprints = sorted_engine_fingerprints(&portfolio);

    solver.apply_original_problem_engine_selection(&mut portfolio);

    assert_eq!(portfolio.engines.len(), original_len);
    assert_eq!(
        portfolio
            .engines
            .iter()
            .take(3)
            .map(EngineConfig::engine_type)
            .collect::<Vec<_>>(),
        vec![EngineType::Pdr, EngineType::Bmc, EngineType::Kind],
        "the scalar-BV selector should own the first capacity slots"
    );
    assert!(
        portfolio
            .engines
            .iter()
            .enumerate()
            .filter(|(_, engine)| engine.engine_type() == EngineType::Pdr)
            .nth(1)
            .is_some_and(|(position, _)| position >= 3),
        "one selected PDR must not pull every PDR variant ahead of complementary lanes"
    );
    assert_eq!(
        engine_counts(&portfolio),
        original_counts,
        "W4-2C is scheduling-only and must retain every fallback lane"
    );
    assert_eq!(
        sorted_engine_fingerprints(&portfolio),
        original_fingerprints
    );
}

#[test]
fn feature_selection_preserves_full_tuned_simple_loop_configs() {
    let solver = AdaptivePortfolio::new(
        create_simple_loop(),
        AdaptiveConfig::with_budget(Duration::from_secs(30), false).with_max_engines(None),
    );
    let mut portfolio = solver.simple_loop_portfolio_config(Duration::from_secs(30));
    let before = sorted_engine_fingerprints(&portfolio);

    solver.apply_original_problem_engine_selection(&mut portfolio);

    assert_eq!(
        sorted_engine_fingerprints(&portfolio),
        before,
        "selector priority must preserve every tuned route configuration"
    );
}

#[test]
fn feature_selection_preserves_array_pdr_variants_and_caller_precedence() {
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8)));
    let solver = AdaptivePortfolio::new(
        create_identity_simple_loop(array_sort),
        AdaptiveConfig::with_budget(Duration::from_secs(30), false)
            .with_preferred_engine_order(vec![EngineType::Imc])
            .with_max_engines(Some(1)),
    );
    let mut portfolio = solver.simple_loop_array_portfolio_config(Duration::from_secs(30));
    let original_len = portfolio.engines.len();

    solver.apply_original_problem_engine_selection(&mut portfolio);

    assert_eq!(portfolio.engines.len(), original_len);
    assert_eq!(
        portfolio
            .engines
            .iter()
            .map(EngineConfig::engine_type)
            .collect::<Vec<_>>(),
        vec![
            EngineType::Pdr,
            EngineType::Pdr,
            EngineType::Lawi,
            EngineType::Bmc,
            EngineType::Imc,
        ],
        "BvArrays should use the array selector while retaining unmatched IMC"
    );
    let pdr_variants = portfolio
        .engines
        .iter()
        .filter_map(|engine| match engine {
            EngineConfig::Pdr(pdr) => Some(pdr.use_negated_equality_splits),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(pdr_variants, vec![false, true]);

    solver.prepare_portfolio_config(&mut portfolio, StagedProbeBudgetProfile::BmcOnly);
    assert!(matches!(
        portfolio.engines.as_slice(),
        [EngineConfig::Imc(_)]
    ));
}

#[test]
fn feature_selection_cannot_undo_datatype_guards() {
    let solver = AdaptivePortfolio::new(
        create_identity_simple_loop(solidity_route_balance_sort()),
        AdaptiveConfig::with_budget(Duration::from_secs(30), false).with_max_engines(None),
    );
    let selected = EngineSelector::select(&ChcFeatureExtractor::extract(&solver.problem));
    assert!(
        selected
            .engines
            .iter()
            .any(|engine| matches!(engine, EngineConfig::Kind(_))),
        "the scalar DT+BV selector should request Kind before route guards"
    );
    let mut portfolio = PortfolioConfig::production_default();
    portfolio.apply_dt_guards(0);
    let guarded_len = portfolio.engines.len();

    solver.apply_original_problem_engine_selection(&mut portfolio);

    assert_eq!(portfolio.engines.len(), guarded_len);
    assert!(portfolio
        .engines
        .iter()
        .all(|engine| !matches!(engine, EngineConfig::Kind(_))));
    assert!(portfolio.engines.iter().all(|engine| match engine {
        EngineConfig::Pdr(pdr) => pdr.max_escalation_level == 0,
        _ => true,
    }));
}

#[test]
fn feature_selected_primary_loses_stale_staged_probe_cap() {
    let solver = AdaptivePortfolio::new(
        create_body_equality_counter_loop(),
        AdaptiveConfig::with_budget(Duration::from_secs(120), false).with_max_engines(None),
    );
    let mut portfolio = solver.make_default_portfolio_config();
    assert_eq!(
        portfolio.budget_policy(EngineType::Kind),
        BudgetPolicy::Fixed(Duration::from_secs(3))
    );

    solver.apply_original_problem_engine_selection(&mut portfolio);
    assert!(matches!(
        portfolio.engines.first(),
        Some(EngineConfig::Kind(_))
    ));
    solver.prepare_portfolio_config(&mut portfolio, StagedProbeBudgetProfile::BmcAndKind);

    assert_eq!(
        portfolio.budget_policy(EngineType::Kind),
        BudgetPolicy::Default,
        "a selector-promoted primary must receive the full fair wave, not a stale probe cap"
    );
}
