// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::PredicateInterpretation;
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioSolver, ValidationResult};
use crate::single_loop::SingleLoopTransformation;
use crate::tpa::TpaConfig;
use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

/// Create a two-predicate safe chain:
///   x = 0 => P1(x)
///   P1(x - 1) => P2(x)
///   P2(x) /\ x > 10 => false
fn create_multi_predicate_chain_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
    let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            p1,
            vec![ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        )]),
        ClauseHead::Predicate(p2, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p2, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_tpa_singleloop_safe_translation_validates_original_problem() {
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

    let state_space_inv = ChcExpr::and(
        ChcExpr::or(
            ChcExpr::eq(ChcExpr::var(loc_p1), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(arg_p1), ChcExpr::int(0)),
        ),
        ChcExpr::or(
            ChcExpr::eq(ChcExpr::var(loc_p2), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(arg_p2), ChcExpr::int(1)),
        ),
    );

    let canonical_vars: Vec<ChcVar> = sys
        .state_vars
        .iter()
        .enumerate()
        .map(|(i, var)| ChcVar::new(format!("v{i}"), var.sort.clone()))
        .collect();
    let to_canonical: Vec<(ChcVar, ChcExpr)> = sys
        .state_vars
        .iter()
        .cloned()
        .zip(canonical_vars.iter().cloned().map(ChcExpr::var))
        .collect();
    let canonical_formula = state_space_inv.substitute(&to_canonical);

    let witness = SingleLoopSafeWitness::from_tpa(&canonical_formula, &sys.state_vars);
    let translated = translate_singleloop_safe(&problem, &tx, &witness)
        .expect("TPA witness should translate to a validating multi-predicate model");

    let solver = PortfolioSolver::new(
        problem,
        PortfolioConfig {
            external_cancellation: None,
            engines: vec![EngineConfig::Tpa(TpaConfig::default())],
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
        "TPA-style SingleLoop invariant must validate on the original multi-predicate problem: {translated:?}",
    );
}

#[test]
fn test_from_trl_reverses_remapped_state_space_formula() {
    let problem = create_multi_predicate_chain_problem();
    let p1 = problem.predicates()[0].id;

    let mut tx = SingleLoopTransformation::new(problem);
    let sys = tx.transform().expect("SingleLoop transform should succeed");

    let loc_p1 = sys
        ._location_vars
        .get(&p1)
        .expect("P1 location variable should exist")
        .clone();
    let arg_p1 = sys
        ._arg_vars
        .get(&(p1, 0))
        .expect("P1 argument variable should exist")
        .clone();

    let state_space_inv = ChcExpr::or(
        ChcExpr::eq(ChcExpr::var(loc_p1), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(arg_p1), ChcExpr::int(0)),
    );

    let remapped_vars: Vec<ChcVar> = sys
        .state_vars
        .iter()
        .enumerate()
        .map(|(i, var)| ChcVar::new(format!("__p{}_a{i}", p1.index()), var.sort.clone()))
        .collect();
    let to_remapped: Vec<(ChcVar, ChcExpr)> = sys
        .state_vars
        .iter()
        .cloned()
        .zip(remapped_vars.iter().cloned().map(ChcExpr::var))
        .collect();
    let remapped_formula = state_space_inv.substitute(&to_remapped);

    let mut model = InvariantModel::new();
    model.set(
        p1,
        PredicateInterpretation::new(remapped_vars, remapped_formula),
    );

    let witness = SingleLoopSafeWitness::from_trl(&model, &sys.state_vars)
        .expect("TRL compatibility constructor should recover the state-space witness");

    assert_eq!(
        witness.formula.simplify_constants(),
        state_space_inv.simplify_constants(),
        "TRL compatibility constructor must reverse remapped vars back to the state-space formula",
    );
}

#[test]
fn test_from_trl_accepts_state_space_named_vars() {
    let problem = create_multi_predicate_chain_problem();
    let p1 = problem.predicates()[0].id;

    let mut tx = SingleLoopTransformation::new(problem);
    let sys = tx.transform().expect("SingleLoop transform should succeed");

    let loc_p1 = sys
        ._location_vars
        .get(&p1)
        .expect("P1 location variable should exist")
        .clone();
    let arg_p1 = sys
        ._arg_vars
        .get(&(p1, 0))
        .expect("P1 argument variable should exist")
        .clone();

    let state_space_inv = ChcExpr::or(
        ChcExpr::eq(ChcExpr::var(loc_p1), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(arg_p1), ChcExpr::int(0)),
    );

    let mut model = InvariantModel::new();
    model.set(
        p1,
        PredicateInterpretation::new(sys.state_vars.clone(), state_space_inv.clone()),
    );

    let witness = SingleLoopSafeWitness::from_trl(&model, &sys.state_vars)
        .expect("TRL compatibility constructor should preserve state-space vars directly");

    assert_eq!(
        witness.formula.simplify_constants(),
        state_space_inv.simplify_constants(),
        "TRL compatibility constructor must preserve a state-space-form witness",
    );
}

#[test]
fn test_from_trl_rejects_sort_mismatch_against_state_space() {
    let problem = create_multi_predicate_chain_problem();
    let p1 = problem.predicates()[0].id;

    let mut tx = SingleLoopTransformation::new(problem);
    let sys = tx.transform().expect("SingleLoop transform should succeed");

    let mut bad_vars = sys.state_vars.clone();
    bad_vars[0] = ChcVar::new("bad0", ChcSort::Bool);

    let mut model = InvariantModel::new();
    model.set(
        p1,
        PredicateInterpretation::new(bad_vars, ChcExpr::Bool(true)),
    );

    assert!(
        SingleLoopSafeWitness::from_trl(&model, &sys.state_vars).is_none(),
        "sort mismatches must fail closed before SingleLoop back-translation",
    );
}

#[test]
fn test_from_trl_rejects_formula_vars_outside_binders() {
    let problem = create_multi_predicate_chain_problem();
    let p1 = problem.predicates()[0].id;

    let mut tx = SingleLoopTransformation::new(problem);
    let sys = tx.transform().expect("SingleLoop transform should succeed");

    let alien = ChcVar::new("A", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        p1,
        PredicateInterpretation::new(
            sys.state_vars.clone(),
            ChcExpr::ge(ChcExpr::var(alien), ChcExpr::int(0)),
        ),
    );

    assert!(
        SingleLoopSafeWitness::from_trl(&model, &sys.state_vars).is_none(),
        "TRL SingleLoop witnesses with unbound formula variables must fail closed",
    );
}

#[test]
fn test_build_multi_pred_model_rejects_unclosed_interpretation() {
    let problem = create_multi_predicate_chain_problem();
    let p1 = problem.predicates()[0].id;

    let alien = ChcVar::new("A", ChcSort::Int);
    let mut interps = FxHashMap::default();
    interps.insert(p1, ChcExpr::ge(ChcExpr::var(alien), ChcExpr::int(0)));

    assert!(
        build_multi_pred_model(&problem, &interps).is_none(),
        "SingleLoop adapter must not export interpretations with variables outside binders",
    );
}
