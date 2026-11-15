// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;
use crate::ground_derivation::{validate_ground_derivation, GroundDerivationError};
use crate::smt::executor_adapter::install_observed_uf_application_values;
use crate::ClauseBody;
use std::time::Duration;

#[derive(Clone, Copy)]
enum UfArity {
    Unary,
    Nullary,
}

#[derive(Clone, Copy)]
enum QueryEquality {
    Equal,
    Different,
}

struct UfCase {
    solver: BmcSolver,
    pred: PredicateId,
    symbol: String,
    arity: UfArity,
}

fn uf_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(8)))
}

fn uf_value(value: u128) -> SmtValue {
    SmtValue::bitvec_from_u128(value, 8)
}

fn uf_application(symbol: &str, arity: UfArity, argument: ChcExpr) -> ChcExpr {
    let args = match arity {
        UfArity::Unary => vec![Arc::new(argument)],
        UfArity::Nullary => Vec::new(),
    };
    ChcExpr::FuncApp(symbol.to_owned(), ChcSort::BitVec(8), args)
}

fn uf_case(symbol: &str, arity: UfArity, equality: QueryEquality) -> UfCase {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("UfState", vec![ChcSort::BitVec(8); 2]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            uf_var("y"),
            uf_application(symbol, arity, uf_var("x")),
        )),
        ClauseHead::Predicate(pred, vec![uf_var("x"), uf_var("y")]),
    ));
    let relation = ChcExpr::eq(uf_var("b"), uf_application(symbol, arity, uf_var("a")));
    let relation = match equality {
        QueryEquality::Equal => relation,
        QueryEquality::Different => ChcExpr::not(relation),
    };
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(pred, vec![uf_var("a"), uf_var("b")])],
        Some(ChcExpr::and(
            ChcExpr::eq(uf_var("a"), ChcExpr::BitVec(1, 8)),
            relation,
        )),
    )));
    UfCase {
        solver: BmcSolver::new(problem, BmcConfig::default()),
        pred,
        symbol: symbol.to_owned(),
        arity,
    }
}

fn uf_deadline() -> ay_core::time::Instant {
    ay_core::time::Instant::now() + Duration::from_secs(30)
}

fn bind_generated(model: &mut FxHashMap<String, SmtValue>, expression: ChcExpr, value: SmtValue) {
    let ChcExpr::Var(ref variable) = expression else {
        panic!("polynomial variable fixture");
    };
    model.insert(variable.name.clone(), value);
}

fn uf_formula_and_model(
    case: &UfCase,
    names: &mut AcyclicNames<'_>,
) -> (ChcExpr, FxHashMap<String, SmtValue>) {
    let solver = &case.solver;
    let clauses = solver.problem.clauses();
    let mut conjuncts = Vec::new();
    let mut squares = 0;
    let mut simplified = 0;
    solver
        .compile_acyclic_dag_definition(
            case.pred,
            &solver.defs_by_head(),
            &FxHashMap::default(),
            &FxHashMap::default(),
            &mut squares,
            &mut simplified,
            &mut conjuncts,
            uf_deadline(),
            names,
        )
        .unwrap();
    conjuncts.push(
        solver
            .compile_acyclic_dag_query(
                &clauses[1],
                0,
                &FxHashMap::default(),
                &FxHashMap::default(),
                &mut squares,
                &mut simplified,
                uf_deadline(),
                names,
            )
            .unwrap(),
    );
    let mut model = FxHashMap::default();
    bind_generated(
        &mut model,
        solver.dag_predicate(case.pred, names).unwrap(),
        SmtValue::Bool(true),
    );
    bind_generated(
        &mut model,
        solver.dag_rule_indicator(case.pred, 0, names).unwrap(),
        SmtValue::Bool(true),
    );
    for (index, value) in [1, 7].into_iter().enumerate() {
        bind_generated(
            &mut model,
            solver.dag_arg(case.pred, index, names).unwrap(),
            uf_value(value),
        );
    }
    let fact = solver
        .mk_dag_clause_vars(&clauses[0], case.pred, 0, names)
        .unwrap();
    let query = solver.mk_dag_query_vars(&clauses[1], 0, names).unwrap();
    for (substitution, bindings) in [
        (&fact, [("x", 1), ("y", 7)]),
        (&query, [("a", 1), ("b", 7)]),
    ] {
        for (source, value) in bindings {
            bind_generated(&mut model, substitution[source].clone(), uf_value(value));
        }
    }
    let observed = [
        (
            uf_application(&case.symbol, case.arity, fact["x"].clone()),
            uf_value(7),
        ),
        (
            uf_application(&case.symbol, case.arity, query["a"].clone()),
            uf_value(7),
        ),
    ];
    assert!(install_observed_uf_application_values(
        &mut model, &observed
    ));
    (ChcExpr::and_all(conjuncts), model)
}

fn uf_candidate(
    case: &UfCase,
    model: &FxHashMap<String, SmtValue>,
    names: &mut AcyclicNames<'_>,
) -> DerivationWitness {
    case.solver
        .acyclic_dag_model_derivation_witness(
            model,
            &[&case.solver.problem.clauses()[1]],
            &case.solver.defs_by_head(),
            &FxHashMap::default(),
            names,
        )
        .expect("BV8 predicate and clause values remain typed")
}

fn uf_ground(
    case: &UfCase,
    witness: &DerivationWitness,
    model: &FxHashMap<String, SmtValue>,
    names: &mut AcyclicNames<'_>,
) -> Option<GroundDerivation> {
    case.solver.ground_derivation_from_polynomial_witness(
        witness,
        model,
        &[&case.solver.problem.clauses()[1]],
        names,
        uf_deadline(),
    )
}

#[test]
fn unary_and_nullary_uf_models_replay_original_clauses_and_v2_without_solver() {
    for arity in [UfArity::Unary, UfArity::Nullary] {
        // P(x,y) <- y=f(x); false <- P(a,b), a=1, b=f(a).
        // Every total f admits this derivation; choosing f(1)=7 is not a
        // restriction that changes an otherwise safe source into an unsafe one.
        let case = uf_case("f", arity, QueryEquality::Equal);
        let mut live = || true;
        let mut names = AcyclicNames::new(&case.solver.problem, &mut live).unwrap();
        let (formula, model) = uf_formula_and_model(&case, &mut names);
        assert_eq!(evaluate_expr(&formula, &model), Some(SmtValue::Bool(true)));
        let witness = uf_candidate(&case, &model, &mut names);
        let ground = uf_ground(&case, &witness, &model, &mut names).unwrap();
        assert_eq!(ground.steps[0].env["x"], uf_value(1));
        assert_eq!(ground.steps[0].env["y"], uf_value(7));
        assert_eq!(ground.steps[1].env["a"], uf_value(1));
        assert_eq!(ground.steps[1].env["b"], uf_value(7));
        assert_eq!(ground.steps[1].premises, vec![0]);
        assert_eq!(
            validate_ground_derivation(&case.solver.problem, &ground),
            Ok(())
        );
        let counterexample =
            Counterexample::with_witness(Vec::new(), witness).with_ground_derivation(ground);
        let artifact = counterexample
            .ground_derivation_artifact_v2(&case.solver.problem)
            .expect("source-authenticated UF evidence uses existing public V2 API");
        let checked = crate::validate_chc_ground_derivation_artifact_v2(
            &case.solver.problem,
            artifact.bytes(),
        )
        .unwrap();
        assert_eq!(checked.step_count(), 2);
        assert_eq!(checked.uf_observation_count(), 2);
        assert!(!String::from_utf8_lossy(artifact.bytes()).contains("\\u0000ay.uf-"));
        assert!(counterexample
            .ground_derivation_artifact(&case.solver.problem)
            .is_err());
    }
}

#[test]
fn opposite_query_cannot_replay_a_congruent_uf_candidate() {
    let case = uf_case("f", UfArity::Unary, QueryEquality::Different);
    let mut live = || true;
    let mut names = AcyclicNames::new(&case.solver.problem, &mut live).unwrap();
    let (formula, model) = uf_formula_and_model(&case, &mut names);
    assert_eq!(evaluate_expr(&formula, &model), Some(SmtValue::Bool(false)));
    // The legacy reach-flag selector can still produce a candidate. It is
    // specifically original-source ground validation that must refuse it.
    let witness = uf_candidate(&case, &model, &mut names);
    assert!(uf_ground(&case, &witness, &model, &mut names).is_none());
    assert!(!names.stopped());
}

#[test]
fn missing_uf_observations_are_not_replaced_with_defaults() {
    let case = uf_case("f", UfArity::Unary, QueryEquality::Equal);
    let mut live = || true;
    let mut names = AcyclicNames::new(&case.solver.problem, &mut live).unwrap();
    let (_, model) = uf_formula_and_model(&case, &mut names);
    let witness = uf_candidate(&case, &model, &mut names);
    let mut missing = model.clone();
    missing.retain(|name, _| !name.starts_with("\0ay.uf-"));
    assert!(uf_ground(&case, &witness, &missing, &mut names).is_none());
    assert!(!names.stopped());
    assert!(uf_ground(&case, &witness, &model, &mut names).is_some());
}

#[test]
fn conflicting_source_uf_observations_fail_installation_and_ground_replay() {
    let case = uf_case("f", UfArity::Unary, QueryEquality::Equal);
    let mut live = || true;
    let mut names = AcyclicNames::new(&case.solver.problem, &mut live).unwrap();
    let (_, model) = uf_formula_and_model(&case, &mut names);
    let witness = uf_candidate(&case, &model, &mut names);
    let mut ground = uf_ground(&case, &witness, &model, &mut names).unwrap();
    let source_call = uf_application("f", UfArity::Unary, uf_var("a"));
    // A refused installation can leave private scratch in this deliberately
    // poisoned candidate. It must grant no authority at the next boundary.
    assert!(!install_observed_uf_application_values(
        &mut ground.steps[1].env,
        &[(source_call.clone(), uf_value(8))],
    ));
    assert!(matches!(
        validate_ground_derivation(&case.solver.problem, &ground),
        Err(GroundDerivationError::UfCongruenceViolation { .. })
    ));
    let mut conflicting = model.clone();
    conflicting.insert("a".to_owned(), uf_value(1));
    assert!(!install_observed_uf_application_values(
        &mut conflicting,
        &[(source_call, uf_value(8))],
    ));
    assert!(uf_ground(&case, &witness, &conflicting, &mut names).is_none());
    assert!(!names.stopped());
}

#[test]
fn a_source_uf_in_the_generated_name_family_stays_global_during_replay() {
    let symbol = "__bmc_poly_p0_a0";
    let case = uf_case(symbol, UfArity::Unary, QueryEquality::Equal);
    let before = format!("{:?}", case.solver.problem.clauses());
    let mut live = || true;
    let mut names = AcyclicNames::new(&case.solver.problem, &mut live).unwrap();
    let (formula, model) = uf_formula_and_model(&case, &mut names);
    let ChcExpr::Var(ref argument) = case.solver.dag_arg(case.pred, 0, &mut names).unwrap() else {
        panic!("generated argument");
    };
    assert_eq!(argument.name, "__bmc_poly_p0_a0__ay_exact_0");
    assert!(formula
        .vars()
        .iter()
        .all(|variable| variable.name != symbol));
    assert_eq!(evaluate_expr(&formula, &model), Some(SmtValue::Bool(true)));
    let witness = uf_candidate(&case, &model, &mut names);
    let ground = uf_ground(&case, &witness, &model, &mut names).unwrap();
    assert_eq!(
        validate_ground_derivation(&case.solver.problem, &ground),
        Ok(())
    );
    assert_eq!(before, format!("{:?}", case.solver.problem.clauses()));
}
