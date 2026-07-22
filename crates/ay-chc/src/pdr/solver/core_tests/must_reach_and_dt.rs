// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// #7016 PG1: DT cube extraction in partial and MBP paths
// =========================================================================

/// Helper: create a simple IntPair DT sort for tests.
fn test_dt_sort_int_pair() -> ChcSort {
    ChcSort::Datatype {
        name: "IntPair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkpair".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    }
}

/// #7016 PG1: cube_from_model produces DT constructor equality.
#[test]
fn cube_from_model_dt_produces_constructor_equality() {
    let dt_sort = test_dt_sort_int_pair();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![dt_sort.clone(), ChcSort::Int]);
    let p = ChcVar::new("p", dt_sort);
    let n = ChcVar::new("n", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(p.clone()), ChcExpr::var(n.clone())])],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(p), ChcExpr::var(n)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver.canonical_vars(pred).unwrap().to_vec();
    let args: Vec<ChcExpr> = canonical_vars
        .iter()
        .map(|v| ChcExpr::var(v.clone()))
        .collect();

    let mut model = FxHashMap::default();
    model.insert(
        canonical_vars[0].name.clone(),
        SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(42), SmtValue::Int(7)],
        ),
    );
    model.insert(canonical_vars[1].name.clone(), SmtValue::Int(10));

    let cube = solver
        .cube_from_model(pred, &args, &model)
        .expect("cube_from_model should handle DT vars");
    let cube_str = format!("{cube}");
    assert!(
        cube_str.contains("mkpair"),
        "DT cube must contain constructor name 'mkpair', got: {cube_str}"
    );
}

/// #7016 PG1: cube_from_model_partial includes DT constraints.
#[test]
fn cube_from_model_partial_dt_includes_constraints() {
    let dt_sort = test_dt_sort_int_pair();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![dt_sort.clone(), ChcSort::Int]);
    let p = ChcVar::new("p", dt_sort);
    let n = ChcVar::new("n", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(p.clone()), ChcExpr::var(n.clone())])],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(p), ChcExpr::var(n)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver.canonical_vars(pred).unwrap().to_vec();
    let args: Vec<ChcExpr> = canonical_vars
        .iter()
        .map(|v| ChcExpr::var(v.clone()))
        .collect();

    // Partial model: only DT var present, Int var missing.
    let mut model = FxHashMap::default();
    model.insert(
        canonical_vars[0].name.clone(),
        SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(1), SmtValue::Int(2)],
        ),
    );

    assert!(
        solver.cube_from_model(pred, &args, &model).is_none(),
        "cube_from_model should reject partial model (missing Int var)"
    );

    let partial = solver
        .cube_from_model_partial(pred, &args, &model)
        .expect("cube_from_model_partial should produce a partial cube with DT constraints");
    let partial_str = format!("{partial}");
    assert!(
        partial_str.contains("mkpair"),
        "partial cube must include DT constructor, got: {partial_str}"
    );
}

/// #7016 PG1: cube_from_equalities skips DT vars instead of failing.
#[test]
fn cube_from_equalities_skips_dt_vars() {
    let dt_sort = test_dt_sort_int_pair();
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![dt_sort.clone(), ChcSort::Int]);
    let p = ChcVar::new("p", dt_sort);
    let n = ChcVar::new("n", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(p.clone()), ChcExpr::var(n.clone())])],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(p), ChcExpr::var(n)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver.canonical_vars(pred).unwrap().to_vec();
    let args: Vec<ChcExpr> = canonical_vars
        .iter()
        .map(|v| ChcExpr::var(v.clone()))
        .collect();

    // Constraint with an equality for the Int var only.
    let constraint = ChcExpr::eq(ChcExpr::var(canonical_vars[1].clone()), ChcExpr::Int(5));

    let cube = solver
        .cube_from_equalities(pred, &args, &constraint)
        .expect("cube_from_equalities should skip DT vars, not fail");
    let cube_str = format!("{cube}");
    assert!(
        cube_str.contains("5"),
        "cube should contain the Int equality, got: {cube_str}"
    );
}
