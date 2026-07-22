// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn cube_from_model_mbp_falls_back_when_residual_value_missing() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let x = solver.canonical_vars(pred).unwrap()[0].clone();
    let aux = ChcVar::new("aux", ChcSort::Int);

    // `aux` must be eliminated but is intentionally missing from the model.
    // Prior behavior substituted aux := 0, which could fabricate unsatisfiable cubes.
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::or(
            ChcExpr::gt(ChcExpr::var(aux.clone()), ChcExpr::int(0)),
            ChcExpr::lt(ChcExpr::var(aux), ChcExpr::int(0)),
        ),
    );

    let mut model = FxHashMap::default();
    model.insert(x.name.clone(), SmtValue::Int(1));

    let cube = solver
        .cube_from_model_mbp(pred, &[ChcExpr::var(x)], &formula, &model)
        .expect("fallback cube should be available");

    assert_eq!(
        solver.mbp.eval_bool(&cube, &model),
        Some(true),
        "cube should remain consistent with known model assignments"
    );
}

#[test]
fn cube_from_model_mbp_allow_residual_preserves_non_point_generalization() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canon = solver.canonical_vars(pred).unwrap()[0].clone();
    let y = ChcVar::new("aux_y", ChcSort::Int);
    let z = ChcVar::new("aux_z", ChcSort::Int);

    // y is projectable (x = y + 1, y > 0), z is intentionally non-linear
    // and stays residual in allow-residual mode. This should preserve the
    // generalized x-constraint instead of collapsing to x = model_value.
    let formula = ChcExpr::and_all(vec![
        ChcExpr::eq(
            ChcExpr::var(canon.clone()),
            ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::gt(ChcExpr::var(y), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::mul(ChcExpr::var(z.clone()), ChcExpr::var(z)),
            ChcExpr::int(4),
        ),
    ]);

    let mut model = FxHashMap::default();
    model.insert(canon.name.clone(), SmtValue::Int(5));
    model.insert("aux_y".to_string(), SmtValue::Int(4));
    model.insert("aux_z".to_string(), SmtValue::Int(2));

    let args = vec![ChcExpr::var(canon.clone())];
    let point_cube = solver
        .cube_from_model_or_constraints(pred, &args, &formula, &model)
        .expect("point cube fallback should be constructible");
    let cube = solver
        .cube_from_model_mbp(pred, &args, &formula, &model)
        .expect("MBP cube should be constructed");

    assert_ne!(
        cube, point_cube,
        "allow-residual MBP should retain generalization instead of point-cube fallback"
    );
    assert!(
        !crate::pdr::cube::is_point_cube_for_vars(&cube, std::slice::from_ref(&canon)),
        "allow-residual MBP cube should remain non-point after projection"
    );
    assert_eq!(
        solver.mbp.eval_bool(&cube, &model),
        Some(true),
        "projected cube should be satisfied by source model"
    );

    // Generalization check: bump canonical x while preserving aux values.
    // Point cube x=5 becomes false, generalized cube should remain true.
    let mut generalized_model = model.clone();
    generalized_model.insert(canon.name, SmtValue::Int(6));
    assert_eq!(
        solver.mbp.eval_bool(&cube, &generalized_model),
        Some(true),
        "generalized cube should admit x=6"
    );
    assert_ne!(
        solver.mbp.eval_bool(&point_cube, &generalized_model),
        Some(true),
        "point cube should reject x=6"
    );
}

#[test]
fn cube_with_mbp_bv_only_aux_preserves_non_point_generalization_issue_5877() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::BitVec(8), ChcSort::Bool]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let flag = ChcVar::new("flag", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pred,
                vec![ChcExpr::var(x.clone()), ChcExpr::var(flag.clone())],
            )],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x), ChcExpr::var(flag)]),
    ));

    let mut config = test_config();
    config.use_mbp = true;
    let solver = PdrSolver::new(problem, config);
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let canon_x = canonical_vars[0].clone();
    let canon_flag = canonical_vars[1].clone();
    let limit = ChcVar::new("limit", ChcSort::BitVec(8));
    let args = vec![
        ChcExpr::var(canon_x.clone()),
        ChcExpr::var(canon_flag.clone()),
    ];
    let formula = ChcExpr::and(
        ChcExpr::bv_sle(ChcExpr::var(canon_x.clone()), ChcExpr::var(limit.clone())),
        ChcExpr::var(canon_flag.clone()),
    );

    let mut model = FxHashMap::default();
    model.insert(canon_x.name.clone(), SmtValue::BitVec(4, 8));
    model.insert(canon_flag.name, SmtValue::Bool(true));
    model.insert(limit.name, SmtValue::BitVec(5, 8));

    let point_cube = solver
        .cube_from_model_or_constraints(pred, &args, &formula, &model)
        .expect("point-cube fallback should be constructible");
    let cube = solver
        .cube_with_mbp(pred, &args, &formula, &model)
        .expect("Bool+BV-only predecessor should use MBP");

    assert_ne!(
        cube, point_cube,
        "Bool+BV-only predecessors should preserve MBP generalization instead of falling back"
    );
    assert!(
        !crate::pdr::cube::is_point_cube_for_vars(&cube, &canonical_vars),
        "MBP result should remain non-point for the BV predecessor"
    );
    assert_eq!(
        solver.mbp.eval_bool(&cube, &model),
        Some(true),
        "projected BV cube must hold for the source model"
    );

    let mut generalized_model = model.clone();
    generalized_model.insert(canon_x.name, SmtValue::BitVec(5, 8));
    assert_eq!(
        solver.mbp.eval_bool(&cube, &generalized_model),
        Some(true),
        "generalized BV cube should admit x=5 when limit=5"
    );
    assert_ne!(
        solver.mbp.eval_bool(&point_cube, &generalized_model),
        Some(true),
        "point cube should reject the generalized BV assignment"
    );
}

#[test]
fn cube_with_mbp_mixed_bv_int_aux_falls_back_to_point_cube_issue_5877() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::BitVec(8), ChcSort::Bool]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let flag = ChcVar::new("flag", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pred,
                vec![ChcExpr::var(x.clone()), ChcExpr::var(flag.clone())],
            )],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x), ChcExpr::var(flag)]),
    ));

    let mut config = test_config();
    config.use_mbp = true;
    let solver = PdrSolver::new(problem, config);
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let canon_x = canonical_vars[0].clone();
    let canon_flag = canonical_vars[1].clone();
    let limit = ChcVar::new("limit", ChcSort::BitVec(8));
    let steps = ChcVar::new("steps", ChcSort::Int);
    let args = vec![
        ChcExpr::var(canon_x.clone()),
        ChcExpr::var(canon_flag.clone()),
    ];
    let formula = ChcExpr::and_all([
        ChcExpr::bv_sle(ChcExpr::var(canon_x.clone()), ChcExpr::var(limit.clone())),
        ChcExpr::gt(ChcExpr::var(steps.clone()), ChcExpr::int(0)),
        ChcExpr::var(canon_flag.clone()),
    ]);

    let mut model = FxHashMap::default();
    model.insert(canon_x.name, SmtValue::BitVec(4, 8));
    model.insert(canon_flag.name, SmtValue::Bool(true));
    model.insert(limit.name, SmtValue::BitVec(5, 8));
    model.insert(steps.name, SmtValue::Int(1));

    let point_cube = solver
        .cube_from_model_or_constraints(pred, &args, &formula, &model)
        .expect("point-cube fallback should be constructible");
    let ungated_mbp_cube = solver
        .cube_from_model_mbp(pred, &args, &formula, &model)
        .expect("test setup should remain MBP-generalizable without the mixed-sort gate");
    assert_ne!(
        ungated_mbp_cube, point_cube,
        "test setup must distinguish mixed-sort MBP from point-cube fallback"
    );

    let cube = solver
        .cube_with_mbp(pred, &args, &formula, &model)
        .expect("mixed BV+Int predecessor should still yield a fallback cube");
    assert_eq!(
        cube, point_cube,
        "mixed BV+Int auxiliary state must decline MBP and fall back to point cube"
    );
    assert!(
        crate::pdr::cube::is_point_cube_for_vars(&cube, &canonical_vars),
        "fallback cube should stay grounded after mixed-sort MBP rejection"
    );
}

#[test]
fn cube_from_model_mbp_augments_unconstrained_int_var() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x), ChcExpr::var(y)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let canon_x = canonical_vars[0].clone();
    let canon_y = canonical_vars[1].clone();
    let aux = ChcVar::new("aux", ChcSort::Int);
    let args = vec![ChcExpr::var(canon_x.clone()), ChcExpr::var(canon_y.clone())];
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(aux.clone()), ChcExpr::var(canon_x.clone())),
        ChcExpr::gt(ChcExpr::var(aux.clone()), ChcExpr::int(0)),
    );

    let mut model = FxHashMap::default();
    model.insert(canon_x.name.clone(), SmtValue::Int(5));
    model.insert(canon_y.name.clone(), SmtValue::Int(9));
    model.insert(aux.name, SmtValue::Int(5));

    let cube = solver
        .cube_from_model_mbp(pred, &args, &formula, &model)
        .expect("MBP should augment unconstrained canonical vars");

    assert!(
        cube.collect_conjuncts()
            .contains(&ChcExpr::eq(ChcExpr::var(canon_y), ChcExpr::int(9))),
        "augmentation should add y = model(y) for unconstrained canonical var"
    );
    assert_eq!(
        solver.mbp.eval_bool(&cube, &model),
        Some(true),
        "augmented cube must hold for source model"
    );

    let mut generalized_model = model.clone();
    generalized_model.insert(canon_x.name, SmtValue::Int(6));
    assert_eq!(
        solver.mbp.eval_bool(&cube, &generalized_model),
        Some(true),
        "MBP constraint on constrained vars should remain generalized"
    );
}

#[test]
fn cube_from_model_mbp_bool_augmentation_remains_point_cube_compatible() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Bool]);
    let x = ChcVar::new("x", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(b.clone())])],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x), ChcExpr::var(b)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let canon_x = canonical_vars[0].clone();
    let canon_b = canonical_vars[1].clone();
    let aux = ChcVar::new("aux", ChcSort::Int);
    let args = vec![ChcExpr::var(canon_x.clone()), ChcExpr::var(canon_b.clone())];
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(aux.clone()), ChcExpr::int(4)),
        ChcExpr::eq(ChcExpr::var(canon_x.clone()), ChcExpr::var(aux.clone())),
    );

    let mut model = FxHashMap::default();
    model.insert(canon_x.name, SmtValue::Int(4));
    model.insert(canon_b.name, SmtValue::Bool(false));
    model.insert(aux.name, SmtValue::Int(4));

    let cube = solver
        .cube_from_model_mbp(pred, &args, &formula, &model)
        .expect("MBP should augment unconstrained bool canonical var");

    assert_eq!(
        solver.mbp.eval_bool(&cube, &model),
        Some(true),
        "augmented mixed cube must hold for source model"
    );
    assert!(
        crate::pdr::cube::is_point_cube_for_vars(&cube, &canonical_vars),
        "augmented bool assignment should be recognized as a grounded point cube"
    );
}

#[test]
fn cube_from_model_mbp_bool_true_augmentation_emits_equality() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Bool]);
    let x = ChcVar::new("x", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(b.clone())])],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x), ChcExpr::var(b)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let canon_x = canonical_vars[0].clone();
    let canon_b = canonical_vars[1].clone();
    let aux = ChcVar::new("aux", ChcSort::Int);
    let args = vec![ChcExpr::var(canon_x.clone()), ChcExpr::var(canon_b.clone())];
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(aux.clone()), ChcExpr::int(7)),
        ChcExpr::eq(ChcExpr::var(canon_x.clone()), ChcExpr::var(aux.clone())),
    );

    let mut model = FxHashMap::default();
    model.insert(canon_x.name, SmtValue::Int(7));
    model.insert(canon_b.name, SmtValue::Bool(true));
    model.insert(aux.name, SmtValue::Int(7));

    let cube = solver
        .cube_from_model_mbp(pred, &args, &formula, &model)
        .expect("MBP should augment unconstrained bool canonical var (true)");

    assert_eq!(
        solver.mbp.eval_bool(&cube, &model),
        Some(true),
        "augmented mixed cube must hold for source model"
    );
    assert!(
        crate::pdr::cube::is_point_cube_for_vars(&cube, &canonical_vars),
        "augmented bool=true assignment should be recognized as a grounded point cube"
    );
}

#[test]
fn cube_from_model_mbp_unconstrained_missing_value_uses_partial_fallback() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            None,
        ),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x), ChcExpr::var(y)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let canon_x = canonical_vars[0].clone();
    let canon_y = canonical_vars[1].clone();
    let aux = ChcVar::new("aux", ChcSort::Int);
    let args = vec![ChcExpr::var(canon_x.clone()), ChcExpr::var(canon_y.clone())];
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(aux.clone()), ChcExpr::var(canon_x.clone())),
        ChcExpr::gt(ChcExpr::var(aux.clone()), ChcExpr::int(0)),
    );

    // Missing value for canon_y: no model entry and no constraint provides its value.
    // cube_from_model rejects partial cubes (#3004). cube_from_equalities also fails
    // since the formula has no equality for canon_y. But cube_from_model_partial (#3121)
    // returns a best-effort partial cube skipping unevaluable variables. This is sound
    // for PDR blocking (fewer conjuncts = more general = blocks more states).
    let mut model = FxHashMap::default();
    model.insert(canon_x.name.clone(), SmtValue::Int(5));
    model.insert(aux.name, SmtValue::Int(5));

    let fallback_cube = solver.cube_from_model_or_constraints(pred, &args, &formula, &model);
    assert!(
        fallback_cube.is_some(),
        "cube_from_model_or_constraints should return partial cube via cube_from_model_partial (#3121)"
    );
    // The partial cube should constrain only canon_x (the variable with a model value).
    let cube_expr = fallback_cube.unwrap();
    let cube_vars = cube_expr.vars();
    assert!(
        cube_vars.iter().any(|v| v.name == canon_x.name),
        "partial cube must constrain canon_x (has model value)"
    );
    assert!(
        !cube_vars.iter().any(|v| v.name == canon_y.name),
        "partial cube must NOT constrain canon_y (no model value)"
    );

    let mbp_cube = solver.cube_with_mbp(pred, &args, &formula, &model);
    // MBP also returns a cube (falls back internally to cube_from_model_or_constraints).
    assert!(
        mbp_cube.is_some(),
        "cube_with_mbp should return a cube via partial fallback (#3121)"
    );
}

#[test]
fn cube_from_model_or_constraints_bv_partial_model_preserves_non_bv_bindings_issue_6781() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate(
        "P",
        vec![
            ChcSort::BitVec(32),
            ChcSort::Bool,
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
        ],
    );
    let x = ChcVar::new("x", ChcSort::BitVec(32));
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let mem = ChcVar::new(
        "mem",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pred,
                vec![
                    ChcExpr::var(x.clone()),
                    ChcExpr::var(flag.clone()),
                    ChcExpr::var(mem.clone()),
                ],
            )],
            None,
        ),
        ClauseHead::Predicate(
            pred,
            vec![ChcExpr::var(x), ChcExpr::var(flag), ChcExpr::var(mem)],
        ),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let canon_x = canonical_vars[0].clone();
    let canon_flag = canonical_vars[1].clone();
    let canon_mem = canonical_vars[2].clone();
    let args = vec![
        ChcExpr::var(canon_x.clone()),
        ChcExpr::var(canon_flag.clone()),
        ChcExpr::var(canon_mem.clone()),
    ];
    let formula = ChcExpr::eq(ChcExpr::var(canon_flag.clone()), ChcExpr::Bool(false));

    let mut model = FxHashMap::default();
    model.insert(canon_flag.name.clone(), SmtValue::Bool(false));
    model.insert(
        canon_mem.name.clone(),
        SmtValue::ConstArray(Box::new(SmtValue::Bool(false))),
    );

    let cube = solver
        .cube_from_model_or_constraints(pred, &args, &formula, &model)
        .expect("BV partial model should still produce a best-effort cube (#6781)");

    let expected = ChcExpr::and_all([
        ChcExpr::not(ChcExpr::var(canon_flag)),
        ChcExpr::eq(
            ChcExpr::var(canon_mem),
            ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Bool(false))),
        ),
    ]);
    assert_eq!(
        cube, expected,
        "partial BV cube fallback should keep available Bool/Array bindings instead of returning None"
    );
    let cube_vars = cube.vars();
    assert!(
        !cube_vars.iter().any(|v| v.name == canon_x.name),
        "missing BV value must be skipped rather than fabricated in the fallback cube"
    );
}

/// Regression test for #3004: cube_from_model must reject partial cubes
/// where not all non-array canonical variables have model values.
#[test]
fn cube_from_model_rejects_partial_model() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pred,
                vec![
                    ChcExpr::var(x.clone()),
                    ChcExpr::var(y.clone()),
                    ChcExpr::var(z.clone()),
                ],
            )],
            None,
        ),
        ClauseHead::Predicate(
            pred,
            vec![ChcExpr::var(x), ChcExpr::var(y), ChcExpr::var(z)],
        ),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canonical_vars = solver
        .canonical_vars(pred)
        .expect("P should have canonical vars")
        .to_vec();
    let args: Vec<ChcExpr> = canonical_vars
        .iter()
        .map(|v| ChcExpr::var(v.clone()))
        .collect();

    // Full model: all vars present → should return Some
    let mut full_model = FxHashMap::default();
    full_model.insert(canonical_vars[0].name.clone(), SmtValue::Int(1));
    full_model.insert(canonical_vars[1].name.clone(), SmtValue::Int(2));
    full_model.insert(canonical_vars[2].name.clone(), SmtValue::Int(3));
    assert!(
        solver.cube_from_model(pred, &args, &full_model).is_some(),
        "complete model should produce a cube"
    );

    // Partial model: z missing → must return None (not a partial cube with only x,y)
    let mut partial_model = FxHashMap::default();
    partial_model.insert(canonical_vars[0].name.clone(), SmtValue::Int(1));
    partial_model.insert(canonical_vars[1].name.clone(), SmtValue::Int(2));
    assert!(
        solver
            .cube_from_model(pred, &args, &partial_model)
            .is_none(),
        "partial model (missing z) must return None, not a partial cube (#3004)"
    );

    // Empty model: no vars → must return None
    let empty_model = FxHashMap::default();
    assert!(
        solver.cube_from_model(pred, &args, &empty_model).is_none(),
        "empty model must return None (#3004)"
    );
}

#[test]
fn point_cube_detection_rejects_self_referential_equalities() {
    let x = ChcVar::new("x", ChcSort::Int);
    let cube = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );

    assert!(
        !crate::pdr::cube::is_point_cube_for_vars(&cube, &[x]),
        "x = x + 1 is not a point assignment"
    );
}

#[test]
fn point_cube_detection_accepts_var_free_non_literal_terms() {
    let x = ChcVar::new("x", ChcSort::Int);
    let cube = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::add(ChcExpr::int(2), ChcExpr::int(3)),
    );

    assert!(
        crate::pdr::cube::is_point_cube_for_vars(&cube, &[x]),
        "x = 2 + 3 is still a concrete point assignment"
    );
}

#[test]
fn cube_from_equalities_supports_bool_constants() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Bool]);
    let b = ChcVar::new("b", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![ChcExpr::var(b.clone())])], None),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(b)]),
    ));

    let solver = PdrSolver::new(problem, test_config());
    let canon = solver.canonical_vars(pred).unwrap()[0].clone();
    let cube = solver.cube_from_equalities(pred, &[ChcExpr::Bool(true)], &ChcExpr::Bool(true));

    assert_eq!(
        cube,
        Some(ChcExpr::var(canon)),
        "bool constant head args should produce a canonical bool cube"
    );
}

#[test]
fn cube_from_model_mbp_proxy_name_collision_does_not_capture_model_var() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canon = solver.canonical_vars(pred).unwrap()[0].clone();
    let x = ChcVar::new("x", ChcSort::Int);
    // Deliberately collide with the proxy naming scheme.
    let colliding = ChcVar::new("__mbp_head_0", ChcSort::Int);

    let formula = ChcExpr::eq(ChcExpr::var(colliding.clone()), ChcExpr::int(42));
    let args = vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))];

    let mut model = FxHashMap::default();
    model.insert(x.name, SmtValue::Int(1));
    model.insert(colliding.name, SmtValue::Int(42));

    let cube = solver
        .cube_from_model_mbp(pred, &args, &formula, &model)
        .expect("cube should still be extractable when a colliding name exists");

    // The cube must only reference canonical variables (no raw formula vars).
    let cube_vars = cube.vars();
    for v in &cube_vars {
        assert_eq!(
            v.name, canon.name,
            "cube should only reference canonical var '{}', found '{}'",
            canon.name, v.name
        );
    }

    // The head arg is x+1 with x=1, so the canonical var should map to 2.
    let mut expected_model = model.clone();
    expected_model.insert(canon.name.clone(), SmtValue::Int(2));
    assert_eq!(
        solver.mbp.eval_bool(&cube, &expected_model),
        Some(true),
        "cube should be satisfied when canonical var = 2 (from x+1 = 1+1)"
    );

    // Negative test: the cube should NOT be satisfied by the colliding
    // var's value (42) being assigned to the canonical var.
    let mut wrong_model = model.clone();
    wrong_model.insert(canon.name, SmtValue::Int(42));
    assert_ne!(
        solver.mbp.eval_bool(&cube, &wrong_model),
        Some(true),
        "cube should NOT be satisfied when canonical var = 42 (the colliding var's value)"
    );
}
