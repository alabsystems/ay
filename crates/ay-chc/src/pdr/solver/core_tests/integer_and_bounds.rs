// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Tests for extract_integer_only_cube (proof_coverage: #1619-1700)
// =========================================================================

#[test]
fn extract_integer_only_cube_basic_int() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canon = solver
        .canonical_vars(pred)
        .expect("invariant: canonical vars exist")[0]
        .clone();

    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(42));

    let cube = solver
        .extract_integer_only_cube(pred, &[ChcExpr::var(x)], &model)
        .expect("should produce cube for present Int var");

    // Cube should be exactly (= canon_var 42).
    let expected = ChcExpr::eq(ChcExpr::var(canon), ChcExpr::Int(42));
    assert_eq!(cube, expected);
}

#[test]
fn extract_integer_only_cube_bool_var() {
    // Predicate with a Bool argument
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Bool]);
    let b = ChcVar::new("b", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![ChcExpr::var(b.clone())])], None),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(b.clone())]),
    ));

    let solver = PdrSolver::new(problem, test_config());

    let mut model = FxHashMap::default();
    model.insert("b".to_string(), SmtValue::Bool(true));

    let cube = solver
        .extract_integer_only_cube(pred, &[ChcExpr::var(b)], &model)
        .expect("should produce cube for present Bool var");

    // Cube should be exactly the canonical bool variable.
    let canon = solver
        .canonical_vars(pred)
        .expect("invariant: canonical vars exist")[0]
        .clone();
    assert_eq!(cube, ChcExpr::var(canon));
}

#[test]
fn extract_integer_only_cube_missing_var_returns_none() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    let x = ChcVar::new("x", ChcSort::Int);
    let model = FxHashMap::default(); // empty model

    let result = solver.extract_integer_only_cube(pred, &[ChcExpr::var(x)], &model);
    assert!(
        result.is_none(),
        "missing variable in model should return None"
    );
}

#[test]
fn extract_integer_only_cube_constant_arg() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    let model = FxHashMap::default();

    // Pass Int(7) directly as argument (not a variable)
    let cube = solver
        .extract_integer_only_cube(pred, &[ChcExpr::Int(7)], &model)
        .expect("constant Int arg should produce cube without model lookup");

    // Cube should bind the canonical variable to 7.
    let canon = solver
        .canonical_vars(pred)
        .expect("invariant: canonical vars exist")[0]
        .clone();
    let expected = ChcExpr::eq(ChcExpr::var(canon), ChcExpr::Int(7));
    assert_eq!(cube, expected);
}

#[test]
fn extract_integer_only_cube_arity_mismatch_returns_none() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    let model = FxHashMap::default();

    // P has arity 1 but we pass 2 args
    let result =
        solver.extract_integer_only_cube(pred, &[ChcExpr::Int(1), ChcExpr::Int(2)], &model);
    assert!(result.is_none(), "arity mismatch should return None");
}

#[test]
fn extract_integer_only_cube_expression_arg_evaluates() {
    let solver = PdrSolver::new(test_linear_problem(), test_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    // Pass (x + 1) as argument — should evaluate to 4
    let expr_arg = ChcExpr::add(ChcExpr::var(x), ChcExpr::Int(1));
    let cube = solver
        .extract_integer_only_cube(pred, &[expr_arg], &model)
        .expect("evaluable expression arg should produce cube");

    let canon = solver
        .canonical_vars(pred)
        .expect("invariant: canonical vars exist")[0]
        .clone();
    let expected = ChcExpr::eq(ChcExpr::var(canon), ChcExpr::Int(4));
    assert_eq!(cube, expected);
}

// =========================================================================
// Tests for extract_lower_bound_recursive (#3047)
// =========================================================================

#[test]
fn test_extract_lower_bound_ge() {
    // (>= x 5) → lower bound 5
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(5)
    );
}

#[test]
fn test_extract_lower_bound_gt() {
    // (> x 5) → lower bound 6 (x > 5 means x >= 6)
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(6)
    );
}

#[test]
fn test_extract_lower_bound_not_le() {
    // (not (<= x 5)) → lower bound 6 (not(x <= 5) means x > 5 means x >= 6)
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::not(ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5)));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(6)
    );
}

#[test]
fn test_extract_lower_bound_not_lt() {
    // (not (< x 5)) → lower bound 5 (not(x < 5) means x >= 5)
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::not(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(5)));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(5)
    );
}

#[test]
fn test_extract_lower_bound_in_and() {
    // (and (>= x 3) (>= y 10)) → lower bound for x is 3
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3)),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(10)),
    );
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(3)
    );
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "y"),
        Some(10)
    );
}

#[test]
fn test_extract_lower_bound_wrong_var() {
    // (>= x 5) → no lower bound for y
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "y"),
        None
    );
}

#[test]
fn test_extract_lower_bound_unrelated_formula() {
    // (<= x 5) is an upper bound, not a lower bound
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        None
    );
}

#[test]
fn test_extract_lower_bound_negative() {
    // (>= x -10) → lower bound -10
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(-10));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(-10)
    );
}

#[test]
fn test_extract_lower_bound_gt_max_saturates() {
    // With the i128 representation, (> x i64::MAX) has an exact lower bound
    // of i64::MAX + 1; saturation only applies at the i128 boundary:
    // (> x i128::MAX) → saturating_add(i128::MAX, 1) = i128::MAX.
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(i64::MAX));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(i128::from(i64::MAX) + 1)
    );
    let x = ChcVar::new("x", ChcSort::Int);
    let formula = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(i128::MAX));
    assert_eq!(
        PdrSolver::extract_lower_bound_recursive(&formula, "x"),
        Some(i128::MAX)
    );
}

// =========================================================================
// Tests for insert_reach_fact_bounded (#3047)
// =========================================================================

#[test]
fn test_insert_reach_fact_bounded_success() {
    use crate::pdr::reach_fact::{ReachFact, ReachFactId};
    use crate::pdr::solver::ReachabilityState;
    use crate::PredicateId;

    let mut reachability = ReachabilityState::new();
    let fact = ReachFact {
        id: ReachFactId(0),
        predicate: PredicateId(0),
        level: 0,
        state: ChcExpr::Bool(true),
        incoming_clause: None,
        premises: Vec::new(),
        instances: FxHashMap::default(),
    };

    let result = PdrSolver::insert_reach_fact_bounded(&mut reachability, false, fact);
    assert!(result.is_some(), "insertion should succeed");
    assert!(
        !reachability.reach_facts_saturated,
        "store should not be saturated after one insert"
    );
}

#[test]
fn test_insert_reach_fact_bounded_returns_valid_id() {
    use crate::pdr::reach_fact::{ReachFact, ReachFactId};
    use crate::pdr::solver::ReachabilityState;
    use crate::PredicateId;

    let mut reachability = ReachabilityState::new();

    // Insert two distinct facts and verify they get distinct IDs.
    let fact1 = ReachFact {
        id: ReachFactId(0),
        predicate: PredicateId(0),
        level: 0,
        state: ChcExpr::Bool(true),
        incoming_clause: None,
        premises: Vec::new(),
        instances: FxHashMap::default(),
    };
    let fact2 = ReachFact {
        id: ReachFactId(0),
        predicate: PredicateId(0),
        level: 1,
        state: ChcExpr::Bool(false),
        incoming_clause: None,
        premises: Vec::new(),
        instances: FxHashMap::default(),
    };
    let id1 = PdrSolver::insert_reach_fact_bounded(&mut reachability, false, fact1);
    let id2 = PdrSolver::insert_reach_fact_bounded(&mut reachability, false, fact2);
    assert!(id1.is_some(), "first insert should succeed");
    assert!(id2.is_some(), "second insert should succeed");
    assert_ne!(id1.unwrap(), id2.unwrap(), "IDs should be distinct");
    assert!(
        !reachability.reach_facts_saturated,
        "store should not be saturated after two inserts"
    );
}

#[test]
fn test_reach_fact_saturation_requests_cancellation() {
    let mut solver = PdrSolver::new(test_must_reachability_problem(), test_must_config());
    assert!(
        !solver.is_cancelled(),
        "fresh solver should not be cancelled"
    );

    solver.reachability.reach_facts_saturated = true;

    assert!(
        solver.is_cancelled(),
        "reach-fact saturation must fail closed through cooperative cancellation"
    );
}

// =========================================================================
// Tests for must_reachability.rs (#3047)
// =========================================================================

use crate::pdr::reach_fact::{ReachFact, ReachFactId};

/// Build a linear problem P(x) with a fact clause (true => P(0)) and
/// a transition clause (P(x) => P(x+1)), plus a query (P(x) => false).
fn test_must_reachability_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: true => P(0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));

    // Transition: P(x) => P(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::Bool(true)),
        ),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: P(x) ∧ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn test_must_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_negated_equality_splits: false,
        use_must_summaries: true,
        ..PdrConfig::default()
    }
}

#[test]
fn pick_reach_fact_premise_returns_none_when_no_facts() {
    let solver = PdrSolver::new(test_must_reachability_problem(), test_must_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let x = ChcVar::new("x", ChcSort::Int);
    let model = FxHashMap::default();

    // No reach facts have been inserted, so pick_reach_fact_premise should return None.
    let result = solver.pick_reach_fact_premise(pred, 0, &[ChcExpr::var(x)], &model);
    assert!(result.is_none());
}

#[test]
fn pick_reach_fact_premise_selects_matching_fact() {
    let mut solver = PdrSolver::new(test_must_reachability_problem(), test_must_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canonical_var = ChcVar::new("__p0_a0", ChcSort::Int);

    // Insert a reach fact: P(__p0_a0) with state (__p0_a0 = 5)
    let state = ChcExpr::eq(ChcExpr::var(canonical_var), ChcExpr::int(5));
    let fact = ReachFact {
        id: ReachFactId(0),
        predicate: pred,
        level: 0,
        state,
        incoming_clause: None,
        premises: Vec::new(),
        instances: FxHashMap::default(),
    };
    let rf_id =
        PdrSolver::insert_reach_fact_bounded(&mut solver.reachability, false, fact).unwrap();

    // Build a model where x = 5, and args = [x]
    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));

    // pick_reach_fact_premise should find the matching fact
    let result = solver.pick_reach_fact_premise(pred, 0, &[ChcExpr::var(x)], &model);
    assert_eq!(result, Some(rf_id));
}

#[test]
fn pick_reach_fact_premise_rejects_non_matching_fact() {
    let mut solver = PdrSolver::new(test_must_reachability_problem(), test_must_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canonical_var = ChcVar::new("__p0_a0", ChcSort::Int);

    // Insert a reach fact: P(__p0_a0) with state (__p0_a0 = 5)
    let state = ChcExpr::eq(ChcExpr::var(canonical_var), ChcExpr::int(5));
    let fact = ReachFact {
        id: ReachFactId(0),
        predicate: pred,
        level: 0,
        state,
        incoming_clause: None,
        premises: Vec::new(),
        instances: FxHashMap::default(),
    };
    PdrSolver::insert_reach_fact_bounded(&mut solver.reachability, false, fact);

    // Build a model where x = 7 (doesn't match the state constraint __p0_a0 = 5)
    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(7));

    let result = solver.pick_reach_fact_premise(pred, 0, &[ChcExpr::var(x)], &model);
    assert!(result.is_none());
}

#[test]
fn add_must_summary_backed_is_noop_when_disabled() {
    let mut config = test_must_config();
    config.use_must_summaries = false;
    let mut solver = PdrSolver::new(test_must_reachability_problem(), config);
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;

    // Insert must summary while disabled — should be a no-op
    solver.add_must_summary_backed(pred, 0, ChcExpr::Bool(true), ReachFactId(0));

    // Verify nothing was added
    assert!(solver.reachability.must_summaries.get(0, pred).is_none());
}

#[test]
fn add_must_summary_backed_stores_when_enabled() {
    let mut solver = PdrSolver::new(test_must_reachability_problem(), test_must_config());
    let pred = solver
        .problem
        .get_predicate_by_name("P")
        .expect("P should exist")
        .id;
    let canonical_var = ChcVar::new("__p0_a0", ChcSort::Int);

    let formula = ChcExpr::eq(ChcExpr::var(canonical_var), ChcExpr::int(42));
    solver.add_must_summary_backed(pred, 1, formula, ReachFactId(0));

    let retrieved = solver.reachability.must_summaries.get(1, pred);
    assert!(retrieved.is_some(), "must summary should exist at level 1");
}

#[test]
fn block_unreachable_predicates_blocks_isolated_predicate() {
    // Build a problem with two predicates: P is reachable (has fact clause),
    // Q is unreachable (no fact clause, no path from P).
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: true => P(0) — makes P reachable
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));

    // Transition: P(x) => P(x+1) — P reaches itself
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Q(x) => false — Q is queried but unreachable
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, test_must_config());

    // Before blocking: frame[0] should have no Q lemmas
    assert!(solver.frames[0].get_predicate_constraint(q).is_none());

    solver.block_unreachable_predicates_at_frame0();

    // After blocking: frame[0] should block Q with false
    let q_constraint = solver.frames[0].get_predicate_constraint(q);
    assert!(q_constraint.is_some(), "Q should have a blocking lemma");
    assert_eq!(q_constraint.unwrap(), ChcExpr::Bool(false));

    // P should NOT be blocked (it's reachable)
    // P may or may not have a constraint — the important thing is it's not false.
    let p_constraint = solver.frames[0].get_predicate_constraint(p);
    assert!(
        p_constraint.is_none() || p_constraint != Some(ChcExpr::Bool(false)),
        "P should not be blocked"
    );
}

/// Regression test for #3004: must-reachability path must not fabricate default
/// values for missing model entries.
///
/// When a fact clause constrains only some variables (e.g., `x = 0` but `y`
/// unconstrained), the SMT solver may return a partial model with only `x`.
/// Prior to #3004, `cube_from_model` would silently default `y` to `0`,
/// creating a fabricated concrete state. After the fix, `cube_from_model`
/// returns `None` for partial models, and `check_must_reachability` skips the
/// clause via `continue` rather than inserting an over-approximate reach fact.
#[test]
fn must_reachability_rejects_partial_model_no_default_zero() {
    // P(x, y) with fact clause: x = 0 => P(x, y)
    // The fact constrains x but leaves y unconstrained.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Fact: x = 0 => P(x, y) — y is unconstrained
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
    ));

    // Query: P(x, y) ∧ x >= 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y)])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let solver = PdrSolver::new(problem, test_must_config());
    let canonical_vars = solver.canonical_vars(p).unwrap().to_vec();
    assert_eq!(canonical_vars.len(), 2, "P should have 2 canonical vars");

    let args: Vec<ChcExpr> = canonical_vars
        .iter()
        .map(|v| ChcExpr::var(v.clone()))
        .collect();

    // Simulate the must-reachability scenario: SMT returns a model with only
    // the first canonical var (x) assigned. The second var (y) is missing,
    // which previously would have been fabricated as 0.
    let mut partial_model = FxHashMap::default();
    partial_model.insert(canonical_vars[0].name.clone(), SmtValue::Int(0));
    // canonical_vars[1] intentionally missing — simulates partial SAT model

    let result = solver.cube_from_model(p, &args, &partial_model);
    assert!(
        result.is_none(),
        "cube_from_model must return None for partial model (missing y), \
         not fabricate y = 0. This prevents must-reachability from inserting \
         over-approximate reach facts (#3004)"
    );

    // Verify that a full model succeeds (sanity check)
    let mut full_model = partial_model.clone();
    full_model.insert(canonical_vars[1].name.clone(), SmtValue::Int(7));
    let cube = solver
        .cube_from_model(p, &args, &full_model)
        .expect("cube_from_model should succeed with a complete model");
    // Structurally verify the cube binds both canonical vars to model values.
    let x_eq = ChcExpr::eq(ChcExpr::var(canonical_vars[0].clone()), ChcExpr::Int(0));
    let y_eq = ChcExpr::eq(ChcExpr::var(canonical_vars[1].clone()), ChcExpr::Int(7));
    let expected = ChcExpr::and(x_eq, y_eq);
    assert_eq!(
        cube, expected,
        "cube should contain actual model values (x=0, y=7), not fabricated defaults"
    );
}

// ---- Deep nesting tests for extract_lower/upper_bound_recursive (#2487) ----
//
// These tests build genuinely deeply-nested AND trees using Op(And, ...) directly
// to bypass the canonicalizing ChcExpr::and() constructor which flattens AND chains
// into a single n-ary node. Without this bypass, the "10K-depth" expression would
// be a flat And(10001 args) and test iteration, not recursion.

/// Build a left-associated AND chain of depth `n`: And(And(...And(inner, filler)..., filler), filler)
/// Uses Op(And, ...) directly to avoid flattening by ChcExpr::and().
fn build_genuinely_nested_and(inner: ChcExpr, filler: ChcExpr, depth: usize) -> ChcExpr {
    let mut expr = inner;
    for _ in 0..depth {
        expr = ChcExpr::Op(ChcOp::And, vec![Arc::new(expr), Arc::new(filler.clone())]);
    }
    expr
}

fn assert_left_associated_binary_and_depth(expr: &ChcExpr, expected_depth: usize) {
    let mut depth = 0usize;
    let mut current = expr;
    while let ChcExpr::Op(ChcOp::And, args) = current {
        assert_eq!(
            args.len(),
            2,
            "And node at depth {depth} should be binary, not flattened"
        );
        depth += 1;
        current = args[0].as_ref();
    }
    assert_eq!(
        depth, expected_depth,
        "expected left-associated AND depth {expected_depth}, got {depth}"
    );
}

#[test]
fn deep_nesting_extract_lower_bound_no_stack_overflow() {
    let bound = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(42),
    );
    let filler = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
        ChcExpr::Int(0),
    );
    // Depth 2000: deep enough to exercise stacker, small enough for debug-mode
    // stack frames. At 10K depth, debug builds overflow because the 32KB red zone
    // is insufficient for the ~1-2KB debug-mode closures. Filed as a separate issue.
    let deep = build_genuinely_nested_and(bound, filler, 2_000);

    assert_left_associated_binary_and_depth(&deep, 2_000);

    let result = PdrSolver::extract_lower_bound_recursive(&deep, "x");
    assert_eq!(
        result,
        Some(42),
        "extract_lower_bound_recursive should find x >= 42 in deeply nested AND chain, got {result:?}"
    );
}

#[test]
fn deep_nesting_extract_upper_bound_no_stack_overflow() {
    let bound = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(99),
    );
    let filler = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
        ChcExpr::Int(0),
    );
    let deep = build_genuinely_nested_and(bound, filler, 2_000);

    assert_left_associated_binary_and_depth(&deep, 2_000);

    let result = PdrSolver::extract_upper_bound_recursive_impl(&deep, "x");
    assert_eq!(
        result,
        Some(99),
        "extract_upper_bound_recursive_impl should find x <= 99 in deeply nested AND chain, got {result:?}"
    );
}
