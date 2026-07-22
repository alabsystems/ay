// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test provider that returns a fixed hint
struct TestProvider {
    hint: LemmaHint,
}

impl LemmaHintProvider for TestProvider {
    fn collect(&self, _req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        out.push(self.hint.clone());
    }
}

#[test]
fn test_provider_trait() {
    let provider = TestProvider {
        hint: LemmaHint::new(PredicateId(0), ChcExpr::Bool(true), 100, "test-provider"),
    };

    let problem = ChcProblem::new();
    let vars: Vec<ChcVar> = vec![];
    let vars_ref: &[ChcVar] = &vars;
    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(vars_ref) };
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);
    assert_eq!(hints.len(), 1);
    assert_eq!(hints[0].predicate, PredicateId(0));
}

#[test]
fn test_hint_creation() {
    let hint = LemmaHint::new(
        PredicateId(0),
        ChcExpr::ge(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(0),
        ),
        100,
        "test-provider",
    );
    assert_eq!(hint.predicate, PredicateId(0));
    assert_eq!(hint.priority, 100);
    assert_eq!(hint.source, "test-provider");
}

#[test]
fn test_hint_request() {
    let problem = ChcProblem::new();
    let vars: Vec<ChcVar> = vec![ChcVar::new("x", ChcSort::Int)];
    let vars_ref: &[ChcVar] = &vars;

    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(vars_ref) };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    assert_eq!(req.stage, HintStage::Startup);
    assert!(req.canonical_vars(PredicateId(0)).is_some());
}

#[test]
fn test_deterministic_sorting() {
    // Create hints with different priorities
    let mut hints = [
        LemmaHint::new(PredicateId(1), ChcExpr::Bool(true), 200, "b"),
        LemmaHint::new(PredicateId(0), ChcExpr::Bool(true), 100, "a"),
        LemmaHint::new(PredicateId(0), ChcExpr::Bool(false), 100, "c"),
    ];

    // Sort like collect_all_hints does
    hints.sort_by(|a, b| {
        a.priority
            .cmp(&b.priority)
            .then_with(|| a.predicate.0.cmp(&b.predicate.0))
            .then_with(|| a.formula.cmp(&b.formula))
    });

    // Lower priority comes first
    assert_eq!(hints[0].priority, 100);
    assert_eq!(hints[1].priority, 100);
    assert_eq!(hints[2].priority, 200);

    // Same priority: lower predicate ID comes first
    assert_eq!(hints[0].predicate, PredicateId(0));
    assert_eq!(hints[1].predicate, PredicateId(0));
}

#[test]
fn test_providers_registered() {
    // BoundsFromInitProvider should be registered
    assert!(has_providers());
}

#[test]
fn test_arithmetic_providers_applicable_for_non_bool_predicates() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", vec![ChcSort::Bool, ChcSort::Int]);

    assert!(arithmetic_providers_applicable(&problem));
}

#[test]
fn test_arithmetic_providers_skipped_for_pure_bool_predicates() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("state", vec![ChcSort::Bool, ChcSort::Bool, ChcSort::Bool]);

    assert!(!arithmetic_providers_applicable(&problem));
}

#[test]
fn test_pure_bool_problems_still_collect_init_bounds() {
    use crate::{ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let state = problem.declare_predicate("state", vec![ChcSort::Bool]);

    let flag = ChcVar::new("flag", ChcSort::Bool);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(flag.clone()), ChcExpr::Bool(true))),
        ClauseHead::Predicate(state, vec![ChcExpr::var(flag)]),
    ));

    let canonical_flag = ChcVar::new("a0", ChcSort::Bool);
    let canonical_vars = vec![canonical_flag.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;
    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == state {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let hints = collect_all_hints_with_extra(&req, &[]);

    assert!(
        hints.iter().any(|hint| {
            hint.predicate == state
                && hint.source == "bounds-from-init-v1"
                && hint.formula
                    == ChcExpr::ge(ChcExpr::var(canonical_flag.clone()), ChcExpr::Bool(true))
        }),
        "pure-Boolean problems should still keep bounds-from-init hints: {hints:?}"
    );
}

#[test]
fn test_bounds_from_init_provider() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Create a problem with:
    // predicate inv(x: Int, y: Int)
    // clause: x >= 0 /\ y >= 0 /\ y <= 100 => inv(x, y)
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Create variables
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Create constraint: x >= 0 /\ y >= 0 /\ y <= 100
    let constraint = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        ),
        ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(100)),
    );

    // Add init clause: constraint => inv(x, y)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x), ChcExpr::var(y)]),
    ));

    // Define canonical vars for inv
    let canonical_x = ChcVar::new("a0", ChcSort::Int);
    let canonical_y = ChcVar::new("a1", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_x.clone(), canonical_y.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let provider = BoundsFromInitProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // Should extract 3 hints: a0 >= 0, a1 >= 0, a1 <= 100
    assert_eq!(
        hints.len(),
        3,
        "Expected 3 hints, got {}: {:?}",
        hints.len(),
        hints
    );

    // All hints should be for predicate inv
    assert!(hints.iter().all(|h| h.predicate == inv));

    // Check that we got the expected formulas (in canonical vars)
    let expected_formulas = vec![
        ChcExpr::ge(ChcExpr::var(canonical_x), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(canonical_y.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(canonical_y), ChcExpr::int(100)),
    ];

    for expected in &expected_formulas {
        let found = hints
            .iter()
            .any(|h| format!("{:?}", h.formula) == format!("{expected:?}"));
        assert!(found, "Missing expected hint: {expected:?}");
    }
}

#[test]
fn test_bounds_extraction_helpers() {
    use crate::ChcSort;

    let x = ChcVar::new("x", ChcSort::Int);

    // Test: x >= 5
    let expr = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(bounds[0].2); // is_lower_bound

    // Test: x <= 10
    let expr = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(!bounds[0].2); // is_upper_bound

    // Test: x > 0 -> x >= 1
    let expr = ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(matches!(bounds[0].1, ChcExpr::Int(1)));
    assert!(bounds[0].2); // is_lower_bound

    // Test: x < 5 -> x <= 4
    let expr = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(matches!(bounds[0].1, ChcExpr::Int(4)));
    assert!(!bounds[0].2); // is_upper_bound

    // Test inverted comparisons: 5 >= x (means x <= 5) -> upper bound
    let expr = ChcExpr::ge(ChcExpr::int(5), ChcExpr::var(x.clone()));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(matches!(bounds[0].1, ChcExpr::Int(5)));
    assert!(!bounds[0].2); // is_upper_bound

    // Test inverted: 5 <= x (means x >= 5) -> lower bound
    let expr = ChcExpr::le(ChcExpr::int(5), ChcExpr::var(x.clone()));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(matches!(bounds[0].1, ChcExpr::Int(5)));
    assert!(bounds[0].2); // is_lower_bound

    // Test inverted: 5 > x (means x < 5 -> x <= 4) -> upper bound
    let expr = ChcExpr::gt(ChcExpr::int(5), ChcExpr::var(x.clone()));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(matches!(bounds[0].1, ChcExpr::Int(4)));
    assert!(!bounds[0].2); // is_upper_bound

    // Test inverted: 5 < x (means x > 5 -> x >= 6) -> lower bound
    let expr = ChcExpr::lt(ChcExpr::int(5), ChcExpr::var(x));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert_eq!(bounds[0].0, "x");
    assert!(matches!(bounds[0].1, ChcExpr::Int(6)));
    assert!(bounds[0].2); // is_lower_bound
}

#[test]
fn test_bounds_from_init_stuck_stage() {
    // Verify that BoundsFromInitProvider only collects at Startup stage
    let problem = ChcProblem::new();
    let vars: Vec<ChcVar> = vec![];
    let vars_ref: &[ChcVar] = &vars;
    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(vars_ref) };

    let req = HintRequest::new(HintStage::Stuck, &problem, &canonical_vars_fn);

    let provider = BoundsFromInitProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // Should not collect any hints at Stuck stage
    assert!(hints.is_empty());
}
