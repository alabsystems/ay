// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashSet as HashSet;

#[test]
fn test_is_linear_single_pred() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let transform = SingleLoopTransformation::new(problem);
    assert!(transform.is_linear());
}

#[test]
fn test_transform_simple() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut transform = SingleLoopTransformation::new(problem);
    let result = transform.transform();

    assert!(result.is_some());
    let ts = result.unwrap();

    // Should have 1 location var + 1 arg var
    assert_eq!(ts._location_vars.len(), 1);
    assert_eq!(ts._arg_vars.len(), 1);
}

#[test]
fn test_transform_multi_predicate() {
    // Create a simple multi-predicate system:
    // P(x) => Q(x)
    // Q(x) /\ x < 5 => Q(x+1)
    // Q(x) /\ x >= 10 => false
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));

    // Q(x) /\ x < 5 => Q(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Q(x) /\ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut transform = SingleLoopTransformation::new(problem);
    let result = transform.transform();

    assert!(result.is_some());
    let ts = result.unwrap();

    // Should have 2 location vars + 2 arg vars (one per predicate)
    assert_eq!(ts._location_vars.len(), 2);
    assert_eq!(ts._arg_vars.len(), 2);
}

/// Regression test for #2690:
/// transformed transition/query formulas must not retain clause-local vars.
#[test]
fn test_transform_eliminates_clause_local_variables_issue_2690() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    // Transition with complex body argument:
    // Inv(y - 1) /\ y < 5 => Inv(y)
    // `y` must be substituted away; no free clause-local vars may remain.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![ChcExpr::sub(ChcExpr::var(y.clone()), ChcExpr::int(1))],
            )],
            Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(y)]),
    ));

    // Query: Inv(z) /\ z >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(z.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(z), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut transform = SingleLoopTransformation::new(problem);
    let ts = transform.transform().expect("transform should succeed");

    let mut allowed: HashSet<String> = HashSet::default();
    for v in ts._location_vars.values() {
        allowed.insert(v.name.clone());
        allowed.insert(format!("{}_next", v.name));
    }
    for v in ts._arg_vars.values() {
        allowed.insert(v.name.clone());
        allowed.insert(format!("{}_next", v.name));
    }

    if let Some(leaked) = ts
        .transition
        .vars()
        .into_iter()
        .chain(ts.query.vars())
        .find(|v| !allowed.contains(&v.name))
    {
        panic!(
            "found leaked clause-local variable '{}' in transformed system",
            leaked.name
        );
    }
}

#[test]
fn test_back_translate_invariant() {
    // Create a system with two predicates P, Q
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));

    // Q(x) /\ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut transform = SingleLoopTransformation::new(problem);
    let ts = transform.transform().expect("transform should succeed");

    let loc_p = ts
        ._location_vars
        .get(&p)
        .expect("should have loc var for P");
    let loc_q = ts
        ._location_vars
        .get(&q)
        .expect("should have loc var for Q");
    let arg_p = ts
        ._arg_vars
        .get(&(p, 0))
        .expect("should have arg var for P");
    let arg_q = ts
        ._arg_vars
        .get(&(q, 0))
        .expect("should have arg var for Q");

    // Invariant in the transformed space:
    // (loc_P = 1 => arg_P < 10) /\ (loc_Q = 1 => arg_Q < 10)
    //
    // This is compatible with init: all locations are 0 and arguments are unconstrained.
    // With Int location vars, solver invariants use eq(loc, 1) comparisons.
    let invariant = ChcExpr::and(
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::var(loc_p.clone()), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(arg_p.clone()), ChcExpr::int(10)),
        ),
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::var(loc_q.clone()), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(arg_q.clone()), ChcExpr::int(10)),
        ),
    );

    // Back-translate to predicate interpretations
    let interpretations = transform.back_translate_invariant(&invariant);
    assert_eq!(interpretations.len(), 2);

    let interp_p = interpretations
        .get(&p)
        .expect("should have interpretation for P");
    let interp_q = interpretations
        .get(&q)
        .expect("should have interpretation for Q");

    let v0 = ChcVar::new("v0", ChcSort::Int);

    // Location vars should be substituted away.
    assert!(
        !interp_p.vars().iter().any(|v| v.name.starts_with(".loc_")),
        "P interpretation still contains a location var: {interp_p:?}"
    );
    assert!(
        !interp_q.vars().iter().any(|v| v.name.starts_with(".loc_")),
        "Q interpretation still contains a location var: {interp_q:?}"
    );

    // Each predicate's argument variable should be renamed to its canonical variable name.
    assert!(interp_p.vars().contains(&v0));
    assert!(!interp_p.vars().contains(arg_p));

    assert!(interp_q.vars().contains(&v0));
    assert!(!interp_q.vars().contains(arg_q));

    // Structural expectation: location substitution + per-predicate arg rename.
    // Int location vars: active predicate's loc substituted with Int(1),
    // inactive with Int(0). The eq(loc, int(1)) becomes eq(Int(1), Int(1))
    // or eq(Int(0), Int(1)) after substitution.
    let expected_p = ChcExpr::and(
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::int(1), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(v0.clone()), ChcExpr::int(10)),
        ),
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::int(0), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(arg_q.clone()), ChcExpr::int(10)),
        ),
    );

    let expected_q = ChcExpr::and(
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::int(0), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(arg_p.clone()), ChcExpr::int(10)),
        ),
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::int(1), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(v0), ChcExpr::int(10)),
        ),
    );

    assert_eq!(interp_p, &expected_p);
    assert_eq!(interp_q, &expected_q);
}

#[test]
fn test_back_translate_invariant_simplify_constants_drops_inactive_alien_branch() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut transform = SingleLoopTransformation::new(problem);
    let ts = transform.transform().expect("transform should succeed");
    let loc_p = ts
        ._location_vars
        .get(&p)
        .expect("should have loc var for P");
    let loc_q = ts
        ._location_vars
        .get(&q)
        .expect("should have loc var for Q");
    let arg_p = ts
        ._arg_vars
        .get(&(p, 0))
        .expect("should have arg var for P");
    let arg_q = ts
        ._arg_vars
        .get(&(q, 0))
        .expect("should have arg var for Q");

    let invariant = ChcExpr::and(
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::var(loc_p.clone()), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(arg_p.clone()), ChcExpr::int(10)),
        ),
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::var(loc_q.clone()), ChcExpr::int(1)),
            ChcExpr::lt(ChcExpr::var(arg_q.clone()), ChcExpr::int(10)),
        ),
    );

    let interpretations = transform.back_translate_invariant(&invariant);
    let simplified_p = interpretations
        .get(&p)
        .expect("should have interpretation for P")
        .simplify_constants();
    let simplified_q = interpretations
        .get(&q)
        .expect("should have interpretation for Q")
        .simplify_constants();

    let v0 = ChcVar::new("v0", ChcSort::Int);
    assert_eq!(
        simplified_p,
        ChcExpr::lt(ChcExpr::var(v0.clone()), ChcExpr::int(10))
    );
    assert_eq!(
        simplified_q,
        ChcExpr::lt(ChcExpr::var(v0.clone()), ChcExpr::int(10))
    );
    assert_eq!(simplified_p.vars(), vec![v0.clone()]);
    assert_eq!(simplified_q.vars(), vec![v0]);
}
