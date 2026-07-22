// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ClauseBody, ClauseHead};

#[test]
fn test_extract_constants_and_comparisons() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(-1)),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    let qs = QualifierSet::from_problem(&problem);
    assert!(qs.constants.contains(&5));
    assert!(qs.constants.contains(&-1));

    let instantiated = qs.instantiate(&[x, y]);
    assert!(instantiated.iter().any(|e| *e
        == ChcExpr::le(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(5)
        )));
}

#[test]
fn test_cap_constants_respects_max_with_must_keep() {
    let mut constants: FxHashSet<i128> = FxHashSet::default();
    for c in [0i128, 1, -1, 2, -2, 5, 100, -100] {
        constants.insert(c);
    }

    let capped = QualifierSet::cap_constants(constants, 3);
    assert_eq!(capped.len(), 3);
    assert!(capped.contains(&0));
    assert!(capped.contains(&1));
    assert!(capped.contains(&-1));
    assert!(!capped.contains(&2));
    assert!(!capped.contains(&-2));
}

#[test]
fn test_cap_constants_handles_i64_min_without_panic() {
    // i128-lockstep: the extreme-magnitude guard now sits at i128::MIN.
    let mut constants: FxHashSet<i128> = FxHashSet::default();
    for c in [i128::MIN, i128::from(i64::MIN), 0, 5, -5] {
        constants.insert(c);
    }

    let capped = QualifierSet::cap_constants(constants, 2);
    assert!(capped.contains(&0));
    assert!(capped.contains(&5) || capped.contains(&-5));
    assert!(!capped.contains(&i128::MIN));
}
