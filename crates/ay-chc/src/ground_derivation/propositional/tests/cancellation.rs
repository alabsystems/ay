// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn fanout_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![]);
    let q = problem.declare_predicate("q", vec![]);
    let r = problem.declare_predicate("r", vec![]);
    let unused = problem.declare_predicate("unused", vec![]);
    // Query first requires another forward-chaining scan. Repeated premises
    // exercise both reachability and materialization without duplicate steps.
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        r,
        vec![],
    )])));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(q, vec![]), (p, vec![])]),
        ClauseHead::Predicate(r, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![]), (p, vec![])]),
        ClauseHead::Predicate(q, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(unused, vec![]),
    ));
    problem
}

#[test]
fn every_observed_work_stop_is_typed_and_returns_no_partial_derivation() {
    let problem = fanout_problem();
    let before = format!("{problem:?}");
    let mut total = 0;
    let derivation = ground_nullary_refutation(&problem, &mut || {
        total += 1;
        true
    })
    .unwrap()
    .expect("positive control before stop injection");
    validate_ground_derivation(&problem, &derivation).unwrap();
    assert_eq!(derivation.len(), 4);
    assert_eq!(derivation.steps[derivation.query_step].clause_index, 0);
    assert!(total > 20);
    for stop in 1..=total {
        let mut calls = 0;
        let result = ground_nullary_refutation(&problem, &mut || {
            calls += 1;
            calls != stop // A later callback would recover; it must not be tried.
        });
        assert!(
            matches!(result, Err(GroundDerivationError::Interrupted)),
            "stop {stop}"
        );
        assert_eq!(calls, stop);
    }
    assert_eq!(format!("{problem:?}"), before);
    validate_ground_derivation(&problem, &refutation(&problem).unwrap()).unwrap();
}

#[test]
fn missing_candidate_and_clause_cap_remain_distinct_from_interruption() {
    let mut capped = ChcProblem::new();
    for _ in 0..=MAX_GROUND_REFUTATION_CLAUSES {
        capped.add_clause(HornClause::query(ClauseBody::empty()));
    }
    for problem in [ChcProblem::new(), capped] {
        assert!(ground_nullary_refutation(&problem, &mut || true)
            .unwrap()
            .is_none());
        assert!(matches!(
            ground_nullary_refutation(&problem, &mut || false),
            Err(GroundDerivationError::Interrupted)
        ));
        let mut calls = 0;
        let result = ground_nullary_refutation(&problem, &mut || {
            calls += 1;
            calls != 3
        });
        assert!(
            matches!(result, Err(GroundDerivationError::Interrupted)),
            "final missing-candidate poll must refuse"
        );
        assert_eq!(calls, 3);
    }
}

#[test]
fn search_control_stays_stopped_after_the_progress_source_recovers() {
    let problem = fanout_problem();
    let mut calls = 0;
    {
        let mut callback = || {
            calls += 1;
            calls != 5
        };
        let mut control = GroundValidationControl::new(&mut callback);
        assert!(matches!(
            search(&problem, &mut control),
            Err(GroundDerivationError::Interrupted)
        ));
        assert!(control.is_stopped());
        assert!(matches!(
            search(&problem, &mut control),
            Err(GroundDerivationError::Interrupted)
        ));
    }
    assert_eq!(calls, 5);
}
