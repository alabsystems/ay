// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

#[test]
fn test_dar_readiness_accepts_single_pred_linear_arithmetic() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xp = ChcVar::new("xp", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(xp.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(xp.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(xp)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let report = DarReadinessReport::analyze(&problem);
    assert!(report.is_ready(), "expected DAR-ready report: {report:?}");
    assert_eq!(report.predicate_count, 1);
    assert_eq!(report.state_var_count, 1);
}

#[test]
fn test_dar_readiness_rejects_multi_predicate_problems() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.declare_predicate("Q", vec![ChcSort::Int]);

    let report = DarReadinessReport::analyze(&problem);
    assert_eq!(
        report.status,
        DarReadinessStatus::NotApplicable(DarReadinessBlocker::PredicateCount { actual: 2 })
    );
}

/// F1 (LRA-Lin unlock): DAR now admits Bool state sorts. Previously the
/// readiness preflight rejected Bool with UnsupportedStateSort; the mixed
/// Bool+Real predicates that dominate the track made DAR self-skip. Soundness is
/// preserved because DAR never returns Unsafe and its Safe results are replayed
/// against the original clauses by the portfolio acceptance pipeline.
#[test]
fn test_dar_readiness_admits_bool_state_sort() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Bool]);
    let b = ChcVar::new("b", ChcSort::Bool);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::bool_const(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(b.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(b.clone())])]),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(b.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(b)])]),
        ClauseHead::False,
    ));

    let report = DarReadinessReport::analyze(&problem);
    assert_eq!(report.status, DarReadinessStatus::Ready);
}

#[test]
fn test_dar_solver_returns_not_applicable_for_multi_predicate() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(q, vec![ChcExpr::var(x)])]),
        ClauseHead::False,
    ));

    let result = DarSolver::new(problem, DarConfig::default()).solve();
    assert!(
        matches!(result, DarResult::NotApplicable),
        "expected DAR to skip multi-predicate problem, got {result:?}"
    );
}

#[test]
fn test_dar_simple_unsafe() {
    // Init: x = 0
    // Step: x' = x + 1
    // Bad:  x > 1
    // Unsafe at depth 2
    let mut problem = ChcProblem::new();
    let s1 = problem.declare_predicate("s1", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xp = ChcVar::new("xp", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(xp.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    let solver = DarSolver::new(
        problem,
        DarConfig {
            base: ChcEngineConfig::default(),
            max_n: 10,
            query_timeout: Duration::from_secs(2),
            total_timeout: Duration::from_secs(10),
        },
    );
    let result = solver.solve();
    // DAR MVP defers Unsafe reporting to BMC; it returns Unknown for unsafe systems.
    assert!(
        matches!(&result, DarResult::Unknown),
        "Expected Unknown (DAR defers Unsafe to BMC), got: {result:?}"
    );
}

#[test]
fn test_dar_simple_safe() {
    // Init: x = 0
    // Step: x' = x + 1
    // Bad:  x < 0
    // Safe: invariant x >= 0
    let mut problem = ChcProblem::new();
    let s1 = problem.declare_predicate("s1", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xp = ChcVar::new("xp", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(xp.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(xp.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(s1, vec![ChcExpr::var(xp)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(s1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let solver = DarSolver::new(
        problem,
        DarConfig {
            base: ChcEngineConfig::default(),
            max_n: 10,
            query_timeout: Duration::from_secs(2),
            total_timeout: Duration::from_secs(10),
        },
    );
    let result = solver.solve();
    // DAR may return Safe or Unknown depending on interpolation capability
    match result {
        DarResult::Safe(model) => {
            assert!(!model.is_empty(), "Safe model should not be empty");
        }
        DarResult::Unknown => {
            // Expected with current interpolation limitations
        }
        other => panic!("Expected Safe or Unknown, got {other:?}"),
    }
}

/// #6047: After array sort gate lift, DAR attempts array-sorted problems
/// but returns Unknown (interpolation doesn't handle arrays).
#[test]
fn test_dar_array_sort_returns_unknown() {
    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let inv = problem.declare_predicate("Inv", vec![arr_sort.clone()]);
    let a = ChcVar::new("a", arr_sort.clone());
    let ap = ChcVar::new("ap", arr_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(a.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(a.clone())])], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(ap)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(a)])], None),
        ClauseHead::False,
    ));

    let solver = DarSolver::new(problem, DarConfig::default());
    let result = solver.solve();
    assert!(
        matches!(result, DarResult::Unknown | DarResult::Unsafe(_)),
        "Expected Unknown or Unsafe for Array state sort (gate lifted per #6047), got: {result:?}"
    );
}
