// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included in `adaptive_validation::tests` to preserve test FQNs.

/// Two-predicate acyclic DAG `P -> Q`. `safe = true` makes the query
/// unreachable; `safe = false` makes it reachable (genuine cex). Both are
/// acyclic and scalar (Int), so an exhaustive acyclic BMC is a complete
/// decision procedure.
#[cfg(test)]
fn acyclic_dag_two_pred(safe: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // P(x) /\ y = x + 1 => Q(y)   (acyclic edge P -> Q)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(y.clone()),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));
    // Query: Q(y) /\ guard => false. y is always 1.
    // safe: guard `y < 0` is never reachable; unsafe: guard `y = 1` is.
    let guard = if safe {
        ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(0))
    } else {
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(1))
    };
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(y)])], Some(guard)),
        ClauseHead::False,
    ));
    problem
}

/// Fix V1: a scalar acyclic SAFE multi-predicate problem is re-proved on the
/// original clauses, so the finalize gate can accept the verdict without a
/// materialized witness.
#[test]
fn v1_reproves_acyclic_scalar_safe_problem() {
    let adaptive = AdaptivePortfolio::new(
        acyclic_dag_two_pred(true),
        crate::AdaptiveConfig::test_default(),
    );
    assert!(
        adaptive.final_safe_verdict_reproved_on_original(Some(Duration::from_secs(5))),
        "exhaustive acyclic BMC must re-prove a safe scalar acyclic DAG"
    );
}

/// Fix V1 soundness: the re-proof must NOT report Safe on an UNSAFE problem,
/// even though it is acyclic and scalar (BMC finds the counterexample).
#[test]
fn v1_does_not_reprove_acyclic_scalar_unsafe_problem() {
    let adaptive = AdaptivePortfolio::new(
        acyclic_dag_two_pred(false),
        crate::AdaptiveConfig::test_default(),
    );
    assert!(
        !adaptive.final_safe_verdict_reproved_on_original(Some(Duration::from_secs(5))),
        "re-proof must never accept an unsafe problem"
    );
}

/// Fix V1 soundness: cyclic problems are out of scope for an acyclic
/// exhaustion proof and must be rejected by the guard (no false re-proof).
#[test]
fn v1_does_not_reprove_cyclic_problem() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    // Inv(x) => Inv(x + 1)   (self-loop -> cyclic dependency graph)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    // Inv(x) /\ x < 0 => false   (safe but cyclic; re-proof must still bail)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let adaptive = AdaptivePortfolio::new(problem, crate::AdaptiveConfig::test_default());
    assert!(
        !adaptive.final_safe_verdict_reproved_on_original(Some(Duration::from_secs(5))),
        "cyclic problems must not be re-proved by acyclic exhaustion"
    );
}
